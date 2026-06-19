# Teammate D Findings (Round 2): Strategic Horizon Analysis

**Task**: 197 — Scope initial Modal/ upstream PR (~300 LOC)
**Role**: Teammate D (Horizons) — Long-term alignment and strategic direction
**Date**: 2026-06-17
**Scope**: Updated strategic analysis given PR #648/#649 review feedback, algebraic completeness
  work (task 227), FFL coordination opportunity, and optimal PR sequencing

---

## Key Findings

### 1. The Situation Has Changed: Both PRs Now Have CHANGES_REQUESTED

The previous round of Teammate D findings (2026-06-14, `03_teammate-d-findings.md`) was written
when PR #648 and PR #649 had zero reviews. As of 2026-06-17, both have received
`CHANGES_REQUESTED`:

**PR #648 (Propositional, our PR)**:
- ctchou: "I like primitive bot." But objects to old-style references (1930s papers in German).
  Wants a modern reference (Avigad textbook). Does not understand why `Semantics/Basic.lean`
  and `Semantics/Bool.lean` both exist.
- thomaskwaring: "Having falsum as a primitive is more conventional, but the current design was
  discussed fairly thoroughly." Raises the question of whether `⊥` in minimal logic just behaves
  like an atomic formula — why not use `[Bot Atom]`?
- benbrastmckie (our response): Addressed both points. Removed `Semantics/` files from this PR.
  Rebased on upstream/main after PR #536 merged.

**PR #649 (Temporal, our PR)**:
- ctchou: Objects to past-time operators. Wants future-only temporal logic tied to LTS
  omega-executions. Does not understand `Encodable`/`Countable` instances.
- benbrastmckie (our response): Added `FutureTemporalConnectives` base class; split
  `LTLConnectives` (future + next) vs `TemporalConnectives` (future + past). Removed
  `LTL.Satisfies`. Linked temporal semantics to `LTS.OmegaExecution`.

**Strategic implication**: Both PRs are in active review-iteration cycles. The Modal PR
cannot be submitted until at least PR #648 stabilizes — the `Connectives.lean` dependency is
real and the reviewers' concerns may reshape the typeclass hierarchy the Modal PR assumes.
The original estimate of "2 weeks" for #648 feedback has passed; the feedback revealed
substantive design concerns, not just style issues.

### 2. Algebraic Semantics Direction Reshapes the Modal Architecture

Task 227 (algebraic completeness design, currently `[IMPLEMENTING]`) reveals a strategic
development that has direct implications for the Modal PR:

The propositional algebraic semantics work introduces a three-tier hierarchy:
- **JohanssonAlgebra** (MPL) — GHA + distinguished bot element
- **HeytingAlgebra** (IPL) — HA with `bot_val = ⊥`
- **BooleanAlgebra** (CPL) — BA with `bot_val = ⊥`

thomaskwaring's own Zulip comment (2026-05-27) showed he is pursuing **algebraic semantics
for Kripke completeness**: "I derived completeness for Kripke models of intuitionistic logic
from the completeness of its algebraic semantics... the Kripke model has worlds = prime filters
in the Heyting algebra."

This matters for the Modal PR because:

1. **Modal algebras** (Boolean algebras + box operator = `□φ := □φ` preserving ⊤ and
   distribution over ∧) are the algebraic counterpart of modal Kripke semantics. If CSLib
   moves toward algebraic completeness proofs (as task 227 targets for propositional logic),
   the Modal PR's choice of primitives will determine how well modal algebras can be defined.

2. **Box-as-primitive is algebraically natural**: The box operator on a Boolean algebra is a
   necessity operator satisfying `□⊤ = ⊤` and `□(φ ∧ ψ) = □φ ∧ □ψ`. With diamond-as-
   primitive, you get `◇⊥ = ⊥` and distribution over ∨ — these are dual but the box form
   interacts more naturally with `GeneralizedHeytingAlgebra.himp` and the existing Mathlib
   interface where `⊤`-preservation is fundamental.

3. **The Modal PR's `{atom, bot, imp, box}` design is algebraically stable**: It matches the
   pattern that task 227 has developed for propositional logic. The `AlgEvaluate` function for
   modal formulas would be a natural extension of the propositional evaluator with an added
   `□` case requiring a closure operator on the algebra.

**Confidence**: High (task 227 is actively implementing algebraic completeness proofs that
directly confirm the algebraic coherence of the bot-as-primitive design).

### 3. PR #648's Semantics Removal Creates a Strategic Opening for the Modal PR

ctchou's feedback on PR #648 forced removal of `Semantics/Basic.lean` and `Semantics/Bool.lean`
from the propositional PR. This means the propositional PR is now purely syntactic (formula
type + typeclass instances + natural deduction). The semantics question is explicitly deferred.

**This creates an opening for the Modal PR**: The Modal PR can introduce Kripke semantics for
modal formulas as a **new contribution** that propositional logic does not yet have upstream.
The Modal PR can legitimately say: "We add the first semantics layer (Kripke) for any formula
type in CSLib." This is a stronger narrative than a pure refactoring.

However, this also adds scope risk: if the Modal PR includes both the formula refactoring
AND Kripke semantics (`Basic.lean` = formula type; `Denotation.lean` = set-theoretic semantics),
the PR is already ~355 LOC without `LogicalEquivalence.lean`. Adding `LogicalEquivalence.lean`
pushes to ~420 LOC.

**Recommendation**: Keep the initial Modal PR focused on the three-file refactoring
(Basic + Denotation + LogicalEquivalence, ~355 LOC) as previously established. The Kripke
semantics is already in `Denotation.lean` — the opening narrative is available without adding
new files.

### 4. Task 197 Should Not Be Reconceived — Its Scope Is Correct

The question was raised whether task 197 should be broadened into "coordinate Modal/ upstream
strategy." It should not. Here is why:

1. **The pr-description.md is already written** and covers the strategic framing. The task's
   implementation artifact exists and is high quality. Task 197's scope is complete.

2. **The remaining work is execution, not strategy**: Branch creation, CI verification, and PR
   submission via `/pr`. These are implementation tasks, not research tasks.

3. **Strategy is best served by keeping task 197 narrow**: A broader "coordinate Modal strategy"
   task would have an unclear completion condition. The modal PR submission is a clear, concrete
   deliverable.

4. **The coordination work is best done via a Zulip message**, which is a ~200-word action, not
   a separate task. The pr-description.md already provides the content for that message.

**What task 197 should still accomplish**: Ensure the PR is submitted once PR #648 stabilizes
enough that its `Connectives.lean` structure is confirmed. Given that PR #648 now has
CHANGES_REQUESTED and benbrastmckie has responded, the next state is either:
- Another round of review → more changes
- Approval → Modal PR can be stacked and submitted

The Modal PR submission should happen **after PR #648 reaches approval**, not before.

### 5. FFL Coordination: Timing Is Ripe but Scope Is Bounded

SnO2WMaN (FFL author) expressed interest in collaboration in the Zulip thread. The FFL project
has GL completeness, Kripke semantics redesign (SeqPL project), and interest in the modal cube.
The question is: does this create an obligation or opportunity for the user's Modal PR?

**Assessment**: FFL coordination should be acknowledged but not acted upon before the Modal PR:

1. **FFL's GL completeness** is independent of the user's K/T/B/4/5/S4/S5 completeness.
   GL is provability logic (no 5 axiom, adds Löb's axiom), requiring a separate treatment.
   The user's Modal PR does not include GL.

2. **SnO2WMaN's Kripke semantics redesign** (SeqPL) addresses universe issues in first-order
   Kripke models. The user's modal formulas are propositional — no universe issues arise.
   FFL's redesign is orthogonal to the propositional modal PR.

3. **The right coordination point is after the Modal PR is merged**, not before. At that point,
   the user can invite SnO2WMaN to extend the established framework for GL as a follow-up PR.

4. **One concrete opportunity**: mention SnO2WMaN and FFL in the PR description's contribution
   roadmap section — "Future work includes GL completeness (see FFL's existing formalization)"
   — which signals openness to collaboration without committing to specific joint work.

**Confidence**: Medium — this judgment depends on how receptive SnO2WMaN is to contributing to
a CSLib framework they did not design. A Zulip direct message to SnO2WMaN after the Modal PR
is submitted is the appropriate action.

### 6. Optimal PR Sequencing: Two-PR Stack Remains Correct

The sequencing question was: should Modal wait for #648, help with fmontesi's #607, or
collaborate with Kyle Miller on S5?

**Answer**: The two-PR stack (#648 → Modal) remains correct. Here is the updated case:

| Option | Assessment |
|--------|------------|
| Wait for #648 then submit Modal | **Correct**. PR #648 is actively being iterated; the Modal PR's Connectives.lean extension cannot be finalized until #648's typeclass design is settled. |
| Help with fmontesi's #607 | **Wrong order**. PR #607 proposes to add typeclasses to the *existing* `{not, and, diamond}` primitive set — the opposite direction from the user's design. Contributing to #607 would entrench the wrong primitives. |
| Collaborate with Kyle Miller on S5 | **Premature**. Kyle Miller's S5 completeness uses a Hilbert-style axiomatization over the existing `{not, and, diamond}` type. If the Modal PR's refactoring is accepted, Kyle Miller's work would need to be rebased. Collaborating now would create rework. The correct order is: (1) get primitive set accepted, (2) then Kyle Miller contributes completeness. |
| Submit Modal before #648 | **Not viable**. `Connectives.lean` doesn't exist upstream. The Modal PR cannot compile without it. |

**The governance angle**: fmontesi controls the merge decision. He is both the original `Modal/`
author and the author of PR #607. The user's two PRs (#648, #649) have received CHANGES_REQUESTED
from ctchou — not from fmontesi. fmontesi has not commented on #648 or #649 yet. This suggests
fmontesi is waiting to see how the design discussions resolve before engaging. A targeted Zulip
message to fmontesi (referencing the Zulip thread where he asked about coordination) is the
highest-leverage action before the Modal PR is submitted.

### 7. The Collaborator vs. Competitor Frame: The User Is Currently Neither

The user has posted to the Zulip thread (2026-06-11) describing their work on Hilbert proof
systems with soundness and completeness, linking to their fork. Alexandre Rademaker invited
this. The community has not positioned the user as a competitor — SnO2WMaN said "I'm happy
someone else is working on this" and Kyle Miller said "I'm happy to get working on CSLib."

**The risk is drift toward isolation**: multiple contributors (Kyle Miller, SnO2WMaN, fmontesi,
thomaskwaring) have adjacent or overlapping work. If the user's PRs take months to merge due
to review iterations, these contributors may independently establish patterns that conflict.

**Actions that prevent drift**:
1. Keep responding promptly to PR review feedback (user has already done this for #648 and #649).
2. Post a brief Zulip update when the Modal PR is submitted, explicitly inviting Kyle Miller
   and SnO2WMaN to review or plan follow-up contributions.
3. Mention in the Modal PR description that a subsequent PR will add the Hilbert proof system
   and invite coordination on the proof-system API (InferenceSystem, as fmontesi suggested).

---

## Recommended Approach

### Primary Recommendation: Wait for PR #648 Approval, Then Submit Modal PR

**Rationale**:
1. PR #648 is in active iteration (CHANGES_REQUESTED → user response → pending second review).
   Submitting the Modal PR before #648 is approved risks having to rebase the Modal PR twice
   (once when #648 changes, once when it merges and GitHub bases are updated).

2. The Modal PR's `Connectives.lean` extension (`HasBox` + `ModalConnectives`) must be
   consistent with whatever #648's `Connectives.lean` looks like after reviews. If reviewers
   ask to rename `HasImp` to `HasImpl`, the Modal PR's `ModalConnectives` (which extends
   `PropositionalConnectives` which uses `HasImp`) would also need updating.

3. The pr-description.md artifact is already written and high quality. The wait time is
   implementation preparation time: create the PR branch, run CI, and verify the ~355 LOC
   diff compiles.

### Secondary Recommendation: Actively Help PR #648 Close

The fastest path to submitting the Modal PR is getting PR #648 approved. The user has already
responded to ctchou's and thomaskwaring's concerns. The remaining open question from
thomaskwaring is whether `⊥` should be primitive vs. `[Bot Atom]`. Task 227 (algebraic
completeness) provides a strong argument for primitive `⊥`: the free algebra argument
(substitution invariance), the Johansson/Heyting/Boolean algebra three-tier hierarchy, and
the algebraic completeness proof all require `⊥` as a primitive nullary operation, not an
instance of `Bot Atom`.

**Action**: If PR #648's review thread is still open when the user next engages, reference
task 227's argument: "The algebraic semantics work (task 227) confirms that primitive `⊥` is
necessary for the free algebra property — `subst` maps `bot` to `bot` because it preserves
nullary operations. If `⊥` were `[Bot Atom]`, substitution would not be a well-defined
algebraic homomorphism."

### Tertiary Recommendation: Task 197 Scope Remains Correct — Do Not Broaden

Task 197 is a `pr` task type with a `pr-description.md` artifact. It is waiting for PR #648
to stabilize before `/pr` is executed. The task should be kept as-is. A broader "coordinate
Modal strategy" task would not be actionable and would duplicate work already in the
pr-description.md.

---

## Evidence and Examples

### Evidence 1: Both Dependency PRs Now Have Active Review Feedback

As of 2026-06-17:
- PR #648: `CHANGES_REQUESTED` from ctchou and thomaskwaring. User responded. Status: pending
  second review.
- PR #649: `CHANGES_REQUESTED` from ctchou. User responded. Status: pending second review.

This is a 2-4 week cycle before approval is plausible, assuming reviewers respond quickly.

### Evidence 2: Task 227 Confirms Algebraic Coherence of Bot-as-Primitive

From `specs/227_algebraic_completeness_design/reports/03_primitive-bot-defense.md`:

> "The line `| .bot => .bot` is the crux. It says: ⊥ is a nullary operation in the signature,
> fixed by every substitution. This is not a convention — it follows from the definition of
> homomorphism: a homomorphism of algebras preserves all operations."

The algebraic completeness proofs in task 227 would become significantly more complex if `⊥`
were `[Bot Atom]` rather than a primitive constructor — the substitution monad structure would
break. This is the strongest technical argument for primitive `⊥`, and it is directly
applicable to the PR #648 review discussion.

### Evidence 3: ctchou's Reference Feedback Provides Actionable Guidance

ctchou explicitly asked for a modern reference (Avigad's textbook) in place of 1930s papers.
The pr-description.md for task 197 currently cites `[Johansson1937]`, `[Wajsberg1938]`,
`[McKinsey1939]`. These will receive the same pushback from ctchou. The Modal PR description
should:
1. Lead with `[Blackburn2001]` and `[ChagrovZakharyaschev1997]` (modern references).
2. Use `[Burgess1984]` only as secondary support.
3. Drop the 1930s paper citations from the PR description body (move them to references.bib
   only if needed for the theorem attribution).

### Evidence 4: fmontesi's InferenceSystem Invitation

fmontesi wrote on 2026-05-28 in the Zulip thread:
> "Regarding the axiomatised systems: it looks like a good use case for the approach I followed
> in CLL and MLL? That is, define a mega-inductive with all the axioms in the Modal Cube and
> instantiate InferenceSystem for each fragment."

This is a direct invitation for the user's Hilbert proof system work to use the InferenceSystem
API. The Modal PR's PR description should explicitly mention this: "The proof system (planned
for a subsequent PR) will use the InferenceSystem API as suggested in the Zulip discussion."
This signals that the user read and values fmontesi's architectural guidance.

### Evidence 5: Kyle Miller's S5 Completeness Is Not a Threat — It Is a Planned Collaboration

Kyle Miller's S5 completeness (Gist linked in Zulip) uses a self-contained inductive
`ax_s5` over an `{atom, not, box}` type that differs from both the current upstream type and
the user's proposed type. Kyle Miller said: "I'm happy to get working on CSLib once this PR is
merged" — meaning he is explicitly waiting for the Modal PR's primitive-set decision before
adapting his work. This is the correct sequencing and confirms that Kyle Miller sees the user
as a predecessor, not a competitor.

---

## Confidence Level

| Finding | Confidence | Basis |
|---------|------------|-------|
| PR #648 and #649 both have CHANGES_REQUESTED | High | GitHub API verified |
| Algebraic coherence of bot-as-primitive (task 227 evidence) | High | Task 227 report directly addresses the question |
| Modal PR should not be submitted before PR #648 approval | High | Hard dependency on Connectives.lean structure |
| Task 197 scope is correct — do not broaden | High | pr-description.md is complete; broadening would be unmeasurable |
| FFL coordination should come after Modal PR merges | Medium | Depends on SnO2WMaN's interest in contributing to CSLib |
| Kyle Miller is waiting on Modal PR's primitive decision | High | Verbatim from Zulip: "happy to work once this PR merges" |
| Fmontesi has not yet reviewed #648/#649 | High | GitHub API shows zero reviews from fmontesi on both PRs |
| Zulip message to fmontesi is highest-leverage pre-PR action | Medium | Based on governance analysis; uncertain how fmontesi will respond |
| ctchou will push back on 1930s paper citations in Modal PR | High | Verbatim from PR #648 review: "not helpful to refer to old papers" |
| Algebraic semantics work creates opening for modal algebras | Medium | Extrapolated from task 227 design; not yet confirmed by reviewers |
