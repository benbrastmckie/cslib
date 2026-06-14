# Teammate C Findings: Risks, Reviewer Expectations, and Conflict Analysis

**Role**: Critic — identify risks, reviewer objections, and potential blockers
**Task**: 188 — Design a first upstream PR (~300 LOC) contributing propositional logic foundations
**Date**: 2026-06-14
**Confidence**: HIGH across all sections (based on direct GitHub PR inspection and code diffing)

---

## Executive Summary

The current propositional logic codebase is in strong shape (zero sorries, 100% CI passing, fully
documented), but contributing it upstream requires navigating significant structural mismatches with
what exists on upstream `main`. The most critical findings:

1. **The ctchou objection is fully resolved.** The current code uses `{atom, bot, imp, and, or}` as
   five primitive constructors, not the two-primitive `{atom, bot, imp}` approach that ctchou
   challenged. Reviewers cannot repeat the original objection.

2. **Upstream `main` has a different `Defs.lean` signature.** The upstream Proposition type uses
   `{atom, and, or, impl}` with `Bot` via `Atom`-level instance injection — structurally different
   from our `{atom, bot, imp, and, or}` with explicit `bot` constructor. Any PR touching `Defs.lean`
   will be a **refactoring PR**, not purely additive.

3. **Two open PRs conflict directly.** PR #536 (thomaskwaring) modifies `Defs.lean` and
   `NaturalDeduction/Basic.lean` — the same files we must touch. PR #607 (fmontesi) introduces
   `HasAnd`/`HasOr` typeclasses under `Foundations/Logic/Operators/` — overlapping our
   `Connectives.lean` approach.

4. **None of the Propositional/ subdirectories (ProofSystem, Metalogic, Semantics) exist upstream.**
   Everything except `Defs.lean` and `NaturalDeduction/Basic.lean` is entirely new. This is an
   advantage for additive PRs but creates a dependency ordering question: can we contribute
   ProofSystem/Metalogic/Semantics without first merging the Defs.lean refactor?

5. **PR size constraint is firm.** PR #633 was explicitly rejected by chenson2018 as "very large."
   The request was for under 500 lines, with preference for under ~300 lines for AI-assisted PRs.

---

## Section 1: Risks

### Risk 1 (CRITICAL): Upstream Defs.lean Structural Mismatch

The upstream `main` has a different `Proposition` type:

**Upstream `main`** (`Cslib/Logics/Propositional/Defs.lean`):
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
  | impl (a b : Proposition Atom)
-- Bot comes from Bot Atom instance (atoms carry bottom)
instance instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
```

**Our version**:
```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
-- Bot is a native constructor; Bot instance wraps it
```

**Differences**:
- Upstream uses `impl`, we use `imp` (name difference)
- Upstream has no `bot` constructor; uses `atom ⊥` via `[Bot Atom]` instance
- Upstream `IsIntuitionistic` and `IsClassical` are Atom-agnostic (`[Bot Atom]`)
- Our version: `bot` is a standalone constructor, enabling `Bot (Proposition Atom)` via `⟨.bot⟩`

**Risk assessment**: Any PR that contributes a Hilbert proof system or Kripke semantics will depend
on formula induction. If the formula type on upstream main differs, our proofs will not compile
against upstream main without porting.

**Mitigation**: The first PR could be additive only (new files, no changes to upstream's
`Defs.lean`), building ProofSystem on top of upstream's formula type. This requires verifying that
the Hilbert axioms work over the `{atom, and, or, impl}` structure.

### Risk 2 (HIGH): PR #536 Direct Conflict with Defs.lean

PR #536 (thomaskwaring, OPEN) modifies `Cslib/Logics/Propositional/Defs.lean` and
`NaturalDeduction/Basic.lean`. It changes `IsClassical` and `IsIntuitionistic` to reference an
inference system rather than a theory, and adds `NaturalDeduction/Theory.lean`.

**Conflict assessment**: If PR #536 merges before our PR, the `Defs.lean` interface changes. If our
PR tries to modify `Defs.lean` as well, GitHub will flag merge conflicts. Since thomaskwaring is a
CSLib reviewer and collaborator, his PR has high priority.

**Strategy**: Either (a) build our first PR as purely additive (no `Defs.lean` changes), stacked on
top of existing upstream interfaces, or (b) coordinate with thomaskwaring via Zulip to establish
sequencing.

### Risk 3 (HIGH): PR #607 Typeclass Architecture Overlap

PR #607 (fmontesi, OPEN) introduces a `Foundations/Logic/Operators/` directory with one file per
connective (`And.lean`, `Or.lean`, `Impl.lean`, `Not.lean`, etc.), each defining a `HasX` typeclass
with scoped notation. This is the Montesi/lead-maintainer approach.

Our `Connectives.lean` bundles multiple classes into one file and adds bundled classes
(`PropositionalConnectives`, `ModalConnectives`, etc.) not present in PR #607. The approach is
aligned in spirit (per-operator `HasX` classes) but different in organization:
- PR #607: `Foundations/Logic/Operators/And.lean` etc. (one file per operator)
- Our approach: `Foundations/Logic/Connectives.lean` (all operators in one file)

Our `Connectives.lean` also explicitly acknowledges PR #607 in its docstring ("following the
operator-typeclass direction of fmontesi's PR #607").

**Risk**: If PR #607 merges first, our bundled approach may be rejected in favor of the per-file
approach. Reviewers may ask us to either adapt to PR #607's directory structure or wait for it.

**What eric-wieser said** (PR #635 inline review): "Here you could co-opt mathlib's `Bot` and
`HImp` classes." This suggests a third approach — using Mathlib's existing typeclasses rather than
CSLib-specific ones. If eric-wieser is assigned to review our Connectives.lean, he may repeat this
suggestion.

### Risk 4 (MEDIUM): `@[expose] public section` Pattern

The `@[expose] public section` pattern is used extensively across CSLib (confirmed in Bimodal,
Modal, Temporal, LinearLogic modules). It is **not a new introduction** — it is an established CSLib
convention. Risk of reviewer objection is LOW.

However, the attribute `@[expose]` is a CSLib-specific extension (not from Lean or Mathlib core).
Reviewers familiar only with Lean/Mathlib but not CSLib internals might question it. Including a
brief comment in the PR description that this follows CSLib convention (e.g., citing Modal/Basic.lean
as precedent) would preempt the question.

### Risk 5 (MEDIUM): `module` Keyword at File Top

The bare `module` keyword at the top of every file is CSLib-standard. It appears in all 26
Propositional files, all 16 Foundations/Logic files, and across Modal, Temporal, Bimodal, Lambda,
CCS, and Languages modules. Risk of reviewer objection is LOW.

The upstream main `Defs.lean` and `NaturalDeduction/Basic.lean` both use `module` already, so this
cannot be an objection.

### Risk 6 (MEDIUM): PR Size vs. Scope for First Contribution

PR #633 (the original large propositional PR, ~6,000+ lines) was rejected as "very large."
chenson2018 specifically requested "under 500 lines" and "even this is quite large for a first
contribution." For a first PR from an AI-assisted author, the bar is lower.

Our 41-file codebase cannot be contributed in one PR. The first PR must be carefully scoped to
~300 lines. Risk: even a well-scoped PR may face requests to split further.

**Quantified scope estimate**: The files most suited to a first standalone PR are:
- `Foundations/Logic/Connectives.lean` (~100 lines of substantive content)
- `Logics/Propositional/Defs.lean` (refactor of upstream's ~130-line file)
- Subtotal: ~230 lines net new/changed

This is within range but depends heavily on whether the `Defs.lean` refactor is bundled in or kept
separate.

### Risk 7 (LOW): Universe Polymorphism Choices

Our code uses `Type u` with `variable {Atom : Type u} [DecidableEq Atom]`, matching the upstream
`Defs.lean` exactly. No universe polymorphism mismatch risk.

### Risk 8 (LOW): Naming: `imp` vs `impl`

Our code uses `imp` for the implication constructor; upstream uses `impl`. This is a surface-level
naming inconsistency. Any additive PR that introduces `imp` notation into a codebase with `impl`
will require justification, and would likely trigger a reviewer request to use `impl` for
consistency with the existing upstream file — or conversely to rename upstream's `impl` to `imp`.

This is resolvable but must be addressed in the PR description.

---

## Section 2: Reviewer Expectations

Based on direct inspection of PR #633, PR #635, PR #607 review comments, and CONTRIBUTING.md:

### Expectation 1: Small, Focused PRs (~300-500 Lines Maximum)

From PR #633 (chenson2018): "At the moment this PR is very large. Especially for new contributors
and/or when AI is involved, we ask for smaller PRs in the neighborhood of fewer than 500 lines."

**Action required**: The first PR must be scoped to a single coherent capability, ideally a
standalone module that adds value without depending on unmerged PRs.

### Expectation 2: AI Disclosure is Required

CONTRIBUTING.md cites the Mathlib policy explicitly: "If you use artificial intelligence [...] please
explain this in the PR description. Explain which tool(s) you used and how you used it."

PR #635 included a complete AI disclosure section. The template to follow is:
```
## AI Disclosure
This PR was prepared with the assistance of Claude Code (Anthropic), used for [specific uses].
All Lean code was written by the author (Benjamin Brast-McKie) and verified to compile on the PR branch.
```

This is **mandatory**. Omitting it would likely trigger a reviewer request to add it.

### Expectation 3: Literature References Must Be Accurate and Correctly Cited

From PR #633 (ctchou): "It would also be helpful to point out where exactly in your code is each
reference used." From the task 171 research: ctchou checked the actual Gentzen paper and found it
did not support the claimed basis.

**Action required**:
- Every docstring that mentions a literature source must use BibKey format `[Author, *Title*][BibKey]`
- The `references.bib` entry must exist for every BibKey used
- The claim made must accurately reflect what the source says

Task 185 already fixed all "CZ" citations to BibKey format. This risk is now LOW provided the task
185 fixes are included in the PR.

### Expectation 4: Reuse Existing Typeclasses Before Introducing New Ones

From PR #607 and PR #635 review comments (eric-wieser): "Here you could co-opt mathlib's `Bot` and
`HImp` classes." From CONTRIBUTING.md (Reuse section): "New definitions should instantiate existing
abstractions whenever appropriate."

Any PR introducing `HasBot`, `HasImp`, `HasAnd`, `HasOr` must explain why these cannot simply be
`Bot`, `HImp`, `Sup`, `Inf` from Mathlib. The explanation is strong (Mathlib's `HImp` carries
lattice-algebraic semantics; our classes are for syntactic formula types) and documented in
`Connectives.lean`'s design rationale section. This must be preserved in the PR.

### Expectation 5: Coordination for Major/Architectural Contributions

From CONTRIBUTING.md: "For any major development, it is strongly recommended to discuss first on
Zulip (or via a GitHub issue) so that the scope, dependencies, and placement in the library are
aligned." The Zulip thread cited in PR #635 (https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic)
shows this coordination happened.

**Action required**: Before submitting the first upstream PR, post on the CSLib Zulip describing the
planned contribution scope. Mention that it builds on the existing NaturalDeduction/Basic.lean and
Defs.lean and adds Hilbert proof systems, proof system metalogic, and Kripke semantics.

### Expectation 6: Proof Style Must Follow Mathlib Conventions

From CONTRIBUTING.md: "Please try to make proofs easy to follow. Golfing and automation are
welcome, as long as proofs remain reasonably readable and compilation does not noticeably slow down."

Task 185 partially addressed this (decomposed `prop_truth_lemma`, extracted helpers). The remaining
known style issue is the long `Combinators.lean` `app2`/Vireo proof (131 lines, uncommented stages
3-5). This file is unlikely to be in a first PR but should be noted for later contributions.

### Expectation 7: PR Title Format

From CONTRIBUTING.md: PR titles must begin with `feat`, `fix`, `doc`, `style`, `refactor`, `test`,
`chore`, or `perf`, optionally followed by a parenthetical scope.

Examples for our first PR:
- `feat(Foundations/Logic): logical connective typeclass hierarchy`
- `feat(Logics/Propositional): Hilbert proof system with axiom hierarchy`
- `feat(Logics/Propositional): Kripke semantics and completeness for classical, intuitionistic, and minimal logic`

### Expectation 8: Strong Completeness is Expected (not just Weak Completeness)

From PR #633 (xcthulhu): "What would the level of effort be to strengthen your results to strong
completeness?" This was asked immediately upon seeing the initial completeness results.

From PR #633 (xcthulhu follow-up): "Why are there still weak completeness results now if you have
strong completeness results?" — After strong completeness was added, reviewers questioned the
continued presence of weak completeness theorems.

**Action required**: If the first PR includes completeness results, it should include strong
completeness (set-based, Lindenbaum-style) directly. Having only weak completeness will trigger a
reviewer question. If only weak completeness is contributed in a first PR, this must be explicitly
addressed in the PR description ("strong completeness will follow in a subsequent PR").

---

## Section 3: CI Requirements

The CI pipeline that upstream runs (per CONTRIBUTING.md):

1. `lake build` — syntax linters run during build
2. `lake exe checkInitImports` — all files must `import Cslib.Init`
3. `lake lint` — environment linters
4. `lake exe lint-style` — text linters (100-character line limit, etc.)
5. `lake test` — CslibTests suite
6. `lake exe mk_all --module` — `Cslib.lean` must import all files
7. `lake shake --add-public --keep-implied --keep-prefix` — import minimization

**Current status** (from task 185 execution summary):
- All 7 checks PASS locally on the current branch

**Risks**:
- The upstream CI may run against a slightly different Mathlib version (PR #643 is a nightly
  adaptation that merged June 13). Our local build uses the local `lake-manifest.json`. The first PR
  should verify CI passes against the upstream `main` HEAD.
- `lake exe lint-style` enforces 100-character line limits. All citation lines in task 185 were kept
  under this limit, but any new PR-specific docstring text must also respect this limit.
- The `lake shake` import minimization check caught real issues in task 185 (transitive imports
  between Completeness and StrongCompleteness files). Any new PR must run this check.

### Files That Must Import Cslib.Init

Every file we contribute must begin with `import Cslib.Init` (or a `public import` of something
that imports it). This is enforced by `lake exe checkInitImports`. All 42 current files are
compliant.

---

## Section 4: Potential Conflicts

### Conflict 1: PR #536 (thomaskwaring — `Defs.lean` refactor)

**What it does**: Changes `IsClassical` and `IsIntuitionistic` from theory-typed to
inference-system-typed; adds `NaturalDeduction/Theory.lean`; modifies `Defs.lean`.

**Conflict with us**: If we submit any PR that modifies `Defs.lean` (e.g., to change `impl` to
`imp`, add a `bot` constructor, or register typeclass instances), PR #536 and our PR will conflict
on the same file.

**Severity**: HIGH if we touch `Defs.lean`; NONE if our first PR is purely additive.

**Mitigation**: Make the first PR purely additive (new files only), building on upstream's existing
`Defs.lean` with `impl`, `[Bot Atom]` pattern. Port our proof systems to that signature.

### Conflict 2: PR #607 (fmontesi — `Foundations/Logic/Operators/` typeclasses)

**What it does**: Introduces `HasAnd`, `HasOr`, `HasImpl`, `HasNot`, `HasBox`, `HasDiamond`,
`HasTensor`, `HasIff` classes in one-file-per-operator format under `Foundations/Logic/Operators/`.

**Conflict with us**: Our `Connectives.lean` introduces `HasAnd`, `HasOr`, `HasBot`, `HasImp`,
`HasBox`, `HasUntil`, `HasSince` in a single bundled file, plus `PropositionalConnectives`,
`ModalConnectives`, etc. The `HasAnd` and `HasOr` class names would collide if both PRs attempt to
define them in the same namespace (`Cslib.Logic`).

**Severity**: HIGH if PR #607 merges first and we still try to define `HasAnd`/`HasOr` in
`Connectives.lean`; requires adapting to use PR #607's classes instead.

**Mitigation**: If PR #607 merges, we should import its `Operators/And.lean` and `Operators/Or.lean`
rather than redefining the classes, and drop the corresponding definitions from `Connectives.lean`.

### Conflict 3: PR #542 (thomaskwaring — further Propositional API)

**What it does**: Adds theory ordering and saturated theories. Depends on PR #536.

**Conflict with us**: This PR adds new files that depend on the changed `Defs.lean` from PR #536.
If both PRs are in flight when we submit, our contribution must be compatible with whichever version
of `Defs.lean` ends up on main.

**Severity**: LOW for our first PR if we are purely additive; MEDIUM for later PRs that depend on
proof system infrastructure.

### Conflict 4: PR #587 (thomaskwaring — notation typeclasses and models)

**What it does**: Proposes `Models α β`, `ParamModels α β`, `InterpModels α β` typeclasses for
semantic frameworks.

**Conflict with us**: Our Kripke semantics uses Lean's `Set` and `Prop` directly rather than a
`Models` typeclass. If PR #587 defines a standard `Models` typeclass and it becomes expected that
all logic semantics instantiate it, our Semantics files may need to be refactored.

**Severity**: LOW for a first PR (semantics likely not in scope); MEDIUM for later Semantics PRs.

---

## Section 5: The ctchou Objection — Status and Residual Risk

### What ctchou Objected To (PR #635)

ctchou's three comments on PR #635 were all about the claim that `{imp, bot}` is the basis for
intuitionistic logic:

1. "Can all logical connectives be reduced to implication and falsum in intuitionistic propositional
   logic? I don't think `Cslib/Logics/Propositional/Defs.lean` was designed for classical
   propositional logic alone."
2. He attached the Gentzen 1935 paper and noted Gentzen did not use `{imp, bot}` alone.
3. He cited the SEP article on Heyting 1930 showing full connectives were primitive.

### How the Current Code Resolves This

The current codebase **directly addresses all three objections**:

1. `Defs.lean` now uses `{atom, bot, imp, and, or}` as five native constructors. Conjunction and
   disjunction are NOT defined as classical Lukasiewicz abbreviations — they are primitives.
2. The ND system in `NaturalDeduction/Basic.lean` has 10 primitive rules (ax, ass, andI, andE1,
   andE2, orI1, orI2, orE, impI, impE). This matches Gentzen's NJ exactly.
3. The module docstring of `Defs.lean` explicitly says: "following the standard Gentzen/Prawitz/
   Troelstra-van Dalen full-connective tradition."
4. The `Connectives.lean` docstring explicitly documents the reason for dropping Lukasiewicz:
   "The classical encodings `and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are only
   propositionally equivalent to `∧` and `∨` in classical logic ([Wajsberg1938], [McKinsey1939])"

**Residual risk from ctchou**: The ctchou objection in its original form is fully resolved. However,
ctchou may raise a **new objection** about the relationship between our `Connectives.lean` (bundled
typeclasses) and fmontesi's PR #607 (per-operator files). Since ctchou commented on PR #607
suggesting a 3-file split (Modal, Tensor, Propositional), he is engaged with the architecture.

**Action required**: In the PR description, explicitly note that `{and, or}` are now primitives
following the full-connective tradition. Cite the `Connectives.lean` docstring's references to
`[Wajsberg1938]` and `[McKinsey1939]` as justification for rejecting the Lukasiewicz approach.

### What Reviewers Will Expect to See in the PR Description

Based on PR #635 feedback and the task 171 research:

1. A clear statement of which logic tradition is being followed and why (Gentzen/Prawitz full
   connectives, not Lukasiewicz {imp, bot} reduction).
2. Explicit acknowledgment that this is an improvement over the previous PR #635 approach and why.
3. Accurate citations with BibKey format for every reference in the PR.
4. A statement of what the PR does NOT include (e.g., "full IPC with disjunction property is
   not yet formalized — this PR covers the {→, ⊥, ∧, ∨} fragment").

---

## Section 6: Confidence Assessment

| Finding | Confidence | Evidence Source |
|---------|------------|-----------------|
| ctchou objection resolved by {atom,bot,imp,and,or} constructors | HIGH | Direct code read of Defs.lean |
| Upstream `main` has different `Proposition` type (`impl`, no `bot` constructor) | HIGH | `git show upstream/main:Cslib/Logics/Propositional/Defs.lean` |
| PR #536 conflicts on Defs.lean | HIGH | `gh api` + file list inspection |
| PR #607 conflicts on HasAnd/HasOr typeclass names | HIGH | PR file inspection |
| CI requirements: all 7 checks | HIGH | CONTRIBUTING.md + task 185 summary |
| PR size limit ~300-500 lines | HIGH | PR #633 reviewer comment (chenson2018) |
| AI disclosure required | HIGH | CONTRIBUTING.md explicit policy |
| Strong completeness expected, not just weak | HIGH | PR #633 reviewer comment (xcthulhu) |
| `@[expose] public section` is standard CSLib | HIGH | Grep across Modal, Temporal, Bimodal |
| `module` keyword is standard CSLib | HIGH | Grep across all CSLib modules |
| Literature citations must be accurate to source | HIGH | ctchou PR #635 comments + Gentzen paper attach |
| PR #587, PR #542 are lower-risk conflicts | MEDIUM | Open PR list + file scope inspection |

---

## Key Takeaways for the Implementation Plan

1. **The ctchou objection is dead.** The new 5-constructor approach directly satisfies everything
   ctchou asked for. The PR description must highlight this change explicitly.

2. **The first PR should be purely additive (no Defs.lean changes).** Either build on upstream's
   existing `{atom, and, or, impl}` formula type (requiring proof porting), or make the Defs.lean
   refactor a separate first PR with narrow scope (~100 lines, clearly explained change).

3. **Coordinate with fmontesi (PR #607) and thomaskwaring (PR #536) on Zulip before submitting.**
   The CONTRIBUTING.md explicitly requires this for architectural contributions.

4. **The `Connectives.lean` approach needs reconciliation with PR #607.** Either wait for PR #607
   to merge and adapt, or propose a compatible superset (bundled classes built on top of per-operator
   files from PR #607).

5. **Include strong completeness in any completeness PR.** Weak completeness alone will trigger
   reviewer questions.

6. **All 7 CI checks must pass before submission.** The task 185 audit confirmed they currently all
   pass locally; verify against upstream main's current HEAD before the actual PR.
