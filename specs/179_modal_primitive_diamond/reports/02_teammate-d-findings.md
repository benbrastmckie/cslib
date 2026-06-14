# Teammate D (Horizons) Findings: Strategic Direction for Primitive Diamond

**Task**: 179 — modal_primitive_diamond
**Researcher role**: Horizons — long-term vision and strategic alignment
**Date**: 2026-06-14

---

## Key Findings

### 1. The Roadmap Does Not Name Intuitionistic Modal Logic as a Goal — But the Architecture Already Implies It

The ROADMAP.md describes the current effort as "porting BimodalLogic to CSLib" and focuses
on discrete/continuous completeness for bimodal and temporal logics. Intuitionistic or minimal
modal logic is not listed as a named goal.

However, the architecture already embeds the primitive-first philosophy. The `Connectives.lean`
file (contributed as part of task 188's upstream PR) justifies `HasAnd`/`HasOr` primitivity
using exactly the same argument that task 179 uses for diamond: classical equivalences collapse
the distinction only in classical logic. The docstring cites Wajsberg 1938 and McKinsey 1939
for and/or, and analogous literature exists for box/diamond (Fischer Servi 1984, Simpson 1994).

The project's documented architectural decision — five primitives `{atom, bot, imp, and, or}`
for propositional logic to support all three bases (minimal, intuitionistic, classical) — was
made explicitly to avoid baking in classical assumptions. Primitive diamond is the exact same
principle applied to modal logic. The roadmap may not list intuitionistic modal logic by name,
but the architecture commits to it implicitly.

**Conclusion**: Primitive dia is not premature optimization — it is the consistent application
of an existing architectural commitment.

### 2. Upstream Convergence: Primitive Diamond Is the Path Toward Alignment, Not Away From It

Upstream CSLib uses `{atom, not, and, diamond}` as primitives — diamond is already primitive
upstream. The fork currently does the opposite: derives diamond from box.

This creates a divergence that would need to be resolved for any future modal PR to upstream.
The three possible outcomes are:

| Scenario | What happens to diamond |
|----------|------------------------|
| Keep derived diamond | Every future modal upstream PR requires a design-debt discussion |
| Add primitive diamond now (task 179) | Fork's modal design aligns with upstream's design principle |
| Wait until a modal upstream PR is ready | Diamond divergence becomes the blocking issue for that PR |

The PR-188 execution summary shows the propositional PR is nearly ready. The PR roadmap in
`pr-description.md` outlines a 6-PR sequence: propositional first, then Hilbert, ND, semantics,
and completeness. Modal logic does not appear on the near-term roadmap — it belongs to later PRs.

However, when modal PRs do arrive, having primitive diamond in the fork will make the PR
design clean. The fork's current `{atom, bot, imp, box}` type does not align with upstream's
modal formula type. Task 179 brings the fork's modal type closer to the upstream design direction.

**Conclusion**: Primitive dia supports upstream convergence when modal PRs eventually arrive.
It is not blocking for the current propositional PR track.

### 3. Task Sequencing: 179, 180, 181 Are Parallel Foundation Refactors, Not Sequential Features

The dependency graph shows:
- Task 179 (modal dia): no dependencies beyond completed task 175
- Task 180 (temporal G/H): no dependencies beyond completed task 176
- Task 181 (bimodal dia+G+H): depends on both 179 and 180

This is the correct order: 181 is the union of 179 and 180. The three tasks cannot be
merged into one because they span different logic levels with different file sets.

The question is whether 179 and 180 should be done now versus later. Arguments against
delaying:

1. **Technical debt accumulates as files grow**: Each metalogic file added under the current
   modal formula type is a file that will need a `.dia` case added later. The modal Metalogic
   directory already has 1,370 lines across 5 files + 3,754 lines across 30 system files. Every
   completeness theorem written under the derived-diamond design is harder to maintain once the
   constructor changes.

2. **The playbook exists**: Task 177 (bimodal and/or) proved the pattern — add constructors,
   propagate match cases. The existing `01_primitive-diamond-research.md` already has the scope
   estimate (~55 files). There is no new architectural risk here.

3. **Tasks 179 and 180 block 181, which blocks nothing else currently**: The wave 2 tasks
   (39, 40, 181) are all blocked — 39 and 40 depend on tasks 36/37 which are blocked on
   upstream BimodalLogic. Task 181 depends only on 179 and 180. Doing 179 and 180 now creates
   a clean path to eventually doing 181 when 36/37 unblock.

**Should 179 and 180 be done together (parallel)?** Yes. They are independent tasks (different
codebases), both are [NOT STARTED] with research available, and neither blocks the other. The
team could run them in parallel via `--team` if resources allow.

### 4. The Generic Connective Alternative: Not Worth Pursuing Now

The "creative alternative" of a generic `Connective` type or modular proposition builder using
typeclasses is worth examining strategically.

The `HasBox`/`HasDia`/`HasUntil`/`HasSince` classes already exist in `Connectives.lean`.
Crucially, `ModalConnectives` does **not** include a `HasDia` class — there is no `HasDia`
currently. Adding primitive `dia` will require either:

1. Adding `HasDia` to `Connectives.lean` and extending `ModalConnectives` to include it
2. Or keeping diamond purely as a constructor with no typeclass backing

Option 1 is the correct long-term approach. The `Foundations/Logic/Axioms.lean` file has
`HasAxiomB` that references `◇` through the derived `diamond` abbrev. With primitive dia,
axiom B (`φ → □◇φ`) would use the primitive `.dia` constructor directly, which is cleaner.

The pattern of extending `Connectives.lean` with new typeclass entries as each logic level
adds primitives is already established. `HasBox` was added for modal; the parallel for diamond
would be `HasDia`. This is not a new generic architecture — it is the existing architecture
already supporting exactly this use case.

**Conclusion**: No new generic architecture is needed. `HasDia` fits cleanly into the
existing `Connectives.lean` hierarchy. This should be part of task 179's scope.

### 5. The Case for "Not Now" Is Weak — The Case for "Now" Is Strong

A "not now" decision would only make sense if:
- The task were very large and high-risk (it is not — task 177 at 127 files was larger)
- It contradicted a roadmap commitment (it does not — nothing in the roadmap says "keep diamond derived")
- The upstream strategy called for modal PRs with derived diamond first (upstream already has primitive diamond)
- There were competing priorities that made task 179 a distraction (tasks 188 and 192 are propositional, independent)

None of these conditions hold. The existing research report (01_primitive-diamond-research.md)
has already done the conceptual work. The implementation playbook exists from task 177.

---

## Recommended Approach

**Proceed with task 179 as described, extended with a `HasDia` typeclass addition.**

Specific recommendations:

1. **Do task 179 now**: The architectural consistency argument is strong, the research is
   complete, and the playbook is proven. There is no strategic reason to delay.

2. **Add `HasDia` to `Connectives.lean`**: This is a natural companion step. The typeclass
   hierarchy currently has `HasBox` but no `HasDia`. Adding it makes the connective abstraction
   complete for modal logic and keeps `ModalConnectives` aligned with what the PR-188 roadmap
   contributes upstream.

3. **Extend `ModalConnectives` to include `HasDia`**: After task 179, `ModalConnectives` should
   extend `PropositionalConnectives`, `HasBox`, and `HasDia` — the full primitive set for
   classical/intuitionistic modal logic.

4. **Run tasks 179 and 180 in parallel if resources allow**: They are independent and follow
   the same pattern. Completing both together unlocks 181.

5. **Defer task 181 until 179 and 180 are complete**: The bimodal layer must track the union
   of modal and temporal primitives. Do not attempt to add dia to bimodal until the modal and
   temporal layers establish the pattern.

6. **No new axioms or design patterns are needed**: The zero-debt policy is satisfied by the
   existing strategy — new primitive constructors propagate through match cases, and classical
   equivalences become theorems rather than definitions.

---

## Evidence and Examples

### Evidence 1: Upstream Already Has Primitive Diamond

From `01_team-research.md` (task 188): "Upstream uses `{atom, not, and, diamond}` as primitives."
Task 179 closes the design divergence: the fork's `{atom, bot, imp, box}` becomes `{atom, bot,
imp, and, or, box, dia}` — a superset of upstream's primitive set that adds the full propositional
base and keeps box as an equal citizen with diamond.

### Evidence 2: The `Connectives.lean` Hierarchy Is Missing `HasDia`

Current `Connectives.lean` defines:
```
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
```
Diamond is absent. Adding `HasDia` and extending `ModalConnectives` is consistent with the
existing pattern and was likely deferred to exactly this task. The docstring notes "diamond
(possibility) are derived connectives" — after task 179, this changes.

### Evidence 3: Formula Type Divergence Is Already Documented as a Problem

From `01_primitive-diamond-research.md`: "The fork (current) uses `{atom, bot, imp, and, or,
box}` — derives dia classically. This is not logic-neutral." The research report explicitly
flags the current state as a design limitation. Task 179 is the prescribed fix.

### Evidence 4: Scope Is Comparable to Completed Tasks

Task 177 (bimodal and/or) involved ~127 files and is complete. Task 179 targets ~55 modal
files — smaller scope, same pattern. The 8,084-line modal codebase is well-bounded.

### Evidence 5: No Competing Roadmap Priority Is Blocked by Task 179

Wave 1 tasks: 36, 37 (blocked externally), 179, 180, 188, 192 (propositional PR track).
Tasks 188 and 192 are independent of modal logic. Running 179 in parallel with the propositional
PR work creates no conflicts.

---

## Confidence Level

**HIGH** — The strategic case for proceeding with task 179 is strong and multi-dimensional:
architectural consistency, upstream convergence, logical completeness of the connective
hierarchy, and concrete evidence that the scope and playbook are well-understood. The only
open question is whether `HasDia` should be added to `Connectives.lean` in the same task (179)
or deferred — the recommendation is to include it in 179's scope as a one-line typeclass
addition with minimal risk.
