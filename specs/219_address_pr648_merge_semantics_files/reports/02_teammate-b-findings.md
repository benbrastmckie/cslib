# Teammate B Findings: PR Coordination and Alternative Strategies

## Key Findings

### 1. PR #536 Status: Clean, Mergeable, Should Be First

PR #536 (`refactor(Logics/Propositional): classical and intuitionistic inference systems`)
by thomaskwaring is **mergeable with a clean state** — `gh api` confirms `mergeable: true`,
`mergeable_state: "clean"`, not a draft. ctchou explicitly said "#536 is ready to merge, so
you should wait for it."

**What #536 changes in `Defs.lean`**: It replaces `IsIntuitionistic`/`IsClassical` from
theory-based (inhabiting a Theory type) to inference-system-based (inhabiting an InferenceSystem
type). This directly conflicts with PR #648's `Defs.lean` changes: both PRs modify
`IsIntuitionistic`, `IsClassical`, `IPL`, `CPL`, and their associated theorems. They cannot
be merged independently without rebase.

**Action**: Wait for #536 to merge, then rebase PR #648's `Defs.lean` hunk on top of #536's
`Defs.lean`. The conceptual changes (bot as primitive, imp renamed from impl) are compatible
with #536's inference-system refactor — they operate on different parts of the file.

### 2. PR #607 Status: Open With Merge Conflict (Dirty)

PR #607 (`feat(Logic): logical operators`) by fmontesi is **currently dirty** — `gh api`
reports `mergeable: false`, `mergeable_state: "dirty"`. It introduces operator typeclasses
in separate files: `Foundations/Logic/Operators/{And,Or,Impl,Not,Box,Diamond,Iff,Tensor}.lean`.

**Naming conflict with PR #648**:
- PR #607 uses `HasImpl` (for implication) and `HasNot` (for negation)
- PR #648 uses `HasImp` (for implication) and does not define `HasNot` (negation stays derived)
- PR #607 also introduces `HasIff`, `HasBox`, `HasDiamond`, `HasTensor` — none in PR #648

**File collision**: PR #607 changes `Cslib/Logics/Propositional/Defs.lean` to replace direct
notation (`scoped infix:30 " → " => Proposition.impl`) with typeclass instances. PR #648
also heavily refactors `Defs.lean` (renames `impl` to `imp`, adds `bot` as primitive,
replaces `[Bot Atom]` constraints). These two patches **cannot both apply** to `Defs.lean`
without manual resolution.

**PR #648's `Connectives.lean` pre-empts #607's design**: PR #648 creates
`Cslib/Foundations/Logic/Connectives.lean` with `HasBot`, `HasImp`, `HasAnd`, `HasOr`,
`PropositionalConnectives`. PR #587 *also* creates `Cslib/Foundations/Logic/Connectives.lean`
with `HasImpl`, `HasAnd`, `HasOr`, `HasNot`. These are the same filename with different
content — a direct conflict.

### 3. PR #587 Status: Open Design Proposal (Not Ready to Merge)

PR #587 (`feat(Foundations/Logic): Notation typeclasses and models`) by thomaskwaring is a
**design draft** — the PR description explicitly says "the design ought to be discussed before
we settle on anything this general." It is marked open, no mergeable_state data.

**Two versions of `Model.lean`** exist in the PR: `Model.lean` and `ModelOld.lean` — it is
clearly in flux. Reviewer comments on #587 express concerns about notation direction and
whether `HeytingModel` is necessary.

**Overlap with PR #648's `Semantics/Basic.lean`**:
- PR #587's `Model.lean` (the newer version) defines `PL.Valuation (Atom : Type*) := Atom → Prop`
  and `PL.Valuation.interp` — these are structurally identical to PR #648's `Valuation` and
  `Evaluate` in `Semantics/Basic.lean`
- PR #587 wraps this in an `InterpModels` framework; PR #648 defines them standalone
- This means that if #587 merges first, PR #648's `Semantics/Basic.lean` would need to
  either import `#587`'s model or be restructured to expose instances of `HasEntails`

### 4. Direct File Collision Map

| File | PR #648 | PR #607 | PR #587 | PR #536 |
|------|---------|---------|---------|---------|
| `Foundations/Logic/Connectives.lean` | Creates (new) | — | Creates (new, same path!) | — |
| `Foundations/Logic/Operators/*.lean` | — | Creates 8 files | — | — |
| `Logics/Propositional/Defs.lean` | Modifies heavily | Modifies (notation→instances) | — | Modifies (IsClassical refactor) |
| `Logics/Propositional/NaturalDeduction/Basic.lean` | Modifies (impI/impE rename) | — | — | Modifies (IsIntuitionistic refactor) |
| `Logics/Propositional/Semantics/Basic.lean` | Creates (new) | — | Provides equivalent via `PL.Valuation` | — |
| `Logics/Propositional/Semantics/Bool.lean` | Creates (new) | — | — | — |
| `Cslib.lean` | Modifies | — | — | Modifies |

**Hard conflicts** (same file, incompatible changes): `Defs.lean` between #648 and #607;
`Connectives.lean` between #648 and #587.

### 5. Operator Naming: The HasImpl vs HasImp Divergence

This is the most subtle conceptual conflict. PR #607's `HasImpl` is the existing community
direction from fmontesi (who is apparently a CSLib maintainer given the review weight). PR #648
uses `HasImp` — a reasonable alternative but different. PR #587 also uses `HasImpl`.

The community appears to be converging toward `HasImpl` (two PRs vs one). PR #648 should
**adopt `HasImpl` as the implication typeclass name** to align, or else open a naming
discussion on Zulip before the PR is finalized.

Note also: PR #607 keeps `Proposition.impl` as the field name in Defs.lean (via typeclass
instance `HasImpl (Proposition Atom) := {impl := Proposition.impl}`). PR #648 renames it
to `Proposition.imp`. This is a deeper API break — `impl` → `imp` affects all downstream
code that pattern-matches on the constructor.

### 6. The Connectives.lean Collision Is the Critical Blocker

The fact that both PR #648 and PR #587 create `Cslib/Foundations/Logic/Connectives.lean` at
the same path with different content is the **single most dangerous coordination failure**. If
either merges first, the other needs a complete rewrite of that file.

PR #648's version defines: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`
PR #587's version defines: `HasImpl`, `HasAnd`, `HasOr`, `HasNot`, `instNotImplBot`

These differ in: the implication class name (HasImp vs HasImpl), presence of `HasBot` (648
has it, 587 doesn't), presence of `HasNot` (587 has it, 648 doesn't), and the bundled
class (648's `PropositionalConnectives extends HasBot, HasImp`; 587 has no bundled class).

## Recommended Approach

### Option A: Minimum-Conflict Immediate Merge (Best for ctchou satisfaction)

1. **Wait for #536 to merge** (already clean/mergeable, only waiting on timing)
2. **Rebase PR #648** on top of #536 (resolve `Defs.lean` and `NaturalDeduction/Basic.lean`)
3. **Do the file merge** (Basic.lean + Bool.lean → Semantics.lean) as the primary ctchou ask
4. **Update references** to Avigad chapters 2-3
5. **Leave Connectives.lean as-is** with a comment acknowledging overlap with #607/#587,
   and add a note to the PR description flagging the naming divergence for maintainer discussion
6. **Do not restructure to match #587's HasEntails** — that's a separate design decision

This satisfies all four of ctchou's explicit requests and minimizes the conflict surface.

### Option B: Align with #607 Before Merging (Higher Quality, Slower)

1. Wait for #536 to merge
2. Rebase on #536
3. Rename `HasImp` to `HasImpl` and `Proposition.imp` to `Proposition.impl` in PR #648 to
   align with the converging community direction (#607, #587 both use `HasImpl`)
4. Coordinate with fmontesi to merge #607 (or at least confirm #607's naming conventions)
5. Move operator typeclasses to `Operators/Impl.lean` etc. or consolidate with #607's design
6. Do the file merge and reference update

This produces a cleaner library but requires coordination with fmontesi (currently not engaged
in the PR thread).

### Option C: Wait for #607 to Clarify (Slow, Safest Long-Term)

The dirtiness of #607 (merge conflict) suggests active work. Opening a Zulip discussion to
synchronize #607, #587, and #648 on `Connectives.lean` naming before any of them merge would
prevent technical debt. But this could delay #648 for weeks.

**Recommendation: Option A with one addition** — before submitting the revised PR, post a
Zulip message tagging fmontesi and thomaskwaring noting the `HasImp`/`HasImpl` divergence and
asking if they prefer one name so that PR #648 can adopt the consensus. This is a 1-day delay
that prevents a naming inconsistency from entering the library.

## Evidence/Examples

**#536 `Defs.lean` conflict with #648**: Both modify `IsIntuitionistic` class definition —
#536 changes it from `[Bot Atom]`-parameterized to `InferenceSystem`-parameterized; #648
removes the `[Bot Atom]` parameter entirely by making `bot` a primitive constructor. The
end goal is compatible but the rebase path requires manual resolution.

**#607 `Defs.lean` conflict with #648**: #607 changes notation lines to instances
(`HasImpl`, `HasAnd`, etc.) while keeping `impl` as the constructor name. #648 renames
`impl` to `imp` and introduces `HasImp` instead of `HasImpl`. These cannot both apply.

**#587 `Connectives.lean` collision with #648**: Same filename, different classes. If #587
merged first, PR #648's `Connectives.lean` would need to be rewritten to either:
(a) extend #587's classes with `HasBot` and bundled `PropositionalConnectives`, or
(b) replace #587's approach.

**Prop-valued `Evaluate` vs. #587's `PL.Valuation.interp`**: Both implement the same
recursive function (`atom → v x`, `bot → False`, `imp → →`, `and → ∧`, `or → ∨`). If #587
merges, the right move is to define `Evaluate v φ := HasInterp.interp v φ` and get rid of
the standalone definition, but that requires importing #587's framework.

## Confidence Level

- **PR #536 status** (wait, rebase required): **high** — confirmed by `gh api` and ctchou's
  comment
- **PR #607 naming conflict** (HasImpl vs HasImp): **high** — direct comparison of patches
- **PR #587 Connectives.lean collision** (same filename): **high** — both patches create
  the file at `Cslib/Foundations/Logic/Connectives.lean`
- **Recommended approach (Option A + Zulip note)**: **medium-high** — satisfies immediate
  reviewer requests while flagging the design coordination issue
- **Long-term #587 integration path** (HasEntails framework): **medium** — PR #587 is
  explicitly a draft; its final form may change significantly
