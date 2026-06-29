# PR #607 Engagement — Factual Comparison Tables

> **FACTUAL SCAFFOLDING — Points for a human-authored review. Rewrite every sentence in your
> own words before posting (CSLib Zulip AI policy #605827029). No paragraph here is
> ready-to-post prose.**
>
> These tables are building blocks, not a review text. They anchor to the verified live-PR data
> in `reports/02_engagement-strategy.md`; numbers and class names are taken from the raw diff.
> The existing `benbrastmckie` comment (2026-06-17, `issuecomment-4735753144`) has already
> raised several of these points; where that is so, the "prior comment" column notes it — do
> not restate those points, build on them.

---

## Table 1: #607's Eight `HasX` Classes (verbatim from the live diff)

Source: `Cslib/Foundations/Logic/Operators/` sub-directory in #607's diff.
All eight are bare `class … (α : Type*)` mixins with a single method,
`@[expose] public section`, `import Cslib.Init`.

| Class | Method | Notation declaration | Prec / assoc | File |
|---|---|---|---|---|
| `HasAnd` | `and (a b : α) : α` | `scoped infixr:36 " ∧ "` | 36, right | `Operators/And.lean` |
| `HasOr` | `or (a b : α) : α` | `scoped infixr:30 " ∨ "` | 30, right | `Operators/Or.lean` |
| `HasImpl` | `impl (a b : α) : α` | `scoped infixr:25 " → "` | 25, right | `Operators/Impl.lean` |
| `HasNot` | `not (a : α) : α` | `scoped notation:max "¬" p:40` | arg at 40 | `Operators/Not.lean` |
| `HasIff` | `iff (a b : α) : α` | `scoped infixr:20 " ↔ "` | 20, right | `Operators/Iff.lean` |
| `HasBox` | `box (a : α) : α` | `scoped prefix:40 "□"` | 40 | `Operators/Box.lean` |
| `HasDiamond` | `diamond (a : α) : α` | `scoped prefix:40 "◇"` | 40 | `Operators/Diamond.lean` |
| `HasTensor` | `tensor (a b : α) : α` | `scoped infixr:35 " ⊗ "` | 35, right | `Operators/Tensor.lean` |

**Gaps relative to the fork**: No `HasBot`, no `HasTop`, no bundle class. `HasNot` is a
standalone primitive with no link to `⊥`.

---

## Table 2: Notation Divergences — Fork's `PL.Defs` vs #607's Operators

| Operator | Fork (`PL.Defs.lean`) | #607 (`Operators/*.lean`) | Difference |
|---|---|---|---|
| `∧` | `scoped infix:36` (non-assoc) | `scoped infixr:36` | Associativity: non-assoc vs right |
| `∨` | `scoped infix:35` (non-assoc) | `scoped infixr:30` | Both assoc and precedence differ |
| `→` | `scoped infix:30` (non-assoc) | `scoped infixr:25` | Both assoc and precedence differ |
| `↔` | `scoped infix:20` (non-assoc) | `scoped infixr:20` | Associativity only |
| `¬` | `scoped prefix:40` | `scoped notation:max "¬" p:40` | Minor form difference |

**Key observation**: The fork's non-assoc `infix` means `a ∧ b ∧ c` is a parse error; #607's
`infixr` parses it right-associatively as `a ∧ (b ∧ c)`. The `infixr` form is more usable
(matches mathematical convention and Mathlib). The fork should adopt #607's `infixr` ladder
once the typeclass notation supersedes the local declarations.

---

## Table 3: Naming Options Table — `Has` prefix + `impl` vs `imp`

Two independent decisions are conflated in the naming discussion; they should be resolved
separately but in the same review thread.

### Decision A — `Has` prefix

| Option | Supported by | Counter-argument |
|---|---|---|
| Keep `HasX` (e.g., `HasAnd`, `HasImpl`) | Matches CSLib's existing `HasFresh`, `HasContext`, `HasSubstitution` (Foundations/Syntax) | eric-wieser (Mathlib maintainer): "the `Has` prefix is largely a Lean-3-ism" |
| Drop `Has` (e.g., `And`, `Or`, `Impl`) | Mathlib-4 idiom (`Bot`, `Top`, `Add`, `Mul`, …) | `And`, `Or`, `Iff` already exist in Lean core/Mathlib as types — concrete name collision risk |

**Concrete collision**: bare `And`, `Or`, `Iff` shadow `core.And : Prop → Prop → Prop`,
`Mathlib.Or`, `Iff` (a `Prop`-level biconditional typeclass). This is a **concrete reason
CSLib may retain `Has`**, not just inertia. The review should surface this trade-off
explicitly and ask the maintainers for a ruling rather than silently adopting either option.
(Point already partially in the prior comment for `impl`/`imp`; the `Has`-prefix angle is new.)

### Decision B — `impl` vs `imp`

| Option | Supported by | Counter-argument |
|---|---|---|
| `impl` / `HasImpl` | #607 (current) | Longer; the `impI`/`impE` natural-deduction rule-prefix convention already uses `imp` |
| `imp` / `HasImp` | `benbrastmckie`'s prior comment; FormalizedFormalLogic convention | #607 currently uses `impl`; renaming is a diff-cost |

**Status**: Already raised in the prior comment. The review should close the loop by asking for
a final decision, not re-open the debate.

---

## Table 4: Notation Precedence Ladder

The precedence ladder #607 establishes (left = binds tighter):

```
↔  20  (infixr)    — loosest; biconditional
→  25  (infixr)
∨  30  (infixr)
⊗  35  (infixr)    — linear tensor
∧  36  (infixr)
¬  40  (prefix)    — tightest propositional unary
□  40  (prefix)
◇  40  (prefix)
```

**Comparison with standard references**: This ladder matches Prawitz/Gentzen typographical
convention (`¬ > ∧ > ∨ > →`) with `↔` outermost. It is also consistent with Mathlib's
propositional notation (Mathlib uses `∧` at 35, `∨` at 30, `→` right-assoc; the 1-point
difference for `∧` here is cosmetic).

**Open question the review should raise**: `→` at precedence 25 *shadows* Lean's core `→`
(Prop implication, which is also right-assoc at similar precedence) inside the
`open scoped HasImpl` scope. Confirm that mixed object-level/meta-level formulas parse
correctly and that this doesn't cause issues in proofs that mix propositional and Prop implication
in the same expression.

**NOTATION.md status**: NOTATION.md is currently silent on logical connectives (it covers only
operational-semantics arrows and equivalences). #607 is effectively setting the library-wide
connective precedence standard. Recommend recording the agreed ladder in NOTATION.md as a
by-product of the PR — a concrete, low-effort contribution offer.

---

## Table 5: File Organisation Options

Three independent reviewers converged on "consolidate":

| Reviewer | Proposal | Detail |
|---|---|---|
| eric-wieser | Single file | "merge all these operators into a single `LogicOperators` file" with one conventions docstring |
| ctchou | 3-file split | `Modal` (box + diamond), `Tensor` alone, `Propositional` for the rest |
| chenson2018 | Single file | Agreed with eric-wieser on consolidation (separate from the `_def` direction issue) |

**Recommendation point for the review**: Consensus exists — pick *one* of these and endorse it.
The single-file option (`Operators.lean` or `LogicOperators.lean`) has the largest reviewer
support and is lowest-friction for fmontesi.

**Note on ORGANISATION.md**: The fork's `ORGANISATION.md` currently lists `Axioms.lean` as
the home of connective typeclasses and `Connectives.lean` as "derived abbreviations" — both
stale after the task-340/task-407 refactors. Whatever file layout lands in #607 should be
reflected in ORGANISATION.md (a Phases 7/8 item, gated on upstream resolution).

---

## Table 6: Prior-Comment Anchoring (to avoid restating benbrastmckie's 2026-06-17 entry)

| Topic | Status |
|---|---|
| Overlap with #648's `Connectives.lean` | Raised in prior comment; now resolved (`Connectives.lean` removed from #648 per commit `85db79a6`) |
| `HasImpl`/`impl` vs `HasImp`/`imp` | Raised; unresolved (needs a decision) |
| Primitive `bot` / primitive `box` motivating argument | Raised (substitution invariance, free-algebra property, necessitation as a pure rule) |
| Falsum/verum via Mathlib `Bot`/`Top` + derived-`¬` bridge | **NOT yet raised** — this is the primary new technical point |
| `_def` lemma direction (chenson's CHANGES_REQUESTED) | **NOT yet raised** — new; the modal proof verbosity is the exhibit |
| eric-wieser's `Has`-prefix comment | **NOT yet raised** explicitly; counter-argument (name collision) is new |
| File consolidation (eric-wieser/ctchou/chenson consensus) | **NOT yet raised** — easy endorsement |
| Tidier instance syntax (`where and := .and`) | **NOT yet raised** — eric-wieser endorsement |
| Notation precedence → NOTATION.md | **NOT yet raised** |
| Bundles as a follow-up PR | **NOT yet raised** |

---

*All data in this file is derived from the live-PR diff and `reports/02_engagement-strategy.md`.
No claim here should be used without verifying it against those primary sources.*
