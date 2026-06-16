# Research Report: Task #222

**Task**: Review PR #648 changes on feat/propositional-v2 and analyze Zulip feedback
**Date**: 2026-06-16
**Mode**: Team Research (4 teammates)

## Summary

PR #648 ("feat(Logics/Propositional): five-primitive formula type with primitive bot") was re-submitted after reviewer feedback from ctchou (CHANGES_REQUESTED) and thomaskwaring (comment with 5 detailed objections). The re-submission successfully addresses most mechanical reviewer requests (semantics split out, German references replaced, rebased on #536) but leaves two significant unresolved issues: (1) a naming conflict with PR #607 (`HasImp` vs `HasImpl`) that the PR description incorrectly claims is "aligned," and (2) thomaskwaring's design-level objection to primitive bot remains on record without resolution. The Zulip thread reveals a deeper architectural tension between three visions for CSLib's propositional layer that should inform next steps.

## Key Findings

### 1. Bot as Primitive vs Atom — Design Disagreement (OPEN)

**The positions:**
- **ctchou** (reviewer, CHANGES_REQUESTED): "I like the idea of adding ⊥ as a primitive." **Supports.**
- **Matthew Doty**: "I do agree with @Ching-Tsun Chou about a separate bot constructor." **Supports.**
- **thomaskwaring** (reviewer): Raises five detailed objections. **Opposes**, or at least wants more discussion.

**thomaskwaring's five points and their status in the re-submission:**

| # | Objection | Addressed? | Assessment |
|---|-----------|------------|------------|
| 1 | Bot behaves like an atom in MPL — why not represent it as such? | Partially | PR acknowledges trade-off but does not rebut the philosophical point |
| 2 | MPL works without ⊥ (Curry-Howard) | No | Not addressed in PR description or response |
| 3 | Extra constructor makes proofs more verbose | Acknowledged | PR admits trade-off; `subst` now has `\| bot => .bot` case. Overhead is real but small |
| 4 | WithBot.some for conservativity needs non-bot-preserving maps | Acknowledged | `intuitionisticCompletion` still uses `WithBot.some`; compatibility preserved but not explained |
| 5 | `⊤ = a → a` is a feature | Addressed | New `top := ⊥ → ⊥` is unconditional (no `[Inhabited Atom]`), a genuine improvement |

**Synthesis:** Primitive bot is the right foundational choice for CSLib's scope (propositional → modal → temporal → bimodal). The constraint elimination is substantial: `[Bot Atom]` previously appeared in `IPL`, `CPL`, `IsIntuitionistic`, `IsClassical`, `LEM`, `Pierce`, `neg`, `top`, and all downstream signatures. The extra `bot` case in recursions is minor. However, thomaskwaring's conservativity point (WithBot.some maps) is technically valid — the design accommodates it but the PR should explain how more clearly.

**Confidence**: HIGH

### 2. HasImp vs HasImpl — Naming Conflict with PR #607 (UNRESOLVED, HIGH IMPACT)

This is the most significant unaddressed issue across all teammate analyses.

**The conflict:**
- PR #648 defines `HasImp` (method: `imp`) in `Connectives.lean`
- PR #607 (fmontesi) defines `HasImpl` (method: `impl`) in `Operators/Impl.lean`
- PR #587 (thomaskwaring, draft) also uses `HasImpl`/`impl`
- The upstream merged code on main uses `impl` as the `Proposition` constructor name

**PR #648's claim:** "Connectives.lean is aligned with [#607's] direction." This is **inaccurate** — they share the per-operator typeclass pattern but diverge on the critical implication naming. If both PRs merge, the codebase gets two competing implication typeclasses.

**Additional conflict:** Notation priorities differ. PR #648 uses `infix:30` for `→`; PR #607 uses `infixr:25`. Different precedence and associativity.

**Recommendation:** Adopt `HasImpl`/`impl` in PR #648 to align with both #607 and #587. The cost is a rename; the benefit is eliminating a merge blocker and signaling collaborative intent. FormalizedFormalLogic uses `imp`, but CSLib's emerging convention (two independent PRs) favors `impl`.

**Confidence**: HIGH

### 3. Semantics Prop/Bool/GHA — Correctly Deferred (RESOLVED for this PR)

**What happened:** The original PR included both `Semantics/Basic.lean` (Prop-valued `Evaluate`) and `Semantics/Bool.lean` (Bool-valued `BoolEvaluate`). ctchou wanted Bool only; thomaskwaring wanted semantics split to a separate PR. The re-submission removes both files.

**The deeper design question (for the follow-up):**

thomaskwaring proposes evaluating over `GeneralizedHeytingAlgebra` (GHA), unifying Bool and Prop as special cases. This is technically correct and necessary for minimal logic completeness:

- **HeytingAlgebra** (Matthew Doty's suggestion): Maps `bot → ⊥_algebra`. This forces `⊥ ≤ x` for all x (ex falso quodlibet), making it IPL-only. **Fails for MPL.**
- **GeneralizedHeytingAlgebra** (thomaskwaring): No required ⊥ element. The canonical Lindenbaum-Tarski algebra for MPL has bot-as-non-absorbing. **Works for MPL, IPL, and CPL.**

**Critical subtlety with primitive bot + GHA:** If `Proposition` has a primitive `bot` constructor, the GHA evaluation function needs a way to interpret it. Since GHA doesn't have a canonical ⊥, the follow-up semantics PR must either:
1. Add a separate `bot_val : H` field to the model structure
2. Extend the valuation to cover `bot` as well as atoms

This is a genuine design constraint that the Zulip discussion identified correctly.

**Unverified claim flagged:** Matthew Doty suggested using `decide` to collapse `canonicalValuation` to Bool: `fun p => decide (Proposition.atom p ∈ S)`. This technically works because `StrongCompleteness.lean` has `attribute [local instance] Classical.propDecidable` — but the resulting `decide` is **noncomputable**, offering zero computational benefit over the Prop version. Neither participant noted this in the discussion.

**Confidence**: HIGH

### 4. Reviewer Feedback Response Status

| Reviewer Request | Status | Notes |
|-----------------|--------|-------|
| ctchou: likes primitive bot | ✅ Maintained | — |
| ctchou: drop dual semantics files | ✅ Both removed | Deferred to follow-up |
| ctchou: English references | ✅ Avigad 2022 used | All German refs removed |
| ctchou: wait for #536 | ✅ Rebased | #536 merged 2026-06-16 |
| ctchou: coordinate with #607/#587 | ⚠️ Claimed but inaccurate | HasImp ≠ HasImpl; path collision with #587 |
| thomaskwaring: split semantics | ✅ Split out | — |
| thomaskwaring: bot-as-primitive concerns | ⚠️ Partially addressed | 5 points acknowledged but not all rebutted |
| thomaskwaring: GHA evaluation | ✅ Acknowledged | "elegant… explore that direction" |
| thomaskwaring: imp/impl naming | ⚠️ Open | PR says "open to reverting"; no reviewer confirmation |

### 5. Additional Issues Identified

**Proposition.iff — half-finished addition:** The PR adds `abbrev Proposition.iff` with `↔` notation but provides no accompanying API lemmas (e.g., iff introduction, iff elimination, `Evaluate_iff`). This is incomplete.

**top definition changed semantically:** Old: `impl (.atom default) (.atom default)` (= `A → A` for arbitrary atom). New: `.imp .bot .bot` (= `⊥ → ⊥`). These are propositionally equivalent in all logics but definitionally different. Code relying on `top = impl (.atom default) (.atom default)` would break.

**Copyright/authorship:** Three files add "2026 Benjamin Brast-McKie" as co-author to thomaskwaring's original work. The changes are substantial enough to justify co-authorship, but thomaskwaring was not explicitly asked to approve this in the review thread.

**instIsIntuitionisticIntuitionisticCompletion:** New instance for `IsIntuitionistic (WithBot Atom) T.intuitionisticCompletion`. Appears correct and useful; no diamond instance concerns identified.

**Confidence**: HIGH

## Synthesis

### Conflicts Resolved

| Conflict | Resolution |
|----------|-----------|
| Teammate A/B disagree on whether Modal uses `impl` | Teammate A checked code directly — the upstream merged Modal code does NOT use `impl` as a Proposition constructor. thomaskwaring's comment refers to the old (now-replaced) `Proposition.impl` or to draft PRs (#587, #607), not merged code |
| Teammate B flags local main vs PR branch divergence on IsIntuitionistic | This is expected — local fork has completeness work not in the upstream PR. Not a conflict, just scope difference |

### Gaps Identified

1. **No follow-up PR/issue tracking for deferred semantics** — the GHA evaluation, BoolEvaluate bridge, and Kripke semantics are deferred but not tracked. Risk of losing the work.
2. **No downstream breakage audit** — the `imp`→`impl` rename affects all code using `implI`/`implE` constructors. The PR does not audit this.
3. **Bimodal/temporal compatibility unverified** — benbrastmckie's local fork has substantial temporal and bimodal code. Whether it compiles against the new API is unverified from the PR alone.

### Recommendations

**Immediate (before next push):**
1. **Rename `HasImp` → `HasImpl`** in Connectives.lean — removes the #607 conflict, costs one rename
2. **Add a PR comment** explicitly noting the Connectives.lean path collision with #587 and proposing coordination
3. **Clarify the ctchou "Bool only" ambiguity** — his comment may have meant "drop Evaluate entirely." The PR response should include a clear paragraph on why Prop-valued `Evaluate` cannot be dropped (Kripke uniformity across modal/temporal logics)

**Post-merge:**
4. **Open a Zulip thread** on `Connectives.lean` joint design before submitting completeness PRs
5. **Submit completeness work in small increments** — one Hilbert system per PR (MinPropAxiom first, then IntPropAxiom, then PropositionalAxiom)
6. **Create a follow-up issue** for the semantics PR with the GHA direction explicitly stated

**Strategic:**
7. Before any Modal PR, open a Zulip discussion on `{atom, bot, imp, box}` vs `{atom, not, and, diamond}` formula primitives
8. Frame the GHA approach as complementary to (not competing with) the Kripke approach — propose bridging theorems

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary PR analysis — issue-by-issue verification | completed | high |
| B | Design tensions — Prop/Bool/GHA, typeclass conflicts | completed | high |
| C | Critic — claim verification, missing considerations | completed | high |
| D | Strategic horizons — PR sequencing, community dynamics | completed | high |

## References

- PR #648: https://github.com/leanprover/cslib/pull/648
- PR #536 (merged): InferenceSystem refactor
- PR #587 (draft, thomaskwaring): Notation typeclasses and models
- PR #607 (open, fmontesi): Logical operators
- Zulip thread: specs/221_revise_pr649_reviewer_feedback/zulip.md
- Avigad, J. (2022). *Mathematical Logic and Computation*. Cambridge University Press.
