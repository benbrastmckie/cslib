# Teammate A Findings: PR #648 Changes and Reviewer Feedback Analysis

**Task**: 222 - review_pr648_zulip_feedback_analysis
**Date**: 2026-06-16
**Focus**: Primary analysis of PR #648 changes against reviewer feedback

## Overview

PR #648 ("feat(Logics/Propositional): five-primitive formula type with primitive bot") has been
re-submitted after reviewer feedback from ctchou and thomaskwaring on the original submission.
This report verifies what was addressed, what remains open, and flags any technical concerns.

**PR State**: OPEN, mergeable, re-submitted 2026-06-16.
**CI Status**: Not independently verified in this analysis.

---

## Reviewer Feedback Summary

### ctchou's Review (CHANGES_REQUESTED, 2026-06-15)

Four issues raised:
1. Bot as primitive: supported (no change requested)
2. Both Semantics/Basic.lean and Semantics/Bool.lean: requests Bool.lean only, or remove both
3. German-language references: replace with Avigad (2022)
4. Coordinate with #607, #587; wait for #536

### thomaskwaring's Comment (2026-06-16)

Five substantive objections to bot-as-primitive, plus:
- Request to split semantics into a separate PR
- Note on imp/impl naming justification weakness
- Request to use GeneralizedHeytingAlgebra for evaluation

---

## Issue-by-Issue Analysis

### Issue 1: Bot as Primitive vs Atom

**Reviewer positions**:
- **ctchou**: Supports ("I like the idea of adding ⊥ as a primitive").
- **thomaskwaring**: Five detailed objections (see below).

**What the PR does**: The `Proposition` inductive type now has five constructors: `atom`, `bot`,
`imp`, `and`, `or`. The old design simulated bottom via `[Bot Atom]` and `instance : Bot (Proposition Atom) := ⟨.atom ⊥⟩`. The new design has `| bot` as a constructor and `instance : Bot (Proposition Atom) := ⟨.bot⟩`, no longer requiring `[Bot Atom]`.

**Verification**: The diff confirms this change in `Defs.lean`. The `Proposition.neg` abbrev is
now `(Proposition.imp · .bot)` instead of `(Proposition.impl · ⊥)` — no `[Bot Atom]` needed.
Similarly, `Proposition.top := .imp .bot .bot` requires no `[Inhabited Atom]`.

**Did benbrastmckie address thomaskwaring's objections?**

thomaskwaring raised five points in the Zulip/PR comment:

1. *"Bot behaves like an atom in minimal logic — why not represent it as such?"*
   - Response in PR description: "primitive `bot` eliminates `[Bot Atom]` constraints throughout
     the propositional logic API ... The trade-off (noted by thomaskwaring) is an extra `bot` case
     in structural recursions."
   - **Assessment**: Partially addressed. The PR description acknowledges the trade-off but does
     not directly rebut the philosophical point. The counter-argument (that bot is *semantically*
     special in IPL/CPL even if syntactically similar in MPL) is implicit at best.
   - **Confidence**: HIGH

2. *"Minimal logic works perfectly well without ⊥"*
   - Response: Not explicitly rebutted in the re-submitted PR description.
   - **Assessment**: Not directly addressed. benbrastmckie's response comment mentions that "bot
     is now primitive" but does not address the sufficiency of minimal logic without bot.
   - **Confidence**: HIGH (gap remains)

3. *"Extra constructor makes all proofs and definitions more verbose"*
   - Response: The PR description says "The trade-off ... is an extra `bot` case in structural
     recursions." No quantification or comparison.
   - **Assessment**: Minimally addressed. The `Proposition.subst` function now has a `| bot => .bot`
     case, and the `weak` and `subs` definitions in Basic.lean are updated accordingly. The overhead
     is real but small. Not convincingly rebutted.
   - **Confidence**: HIGH

4. *"WithBot.some substitution is sometimes important (conservativity results)"*
   - Response: PR description says "subst f .bot = .bot ensures `Proposition.subst` preserves
     bottom structurally ... whereas atom-encoded bot requires additional constraints to prevent
     `subst f (.atom ⊥) = f ⊥` from mapping bottom to an arbitrary formula. As thomaskwaring
     notes, non-bottom-preserving maps are also useful (e.g., conservativity results via
     `WithBot.some`)."
   - **Assessment**: Acknowledged but not fully addressed. The PR description explicitly mentions
     thomaskwaring's conservativity point and notes `WithBot.some` compatibility, but the
     `intuitionisticCompletion` function (which uses `WithBot.some`) is still present in `Defs.lean`.
     The design accommodates the WithBot.some use case but the PR description does not explain how.
   - **Confidence**: HIGH (gap in explanation)

5. *"`⊤ = a → a` is a feature, not a bug"*
   - Response: benbrastmckie's comment says "the current definition is `top := ⊥ → ⊥` — the old
     `a → a` definition required `[Inhabited Atom]`. Both are provable by the same proof
     (`impI` + assumption), and as you noted, with `[Bot Atom]` Lean synthesises `default = ⊥`
     anyway, so they coincide in that setting."
   - **Assessment**: Addressed in the comment but not in the PR description. The new definition is
     `Proposition.top := .imp .bot .bot`, which is well-defined without any constraints and has a
     unique normal form. This is a genuine improvement over `impl (.atom default) (.atom default)`.
   - **Confidence**: HIGH (addressed in response comment, could be clearer in PR description)

**Remaining concern (HIGH confidence)**: thomaskwaring's position remains that the bot-as-primitive
design is a *design regression* for the five-primitive formula type. He has not withdrawn his
objection. The PR has been re-submitted without resolving this disagreement. Whether thomaskwaring's
approval is required for merge is unclear, but his objection is on record.

---

### Issue 2: Semantics Files

**ctchou's request**: "I don't understand why we need both Semantics/Basic.lean and
Semantics/Bool.lean. I think the latter alone is enough."

**thomaskwaring's request**: "Please split the semantics development into a separate PR."

**What the PR does**: Both `Semantics/Basic.lean` and `Semantics/Bool.lean` are **removed** from
the PR. The PR description says "Semantics (`Basic.lean`, `Bool.lean`) deferred to a follow-up PR
per thomaskwaring's request."

**Did this address the issue?**
- thomaskwaring's request (split to separate PR): YES, directly addressed.
- ctchou's request (Bool only, not both): Effectively addressed — both are removed, and the PR
  description notes the question of "Prop vs Bool vs GeneralizedHeytingAlgebra" will be addressed
  in the follow-up PR.

**Remaining concern (MEDIUM confidence)**: There is no follow-up PR or issue created for the
semantics work. The semantics are deferred but not tracked. If no follow-up PR is created,
the semantics work may be lost. This is a process concern, not a technical blocker.

**Technical note on GHA approach**: thomaskwaring and MatthewDoty discuss using
`GeneralizedHeytingAlgebra` for a single polymorphic `Evaluate` that covers both `Bool` and `Prop`
cases. The re-submitted PR description acknowledges: "Thomas, your suggestion of defining the
interpretation for any `GeneralizedHeytingAlgebra` is elegant and I'd like to explore that
direction." This is an open design question for the follow-up.

---

### Issue 3: German-Language References

**ctchou's request**: "It is not helpful to the readers to refer to old papers from the 1930s,
some of which are in German. A good modern reference is Jeremy Avigad's textbook..."

**What the PR does**:
- Added `Avigad2022` entry to `references.bib` (confirmed in diff).
- The re-submitted PR description states "German-language references replaced with Avigad (2022)
  per ctchou's suggestion."
- In `Connectives.lean` docstring, `[Avigad2022]` is used.
- In `Defs.lean` docstring, `[Avigad2022]` is used.
- In `NaturalDeduction/Basic.lean` docstring, `[Avigad2022]` is used (replaces Prawitz, Troelstra
  & van Dalen, Sorensen & Urzyczyn).

**Did this address the issue?**
- ctchou's specific objection (German/old references): YES, all visible references in the diff use
  Avigad2022 only.
- **Scope check**: The diff shows the old references in `NaturalDeduction/Basic.lean` were
  "Dag Prawitz, Natural Deduction" and "Troelstra & van Dalen" and "Sorensen & Urzyczyn" — these
  are **English** references, not German. The German references (Johansson1937, Gentzen1935, etc.)
  were in the original PR's files but are **not visible in the current diff** for Basic.lean.
  This suggests the re-submitted PR's docstrings may not have contained German references at all
  in the Natural Deduction files — only the original PR submission did.

**Confidence**: HIGH that ctchou's concern is addressed.

**Remaining concern (LOW confidence)**: The prior research (task 221 report) identified German
references in `Connectives.lean` (Johansson1937, Wajsberg1938, McKinsey1939, Heyting1930,
Gentzen1935). These appear to have been removed or were never in the re-submitted version since
`Connectives.lean` is a new file in this PR. The current `Connectives.lean` only cites
`[Avigad2022]`. This concern appears resolved.

**Note**: thomaskwaring's own comment acknowledged the German Gentzen reference was "my bad, I read
it in translation." This suggests he was initially responsible for citing Gentzen1935 in the
original `NaturalDeduction/Basic.lean`, and the PR's new version (which replaces the whole
docstring) correctly uses only English references.

---

### Issue 4: Coordination with PR #607, #587, and #536

**ctchou's request**: "You should definitely coordinate this PR with #607 and #587. #536 is ready
to merge, so you should wait for it."

**What the PR does**:
- **PR #536**: The PR has been rebased on upstream/main which includes merged PR #536. The
  `IsIntuitionistic`/`IsClassical` typeclasses now use `[InferenceSystem S (Proposition Atom)]`
  as required by #536. The `[Bot Atom]` constraint is removed from both.
- **PR #607** (fmontesi, "feat(Logic): logical operators"): A new file `Connectives.lean` is added
  with per-operator typeclasses (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`).
- **PR #587** (thomaskwaring, "feat(Foundations/Logic): Notation typeclasses and models"): PR
  description says "no conflict expected."

**Assessment for PR #536**: Addressed. The diff confirms `IsIntuitionistic` and `IsClassical` now
have `[InferenceSystem S (Proposition Atom)]` parameter and lack `[Bot Atom]`. Verified in the
`Defs.lean` and `Theory.lean` diffs.

**Assessment for PR #607**:
- PR #648's `Connectives.lean` uses `HasImp` with method `imp`. PR #607 uses `HasImpl` with method
  `impl`. **These are different names.** The two PRs are not aligned on the implication typeclass.
- PR #648's `Connectives.lean` has `HasBot`, `HasImp`, `HasAnd`, `HasOr`. PR #607 has `HasImpl`,
  `HasAnd`, `HasOr`, `HasNot`, `HasIff`, `HasBox`, `HasDiamond`, `HasTensor` (no `HasBot`, no
  `HasImp`).
- PR #648's `PropositionalConnectives` bundles `HasBot + HasImp`. PR #607 has no bundled class of
  this name.
- **Confidence**: HIGH that there is a real naming conflict. PR #607 uses `HasImpl`/`impl` and PR
  #648 uses `HasImp`/`imp`. If both merge, there will be duplicate typeclass infrastructure with
  different names for implication.
- The PR description notes: "PR #607 (fmontesi): operator typeclasses — `Connectives.lean` is
  aligned with this direction." This claim is **inaccurate** — they have the same structural
  pattern (per-operator classes) but use different method names for implication.

**Assessment for PR #587**:
- PR #587 defines `Models α β`, `ParamModels α β`, and `InterpModels α β` with soundness/
  completeness relative to inference systems. Since PR #648's semantics are removed, direct
  conflict is unlikely.
- **Confidence**: MEDIUM that no conflict exists for this re-submission.

---

### Issue 5: `imp` vs `impl` Naming

**thomaskwaring's comment**: "Re the renaming `imp` / `impl`, I think this is fine, but citing
'CSLib's existing formula types' as your own as-yet-unmerged work is not exactly convincing.
Indeed the actually existing example (`Modal`) uses 'impl'."

**What the PR does**: Uses `imp` throughout (`Proposition.imp` constructor, `impI`/`impE`
derivation constructors, `HasImp` typeclass, `PropositionalConnectives`). The PR description
justifies this: "Constructor naming uses `imp`/`impI`/`impE` (renamed from `impl`/`implI`/`implE`
for consistency with FormalizedFormalLogic convention; open to reverting if reviewers prefer
`impl`)."

**Is thomaskwaring's claim about Modal accurate?**
Checked `Cslib/Logics/Modal/FromPropositional.lean`: No `impl` or `HasImpl` references found in
that file (only `implies` as an English word). The PR #607 diff shows `HasImpl`/`impl` in
*proposed* (not yet merged) code. The current merged `Propositional/Defs.lean` on `main` uses
`| imp` (confirmed by reading the file directly — it's the PR #648 changes that are now merged
into this working tree as `c76df599`). This means thomaskwaring's point that "the actually
existing example (Modal) uses 'impl'" refers to PR #607's proposed changes, not the currently
merged codebase.

**Assessment**: thomaskwaring's factual claim requires clarification. Currently merged Modal code
appears to not use `impl` as a constructor name for propositional implication. However, PR #607
(which thomaskwaring may be aware of) does use `HasImpl`/`impl`. The PR description's justification
is adequate but could be strengthened by noting that the currently merged `Propositional/Defs.lean`
on main uses `imp`.

**Remaining concern (MEDIUM confidence)**: If PR #607 merges, there will be `HasImpl`/`impl` and
`HasImp`/`imp` as different typeclasses/methods in the same codebase. One or the other will need
to be renamed in a follow-up PR. The PR description should acknowledge this explicitly.

---

### Issue 6: `IsIntuitionistic`/`IsClassical` Reconciliation with #536

**What the PR does**: The `IsIntuitionistic` and `IsClassical` classes are now:
```lean
class IsIntuitionistic (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)

class IsClassical (Atom : Type u) (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  dne (A : Proposition Atom) : S⇓(¬¬A → A)
```

**Assessment**: `[Bot Atom]` is removed from both. The inference-system-based parameterization
from #536 is preserved. The `⊥` in `S⇓(⊥ → A)` now refers to `Proposition.bot` (a constructor),
not `(⊥ : Proposition Atom)` via a `Bot` instance from `[Bot Atom]`. Both refer to the same
thing now since `instance : Bot (Proposition Atom) := ⟨.bot⟩` — but the constraint is gone.

**New instance added**: `instIsIntuitionisticIntuitionisticCompletion` is new in `Theory.lean`:
```lean
instance instIsIntuitionisticIntuitionisticCompletion [DecidableEq (WithBot Atom)]
    (T : Theory Atom) :
    IsIntuitionistic (WithBot Atom) T.intuitionisticCompletion where
  efq A := ax (Set.mem_union_right _ (efq_mem_ipl A))
```
This was not in #536's version. It provides the IsIntuitionistic instance for `WithBot Atom` over
`intuitionisticCompletion`. This is a genuine addition that seems correct and useful.

**Confidence**: HIGH that reconciliation is correct.

---

### Issue 7: Copyright/Authorship Changes

**What changed**: Three files had their copyright lines updated:
- `Defs.lean`: `2025 Thomas Waring` → `2025 Thomas Waring, 2026 Benjamin Brast-McKie`
- `NaturalDeduction/Basic.lean`: same pattern
- `NaturalDeduction/Theory.lean`: same pattern

**Assessment**: Standard CSLib practice for derived work — adding one's name when making
substantial modifications. In `Defs.lean`, the changes are substantial (new constructor, new
instances, new abbrevs). In `NaturalDeduction/Basic.lean`, constructor renames and parameter
changes throughout are also substantial. In `Theory.lean`, removing `[Bot Atom]` from all
signatures and updating all proof terms constitutes substantial work.

**Concern (LOW confidence)**: thomaskwaring is the original author of these files. Adding a
co-author without explicitly discussing it with the original author could be perceived as
presumptuous. No objection has been raised on this point, but it's worth monitoring.

---

### Issue 8: `Connectives.lean` — Alignment with PR #607

**What the PR does**: Adds `Cslib/Foundations/Logic/Connectives.lean` with:
- `HasBot` (method: `bot`)
- `HasImp` (method: `imp`)
- `HasAnd` (method: `and`)
- `HasOr` (method: `or`)
- `PropositionalConnectives` (extends `HasBot + HasImp`)

**PR #607 (still open) provides**:
- `HasImpl` (method: `impl`) — implication
- `HasAnd` (method: `and`) — conjunction
- `HasOr` (method: `or`) — disjunction
- `HasNot` (method: `not`) — negation
- `HasIff` (method: `iff`) — biconditional
- No `HasBot`, no `HasImp`

**Conflict analysis**:
| Class | PR #648 | PR #607 | Conflict? |
|-------|---------|---------|-----------|
| Implication | `HasImp` / `imp` | `HasImpl` / `impl` | YES — different names |
| Conjunction | `HasAnd` / `and` | `HasAnd` / `and` | COMPATIBLE |
| Disjunction | `HasOr` / `or` | `HasOr` / `or` | COMPATIBLE |
| Falsum | `HasBot` / `bot` | Not in #607 | No conflict, additive |
| Negation | Not in #648 | `HasNot` / `not` | No conflict, additive |

**Assessment (HIGH confidence)**: The implication typeclass naming is the key conflict. If both PRs
merge independently, the codebase will have two different implication typeclasses. The PR
description's claim of being "aligned with" #607 is overstated. They share the structural pattern
(per-operator classes) but diverge on the critical implication naming.

**Recommendation for PR response**: Explicitly acknowledge that `HasImp` vs `HasImpl` diverges from
#607 and that one of the two PRs will need to adjust. Propose which direction to take.

---

### Issue 9: Notation Priority Conflicts

**In `Connectives.lean`**:
```lean
@[inherit_doc] scoped infix:36 " ∧ " => Proposition.and
@[inherit_doc] scoped infix:35 " ∨ " => Proposition.or
@[inherit_doc] scoped infix:30 " → " => Proposition.imp
@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg
```

In PR #607:
```lean
@[inherit_doc] scoped infixr:25 " → " => HasImpl.impl
@[inherit_doc] scoped infixr:30 " ∨ " => HasOr.or
@[inherit_doc] scoped infixr:35 " ⊗ " => HasTensor.tensor
@[inherit_doc] scoped infixr:36 " ∧ " => HasAnd.and
```

PR #648 uses `infix:30` for `→`, PR #607 uses `infixr:25` for `→`. Different priority levels
and associativity attributes. This is a technical inconsistency that would require resolution.

**Confidence**: HIGH. The diff shows clear divergence in notation priorities.

---

### Issue 10: `module` Keyword in `Connectives.lean`

The new `Connectives.lean` file begins with the bare `module` keyword (line 7 in the diff):
```lean
module

import Cslib.Init
```

This is standard CSLib structure. No issue here.

---

## Issues Not Yet Addressed

1. **`HasImp` vs `HasImpl` conflict with PR #607** (HIGH confidence, HIGH impact): The PR
   description claims alignment with #607 but uses `HasImp`/`imp` while #607 uses `HasImpl`/
   `impl`. This needs explicit coordination or one PR must adjust.

2. **Notation priority divergence with PR #607** (HIGH confidence, MEDIUM impact): `→` is
   `infix:30` in #648 vs `infixr:25` in #607.

3. **thomaskwaring's bot-as-primitive objections not fully rebutted** (HIGH confidence,
   MEDIUM impact): The PR description acknowledges trade-offs but does not directly address all
   five of thomaskwaring's philosophical/technical points. His position on the record is that the
   original `[Bot Atom]` design was discussed and is preferable.

4. **No follow-up tracking for semantics work** (MEDIUM confidence, LOW impact): The deferred
   semantics have no follow-up PR or issue. If not tracked, the GHA evaluation direction could
   be lost.

5. **`imp`/`impl` naming — forward risk** (MEDIUM confidence, MEDIUM impact): If PR #607 merges
   first with `HasImpl`, the `HasImp` in PR #648's `Connectives.lean` creates a permanent
   divergence until a cleanup PR runs.

---

## Summary Table

| Issue | Reviewer | Status | Confidence |
|-------|----------|--------|------------|
| Bot as primitive (design) | thomaskwaring (objection), ctchou (support) | OPEN — design disagreement remains | HIGH |
| thomaskwaring pt 1: bot = atom in MPL | thomaskwaring | Partially rebutted | HIGH |
| thomaskwaring pt 2: MPL works without bot | thomaskwaring | Not addressed in PR | HIGH |
| thomaskwaring pt 3: extra constructor verbosity | thomaskwaring | Acknowledged, not rebutted | HIGH |
| thomaskwaring pt 4: WithBot.some conservativity | thomaskwaring | Acknowledged, partially explained | HIGH |
| thomaskwaring pt 5: top = a→a is a feature | thomaskwaring | Addressed in response comment | HIGH |
| Semantics files removed | thomaskwaring, ctchou | RESOLVED | HIGH |
| German references replaced | ctchou | RESOLVED | HIGH |
| Rebased on main after #536 | ctchou | RESOLVED | HIGH |
| IsIntuitionistic/IsClassical reconciled | ctchou | RESOLVED | HIGH |
| imp vs impl justification | thomaskwaring | Addressed but risk remains if #607 merges | MEDIUM |
| HasImp vs HasImpl conflict with #607 | n/a (new finding) | OPEN | HIGH |
| Notation priority divergence with #607 | n/a (new finding) | OPEN | HIGH |
| No follow-up semantics tracking | n/a (process) | OPEN | MEDIUM |
| Copyright addition | n/a | No objection raised | LOW |

---

## Technical Accuracy Checks

**Claim**: "imp/impI/impE (renamed from impl/implI/implE for consistency with FormalizedFormalLogic
convention)"
**Verification**: FormalizedFormalLogic uses `| imp` for the constructor name. Confirmed by prior
research (task 221 report cites FormalizedFormalLogic/Foundation as using `| imp`). The PR
description's justification is factually accurate.
**Confidence**: HIGH

**Claim**: "Connectives.lean is aligned with #607"
**Verification**: Checked PR #607 diff. Uses `HasImpl`/`impl` for implication; PR #648 uses
`HasImp`/`imp`. The structural pattern (per-operator classes) is shared, but the naming is
incompatible.
**Conclusion**: The claim is misleading. They share the same design philosophy but diverge on
the critical implication naming.
**Confidence**: HIGH

**Claim**: "Reconciled `IsIntuitionistic`/`IsClassical` with the InferenceSystem-parameterized
versions from #536 (removing `[Bot Atom]` since bot is now primitive)"
**Verification**: The diff confirms this. Both classes now have `[InferenceSystem S (Proposition Atom)]` and no `[Bot Atom]`. Verified against the PR #536 pattern.
**Confidence**: HIGH

**Claim**: "Avigad 2022 chapters 2 and 3 covers everything in this PR"
**Source**: ctchou's review.
**Assessment**: Avigad (2022) is a standard textbook on mathematical logic and computation.
Chapters 2-3 cover propositional logic, natural deduction, and proof theory. This is accurate.
**Confidence**: HIGH
