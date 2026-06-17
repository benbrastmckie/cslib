# Critic Research: Task 220 – PR #649 Refactor (Typeclass Split + LTL Formula)

**Role**: Critic (Teammate C)
**Focus**: Gaps, risks, and blind spots in the proposed refactor

---

## Key Findings

### Finding 1: The Hierarchy Diamond Risk Is REAL and Carefully Avoided on the Current Branch — Do Not Reintroduce It

**Confidence: HIGH**

The current `main` branch `Connectives.lean` (line 130) explicitly comments:
```lean
/-- Bimodal connectives: modal connectives plus until and since.
    Note: we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly
    rather than extending `TemporalConnectives`, to avoid a typeclass diamond. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

The diamond was already avoided by having `BimodalConnectives` NOT extend `TemporalConnectives`. If the refactor introduces `FutureTemporalConnectives` and then makes `TemporalConnectives extends FutureTemporalConnectives, HasSince`, and `BimodalConnectives extends ModalConnectives, HasUntil, HasSince` (no path through `TemporalConnectives`), the diamond avoidance is preserved. But if anyone writes:
```lean
class BimodalConnectives extends ModalConnectives F, TemporalConnectives F
```
the diamond returns because `TemporalConnectives extends PropositionalConnectives` AND `ModalConnectives extends PropositionalConnectives`.

**Risk**: The PR task description says to insert `FutureTemporalConnectives` between `PropositionalConnectives` and `TemporalConnectives`. If `BimodalConnectives` continues to avoid extending `TemporalConnectives`, that's fine. But the plan must be explicit about this — any draft that shows `BimodalConnectives extends FutureTemporalConnectives` or `TemporalConnectives` would be wrong.

---

### Finding 2: The PR 649 Branch Has a DIFFERENT Connectives.lean Than main — No `HasBox`, No `ModalConnectives`, No `BimodalConnectives`

**Confidence: HIGH (verified by `git show remotes/origin/feat/temporal-formula-propositional:Cslib/Foundations/Logic/Connectives.lean`)**

The PR branch's `Connectives.lean` is a **stripped-down version** that only defines:
- `HasBot`, `HasImp`, `HasUntil`, `HasSince`, `HasAnd`, `HasOr`
- `PropositionalConnectives` (extends `HasBot`, `HasImp`)
- `TemporalConnectives` (extends `PropositionalConnectives`, `HasUntil`, `HasSince`)

It does **NOT** include `HasBox`, `ModalConnectives`, `BimodalConnectives`. This means:
1. The PR branch diverged from main significantly. Any follow-up commit must target the PR branch state, not main.
2. There is no diamond risk on the PR branch because there is no `ModalConnectives` or `BimodalConnectives` in scope.
3. Adding `FutureTemporalConnectives` on the PR branch is straightforward — just insert it between `PropositionalConnectives` and `TemporalConnectives`.

---

### Finding 3: The `next` Operator Semantic Gap Is Real But Actually an Argument FOR Primitive `next` in LTL

**Confidence: HIGH**

The existing `Temporal.Formula.next` is defined as:
```lean
-- Cslib/Logics/Temporal/Syntax/Formula.lean:413
def next (φ : Formula Atom) : Formula Atom := .untl φ .bot
```
The `complexity` function (line 372) also pattern-matches on `.untl φ .bot` and calls it "next(φ) = φ U ⊥ in Burgess: guard ⊥ impossible, forces immediate step."

Semantically: `φ U ⊥` at time `t` means "∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ⊥(r)". The condition `∀ r ∈ (t,s), ⊥(r)` is vacuously true iff `(t,s)` is empty, i.e., `s = t+1` in a **discrete** model. In a **dense** model (like ℚ or ℝ), there is always a point between `t` and `s`, so the guard `⊥` fails and `φ U ⊥` is ALWAYS FALSE.

This is precisely why LTL requires `next` as a **primitive** — it's only well-defined on omega-words (discrete time). Making `LTL.Formula.next` a constructor (not derived from `untl`) is therefore semantically correct and not a semantic gap.

**Risk to address in commit**: The commit should document this clearly in the docstring for `HasNext`, explaining why `next` must be primitive for omega-word semantics rather than derived from `untl`.

---

### Finding 4: Breaking Changes Are Contained to the PR Branch, Not main

**Confidence: HIGH**

On the **main branch**, `TemporalConnectives` is used in only 2 files:
1. `Cslib/Foundations/Logic/Connectives.lean` (definition)
2. `Cslib/Logics/Temporal/Syntax/Formula.lean` (single instance registration at line 139)

`HasUntil` and `HasSince` are used in:
1. `Cslib/Foundations/Logic/Axioms.lean` (variable declarations: `[HasUntil F] [HasSince F]`)
2. `Cslib/Foundations/Logic/Connectives.lean` (definitions)
3. `Cslib/Foundations/Logic/ProofSystem.lean` (`TemporalBXHilbert` and `TemporalNecessitation` use both)
4. `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` (variable: `[HasUntil F] [HasSince F]`)

**On the PR branch**, since the Connectives.lean is already simplified and the other Foundations files (`Axioms.lean`, `ProofSystem.lean`) are not in the PR diff (they were removed), breaking changes are scoped to the PR branch delta. However, the `TemporalDerived.lean` on main uses `[HasUntil F] [HasSince F]` as separate constraints, NOT `[TemporalConnectives F]`, so changing `TemporalConnectives` does not break those files.

The `ProofSystem.lean` `TemporalBXHilbert` on main (line 427) uses `[HasUntil F] [HasSince F]` directly, also safe.

---

### Finding 5: LTL.Formula as a NEW File Requires `lake exe mk_all` — Scope Risk

**Confidence: HIGH**

Creating `Cslib/Logics/LTL/Syntax/Formula.lean` as a new file triggers the CSLib requirement to:
1. Run `lake exe mk_all --module` to update `Cslib.lean` barrel import
2. Add the new directory to the `Cslib.lean` include tree

No existing LTL directory exists. This is NOT a blocker, but it is additional CI work. The task description mentions "Add basic LTL satisfaction over omega-words" — this is a significant scope expansion. Adding satisfaction semantics over omega-words is NOT a minimal change to address reviewer feedback. It creates a risk of:
- Proof obligations that can't be discharged without `sorry`
- Scope creep delaying the PR merge
- Additional reviewer feedback surface area

**Recommendation**: The safe minimum is `LTL.Formula` type + `toTemporal` embedding + no semantics. Semantics can be a separate PR.

---

### Finding 6: The Existing `Temporal.Formula.next` Definition MUST NOT Be Changed

**Confidence: HIGH**

The existing `next` definition at line 413 of `Temporal/Syntax/Formula.lean` is referenced by:
- `complexity` function (line 372: pattern match on `.untl φ .bot`)
- `swapTemporal_next` theorem (line 529)
- `swapTemporal_prev` theorem (line 533)
- `Formula.prev` definition (line 416)

If the refactor changes the temporal formula's `next` to use a `HasNext` typeclass constructor, these would break. The correct approach is:
- Keep `Temporal.Formula.next` as `def next φ := .untl φ .bot` (derived)
- Make `LTL.Formula.next` a **primitive constructor** (separate inductive)
- These are independent types in independent namespaces

---

### Finding 7: The Burgess Convention Creates a Notation Asymmetry Risk for LTL.Formula

**Confidence: MEDIUM**

The existing temporal logic uses Burgess convention: `untl event guard` (first arg = event, second = guard). Standard LTL in the literature (Pnueli 1977, Vardi & Wolper 1986) uses `φ U ψ` where ψ is the EVENTUAL truth (the "event" in Burgess). This means CSLib's `untl` argument order is REVERSED compared to standard LTL notation.

If `LTL.Formula` also uses Burgess convention for `untl`, the embedding `LTL.Formula.toTemporal` is straightforward (constructor-to-constructor). But the docstrings will be confusing because standard LTL papers write `φ U ψ` meaning "ψ eventually holds" while CSLib's internal convention treats the first arg as the event.

**Risk**: Reviewers unfamiliar with Burgess will be confused about argument order. The commit must include clear notation documentation.

---

### Finding 8: What ctchou and Matthew Actually Requested May Not Match the Plan

**Confidence: MEDIUM** (based on task description, no direct PR comment access)

The task description says ctchou requested "future-only, LTS integration, remove irrelevant instances." The proposed plan addresses:
- future-only: `FutureTemporalConnectives` with `HasUntil`
- remove irrelevant instances: remove `Encodable/Countable/Infinite/Denumerable/BEq`

But "LTS integration" is NOT addressed in the proposed refactor. If ctchou wants the LTL formula type to connect to the existing LTS typeclass infrastructure (in `Cslib/Foundations/LTS/`), this is missing from the plan.

**Unvalidated assumptions**:
1. Does ctchou want `snce` (Since) removed from `TemporalConnectives` entirely, or just from the new LTL fragment? The task plan retains `TemporalConnectives extends FutureTemporalConnectives, HasSince` — ctchou may want `HasSince` removed from the PR entirely.
2. Does Matthew's comment about "class-based MCS/deduction abstraction" apply to THIS PR or only to a future completeness PR? Including any MCS/deduction abstractions in this PR would be scope creep.

---

### Finding 9: Removing BEq Instances Is a Backward-Incompatible Change on the PR Branch

**Confidence: HIGH**

The PR branch's `Formula.lean` (confirmed matching main) has:
```lean
deriving DecidableEq, BEq
```
at line 86. The `BEq`/`LawfulBEq` instances proven manually (lines 267-332) exist in the PR branch. 

Removing these breaks any downstream code that uses `BEq` on `Temporal.Formula`. On the CSLib main branch, the decidability infrastructure (in `Temporal.Metalogic.Decidability.*`) uses `DecidableEq` extensively. If `BEq` is only removed from the PR's temporal formula without affecting the main branch (which retains it), the PR would be narrowing its scope rather than breaking main.

**BUT**: If ctchou wants these removed from the PR scope entirely, it's not a breaking change to main — it just means the PR is smaller. The risk is whether the `DecidableEq` (from `deriving DecidableEq`) can remain while `BEq` instances are manually removed.

---

### Finding 10: There Is No Existing LTL Directory — New Module Requires Namespace Registration

**Confidence: HIGH (verified by `find`)**

The `Cslib/Logics/` directory contains: Bimodal, HML, LinearLogic, Modal, Propositional, Temporal. There is NO `LTL` directory. Creating one requires:
1. Creating `Cslib/Logics/LTL/` directory structure
2. Adding LTL to `Cslib.lean` barrel via `lake exe mk_all --module`
3. The new file must have `import Cslib.Init` per `checkInitImports`
4. All new declarations need docstrings (docBlame lint)

---

## Recommended Approach

### Minimum-Viable Commit to Address Reviewer Feedback

The minimum change that satisfies ctchou and avoids scope expansion:

1. **In `Connectives.lean`**: Add `FutureTemporalConnectives extends PropositionalConnectives F, HasUntil F`. Change `TemporalConnectives` to `extends FutureTemporalConnectives F, HasSince F`. Keep `BimodalConnectives` unchanged (still avoids diamond).

2. **Add `HasNext` typeclass**: Add `class HasNext (F : Type*) where next : F → F` to `Connectives.lean`. Add `LTLConnectives extends FutureTemporalConnectives F, HasNext F`.

3. **Create `LTL/Syntax/Formula.lean`**: Inductive `{atom, bot, imp, next, untl}` with `next` as PRIMITIVE constructor. Register `LTLConnectives` instance. Provide `toTemporal : LTL.Formula → Temporal.Formula` embedding.

4. **Remove/defer**: Keep `TemporalConnectives` unchanged in its semantic role; do NOT add omega-word satisfaction semantics to this PR.

### Risks to Flag to User Before Proceeding

1. **LTS integration not addressed**: Confirm with user if ctchou specifically needs LTS integration in this PR or a future one.
2. **Satisfaction semantics**: Confirm whether adding LTL satisfaction over omega-words is in scope. If so, plan must account for substantial additional proof work.
3. **BimodalConnectives diamond avoidance**: Any draft `Connectives.lean` must be reviewed to ensure `BimodalConnectives` still avoids the diamond. The comment should be preserved or updated.
4. **snce scope**: Confirm whether `HasSince` should be removed from the PR branch's `TemporalConnectives` entirely, or retained in the bundled class.

---

## Evidence and Examples

### Diamond Avoidance Comment (main branch, `Connectives.lean` line 127-130)
```lean
/-- Bimodal connectives: modal connectives plus until and since.
    Note: we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly
    rather than extending `TemporalConnectives`, to avoid a typeclass diamond. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

### PR Branch Connectives.lean Lacks Box/Modal/Bimodal
The PR branch `Connectives.lean` ends at `TemporalConnectives` — no `HasBox`, `ModalConnectives`, or `BimodalConnectives` are present. This makes the PR branch hierarchy simpler and the diamond risk a non-issue for the PR's scope.

### `next` as Derived on Main Branch (Formula.lean:413)
```lean
def next (φ : Formula Atom) : Formula Atom := .untl φ .bot
```
Used in `complexity` pattern matching (lines 371-373) and `swapTemporal_next` theorem.

### ProofSystem.lean Uses `[HasUntil F] [HasSince F]` Directly (not `TemporalConnectives`)
`TemporalBXHilbert` (line 427) takes `[HasUntil F] [HasSince F]` as separate constraints. Changing `TemporalConnectives` does not affect this.

### No LTL Directory in Logics
```
Cslib/Logics/: Bimodal, HML, LinearLogic, Modal, Propositional, Temporal
```
No LTL directory exists; creating it is new infrastructure.

---

## Summary

The proposed refactor is structurally sound in principle but has three concrete risks:

1. **Diamond avoidance must be explicitly preserved** in any new `Connectives.lean` — the comment about why `BimodalConnectives` doesn't extend `TemporalConnectives` must carry through (though on the PR branch, BimodalConnectives isn't even present, so this is only a risk if the PR is rebased onto main or if the new structure is later merged with main).

2. **Scope creep from omega-word satisfaction semantics** — this should be deferred to a separate PR. The minimum viable change is typeclass splits + `LTL.Formula` type + `toTemporal` embedding only.

3. **Unvalidated reviewer intent** — whether ctchou wants `HasSince` removed from `TemporalConnectives` entirely (making it future-only) vs. retaining it in a renamed class is ambiguous from the task description alone. The difference matters for the commit structure.

The semantic point about `next` being primitive in LTL (because `φ U ⊥` is always false in dense models) is actually a STRENGTH of the plan, not a weakness. It should be documented explicitly in the commit.
