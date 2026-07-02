---
task: 472
title: Restore model-class-parametric Proposition.Equiv and LogicalEquivalence framework integration (PR #662)
type: cslib
status: researched
date: 2026-07-02
session: sess_1783022251_1a3cf2
agent: cslib-research-agent
pr: leanprover/cslib#662
---

# Research: Restore model-class-parametric `Proposition.Equiv` + `LogicalEquivalence` framework (PR #662)

## Summary

PR #662 (`feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`,
branch `feat/modal-formula-primitives`, **OPEN**, base `main`, 0 reviews/comments as of
2026-07-02) refactors the Modal formula type and, as a side effect in
`Cslib/Logics/Modal/LogicalEquivalence.lean`, **replaces Fabrizio Montesi's
model-class-parametric `Proposition.Equiv (S : Set (Model World Atom))` and its integration
with the shared `Cslib.Logic.LogicalEquivalence` framework by a standalone
`LogicallyEquivalent` definition** that is hardwired to all models and drops every framework
instance.

The current `main` working tree already contains the standalone replacement (it was landed
via task 137 phase 5, commit `a084f9f2` "write LogicalEquivalence.lean for fork primitives";
the PR diff's `-` side is Montesi's original pre-fork version). So this is a genuine, already-
merged-into-local-`main` divergence, not a hypothetical.

**Recommendation: Option A (restore), in hybrid form.** Keep PR #662's primitive refactor and
its new `{hole, impL, impR, box}` `Proposition.Context`, but re-add the model-class-parametric
`Proposition.Equiv S`, its notation and lemmas, the `IsEquiv` / `Congruence` instances, the
`Satisfies.Context` / `HasHContext` judgemental context, and the `LogicalEquivalence` framework
instance. This restores reuse of the Foundations abstraction (still used by HML and CLL),
removes an inconsistency with `Proposition.valid` (which *is* model-class-parametric), and is
low-to-moderate effort because the removed code is fully recoverable from the PR diff and the
congruence proof content already exists in the standalone version.

## Reuse Check Protocol Results

- **Foundations abstraction exists and is alive.** `Cslib/Foundations/Logic/LogicalEquivalence.lean:20`
  defines `class LogicalEquivalence (Proposition) [HasContext] (Judgement) [HasHContext] (Valid)`
  with `eqv`, a `[congruence : Congruence …]` field, and `eqvFillValid`. Scoped notation
  `≡` (`infix:29`) at line 33.
- **Two live instances remain** (confirmed via `git grep`):
  - `Cslib/Logics/HML/LogicalEquivalence.lean:105` — `instance : LogicalEquivalence (Proposition Label) (Satisfies.Judgement …) (Satisfies.Bundled)`.
  - `Cslib/Logics/LinearLogic/CLL/Basic.lean:653` — `noncomputable instance : LogicalEquivalence (Proposition Atom) (Sequent Atom) Proof`.
  - Modal *used to be* the third instance; PR #662 removed it.
- **Supporting typeclasses** (`Cslib/Foundations/Syntax/`):
  - `HasHContext (α β)` / `HasContext α := HasHContext α α` with fill notation `c<[t]` — `Context.lean:18,24,28`.
  - `class Congruence (α) [HasContext α] (r) extends IsEquiv α r, CovariantClass (Context α) α (·<[·]) r` — `Congruence.lean:19`.
- **Reuse verdict:** the standalone `LogicallyEquivalent` **duplicates the *purpose* of the
  Foundations framework while bypassing it**, so it violates CSLib's reuse-first philosophy. The
  parametric approach is the reuse-consistent one.

## What PR #662 Changed in `Modal/LogicalEquivalence.lean`

Diff hunk `@@ -1,132 +1,83 @@` (file `Cslib/Logics/Modal/LogicalEquivalence.lean`).

### Removed (the model-class-parametric + framework-integrated design, Montesi)

| Removed declaration | Purpose |
|---|---|
| `def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂) : Prop := ∀ m ∈ S, ∀ w, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]` | Equivalence **relative to a model class `S`** |
| `scoped notation φ₁ " ≡[" S "] " φ₂` and `φ₁ " ≡ " φ₂` (= `Equiv Set.univ`) | Class-indexed + K notation |
| `Proposition.equiv_def`, `equiv_iff` (`@[scoped grind =]`) | Unfolding / iff-splitting lemmas |
| `Proposition.equiv_valid (S) (h) : φ₁.valid S ↔ φ₂.valid S` | **Bridge from equivalence to `Proposition.valid S`** |
| `instance : IsEquiv (Proposition Atom) (Proposition.Equiv S)` | equivalence relation (reflexive/symm/trans; enables rewriting) |
| `instance : Congruence (Proposition Atom) (Proposition.Equiv S)` | congruence via the framework typeclass |
| `structure Satisfies.Context` + `Satisfies.Context.fill` + `instance judgementalContext : HasHContext (Judgement …) (Proposition …)` | judgemental (heterogeneous) contexts |
| `instance : LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled` (Modal Logic K) | **framework instance** wiring `eqv`, congruence, `eqvFillValid` |
| `Proposition.Context` constructors `{hole, not, andL, andR, diamond}` | one-hole context over **old** primitives |

### Added (the standalone replacement, current `main`)

`Cslib/Logics/Modal/LogicalEquivalence.lean` (current):
- `Proposition.Context` with new constructors `{hole, impL, impR, box}` (lines 39–47) — correct
  for the new `{atom, bot, imp, box}` primitives.
- `Proposition.Context.fill` (lines 50–54) — matches new constructors.
- `def LogicallyEquivalent.{v} {Atom} (φ ψ) : Prop := ∀ (World : Type v) (m : Model World Atom) (w), Satisfies m w φ ↔ Satisfies m w ψ` (lines 58–59).
- `theorem LogicallyEquivalent.congruence (c : Context) (h) : LogicallyEquivalent (c.fill φ) (c.fill ψ)` (lines 63–81) — a **plain theorem**, not a `Congruence` instance.
- **No** `IsEquiv`, **no** `Congruence` instance, **no** `HasContext`/`HasHContext` instances,
  **no** `Satisfies.Context`, **no** `LogicalEquivalence` instance, **no** notation, **no** `equiv_valid` bridge.

## How the Two Designs Diverge (Lean-level)

1. **Model-class parametricity (the headline loss).**
   - Old: `Proposition.Equiv (S : Set (Model World Atom))` — equivalence *within an arbitrary
     model class* `S`, with `≡[S]` and `≡ := ≡[Set.univ]`.
   - New: `LogicallyEquivalent` is fixed to *all* models. There is **no way to state**
     "`φ ≡ ψ` over reflexive frames" (T), symmetric (B), transitive (4), Euclidean (5), or
     S4/S5 — e.g. the S5 equivalence `◇□φ ≡ □φ` is inexpressible.
   - This is **inconsistent with `Proposition.valid`**, which *is* parametric:
     `Cslib/Logics/Modal/Basic.lean:443` — `def Proposition.valid (S : Set (Model World Atom)) (φ) := ∀ m ∈ S, ∀ w, ⇓Modal[m,w ⊨ φ]`, and `Cslib/Logics/Modal/Cube.lean` defines K/T/B/4/5/D as model classes and reasons about `Proposition.valid`/`logic S`. The removed `equiv_valid` was exactly the bridge `φ₁ ≡[S] φ₂ → (φ₁.valid S ↔ φ₂.valid S)`; the standalone version severs it.

2. **Universe quantification over `World` (a semantic change, not just a loss).**
   The standalone `LogicallyEquivalent.{v}` quantifies **inside** the definition over
   `(World : Type v)`. Montesi's `Proposition.Equiv S` fixed `World` (the ambient section
   variable) and quantified only over `m ∈ S` and `w`. These are *different relations*: the new
   one asserts agreement across all world-types at a single fixed universe `v` (an unusual
   framing that also pins a universe parameter onto every downstream use), whereas the old one is
   the standard "agreement across a model class over a given frame carrier".

3. **Framework integration / rewriting ergonomics.**
   - Losing `IsEquiv` means `≡` is no longer registered as an equivalence relation, so
     `calc`/`Trans`/setoid-style rewriting over equivalence is unavailable.
   - Losing the `Congruence` *instance* (kept only as a bare theorem) means the congruence fact
     is not discoverable through the `Congruence`/`CovariantClass` typeclass that HML and the
     Foundations layer rely on.
   - Losing the `LogicalEquivalence` instance means Modal no longer participates in any generic
     lemma written against the framework (validity-preservation under judgemental contexts via
     `eqvFillValid`).

4. **What the standalone got right (and must be preserved).** The `Proposition.Context`
   constructors `{hole, impL, impR, box}` and `fill` are the correct adaptation to the new
   primitives. Montesi's old `{not, andL, andR, diamond}` context matched the *old* primitives
   and cannot be restored verbatim — so the restoration is a **hybrid**, not a revert.

## Option Evaluation

### Option A — Restore parametric `Proposition.Equiv` + framework integration (RECOMMENDED)

**API to add** (all in `Cslib/Logics/Modal/LogicalEquivalence.lean`, `namespace Cslib.Logic.Modal`, adapting the diff `-` side to the new primitives; keep the existing `Proposition.Context`/`fill`):

```lean
public import Cslib.Foundations.Logic.LogicalEquivalence   -- re-add (removed by #662)

/-- `φ₁` and `φ₂` are equivalent in the class of models `S`. -/
def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) : Prop :=
  ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]

@[inherit_doc] scoped notation φ₁ " ≡[" S "] " φ₂ => Proposition.Equiv S φ₁ φ₂
@[inherit_doc] scoped notation φ₁ " ≡ " φ₂ => Proposition.Equiv Set.univ φ₁ φ₂

@[scoped grind =] theorem Proposition.equiv_def   … := by rfl
@[scoped grind =] theorem Proposition.equiv_iff   … := by simp [Proposition.equiv_def, Satisfies.iff_iff_iff]
theorem Proposition.equiv_valid (S) (φ₁ φ₂) (h : φ₁ ≡[S] φ₂) : φ₁.valid S ↔ φ₂.valid S := by grind

instance : HasContext (Proposition Atom) := ⟨Proposition.Context Atom, Proposition.Context.fill⟩

instance (S : Set (Model World Atom)) : IsEquiv (Proposition Atom) (Proposition.Equiv S) := by
  rw [← equivalence_iff_isEquiv]; grind [Equivalence]

instance (S : Set (Model World Atom)) : Congruence (Proposition Atom) (Proposition.Equiv S) where
  elim ctx φ₁ φ₂ heqv m hₘ w := by
    induction ctx generalizing w
    case hole => grind
    case impL c ih | impR c ih => specialize ih w; grind          -- new primitives
    case box c ih =>                                              -- was `diamond`; now `box`
      rw [Satisfies.iff_iff_iff]; …                                -- use Satisfies.box_iff_forall

structure Satisfies.Context (World Atom : Type*) where
  m : Model World Atom
  w : World
def Satisfies.Context.fill (c) (φ) : Judgement World Atom := Modal[c.m, c.w ⊨ φ]
instance judgementalContext : HasHContext (Judgement World Atom) (Proposition Atom) := ⟨…⟩

instance : LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled where
  eqv := Proposition.Equiv Set.univ
  eqvFillValid heqv c h := by specialize heqv c.m; grind
```

- **Proofs that change vs. the diff `-` side:** only the `Congruence.elim` induction cases,
  because the context constructors changed from `{not, andL, andR, diamond}` to
  `{impL, impR, box}`. The **proof content already exists** in the current standalone
  `LogicallyEquivalent.congruence` (lines 63–81): `impL`/`impR` are handled by `Satisfies` +
  the IH; `box` uses `Satisfies.box_iff_forall` (`Basic.lean:116`) / `Satisfies.iff_iff_iff`.
  It just needs re-expression under the `Congruence.elim` / `CovariantClass` shape.
- **`Satisfies.Bundled`** already exists (`Basic.lean:205`); `Judgement`/`Modal[…]` notation and
  `⇓` derivation notation (`HasInferenceSystem`, `Basic.lean:209`) are unchanged, so the
  judgemental-context and framework instance restore cleanly.
- **`equivalence_iff_isEquiv`** is the Mathlib lemma the original proof used (`rw [← equivalence_iff_isEquiv]`); it compiled at the fork point, so it is available. Verify with `lean_local_search`/`lean_hover_info` at implementation time.
- **Effort:** moderate (single file; ~90 lines re-added; one non-trivial proof, `Congruence.elim` box case, already solved in substance).
- **Risk:** low–moderate. Main risk is the universe handling of `Proposition.Equiv` over a fixed
  `World` section variable vs. any downstream code that adopted the universe-polymorphic
  `LogicallyEquivalent`. `git grep` shows **no external users** of `LogicallyEquivalent` outside
  its own file, so downstream breakage is minimal.
- **Reuse implications:** restores parity with HML and CLL; makes Modal a first-class
  `LogicalEquivalence` participant; aligns equivalence with the already-parametric
  `Proposition.valid`/`logic`/`Cube`.

**Optional refinement (best of both):** define the parametric `Proposition.Equiv S` and also
keep a `LogicallyEquivalent := Proposition.Equiv Set.univ` abbrev so the new name survives, but
back it by the framework. This avoids a naming regression while restoring integration.

### Option B — Defend the standalone `LogicallyEquivalent` (NOT recommended)

- **Argument for:** self-contained, no Foundations import, minimal surface; the congruence
  theorem is proved directly without typeclass plumbing.
- **Against:**
  1. Cannot express model-class-relative equivalence (T/B/4/5/S4/S5) — a core modal-logic need,
     and inconsistent with the parametric `Proposition.valid`/`Cube`.
  2. Duplicates the Foundations framework's purpose, violating reuse-first; leaves Modal as the
     lone logic *not* using `LogicalEquivalence` (HML + CLL do).
  3. Universe-polymorphic `World` quantification is a nonstandard semantics that pins a universe
     parameter on all uses.
  4. Loses `IsEquiv` (rewriting) and the discoverable `Congruence` instance.
- A defense would require a written rationale for (1)–(4); no such rationale exists in the PR
  body (the PR body discusses only the `{atom,bot,imp,box}` primitive refactor, not the
  equivalence redesign) and there are **0 PR reviews/comments** endorsing it. Absent that, Option
  B should be marked for user decision rather than adopted by default. **No sorry/axiom debt is
  involved in either option.**

## Recommendation

Adopt **Option A (hybrid restore)**: keep #662's primitive/context refactor, re-import
`Cslib.Foundations.Logic.LogicalEquivalence`, and re-add `Proposition.Equiv S`, its notation
(`≡[S]`, `≡`), `equiv_def`/`equiv_iff`/`equiv_valid`, the `IsEquiv` and `Congruence` instances,
`Satisfies.Context`/`HasHContext`, and the Modal-K `LogicalEquivalence` instance — porting the
already-solved congruence proof into `Congruence.elim` for the `{impL, impR, box}` cases.
Optionally retain `LogicallyEquivalent` as an abbrev for `Proposition.Equiv Set.univ`.

## Mathematical Elegance & Consistency Rationale

Beyond the reuse-first argument, the parametric restoration is the *mathematically* correct
object for this library — decided by three grounded facts, not by convention:

### 1. The fork already commits to frame-class-relative reasoning everywhere except equivalence

`Proposition.valid` is parametric over a model class `S` (`Modal/Basic.lean:443`), `logic S` is
derived from it (`:448`), and `Cube.lean` builds the entire K/T/B/4/5/D hierarchy as model
classes on top of that. Frame-relative truth *is* the point of modal logic and the reason the
Cube exists in this fork. The standalone `LogicallyEquivalent` is hardwired to all models, so it
can express only K-equivalences: **`◇□φ ≡ □φ` (an S5 fact) is literally inexpressible.** This
leaves the library with a parametric notion of *validity* beside a non-parametric notion of
*equivalence*, and the natural bridge between them —

```
equiv_valid : φ₁ ≡[S] φ₂ → (φ₁.valid S ↔ φ₂.valid S)
```

— cannot even be stated. Restoring `Equiv S` makes equivalence a graded family indexed by the
same `S` that `valid`/`logic`/`Cube` already use, and `equiv_valid` is the morphism connecting
the two families. That symmetry is the consistent design.

### 2. The parametric form *subsumes* the HML pattern rather than conflicting with it

HML's `Proposition.Equiv` (`HML/LogicalEquivalence.lean:22`) is `∀ lts, a.denotation lts =
b.denotation lts` — quantified over *all* models, no class parameter, wired into the framework
via `eqv := Proposition.Equiv`. HML has no `S` because process equivalence has no analog of
frame conditions; Modal does (the Cube). So the elegant design is: the common core
`≡ := Equiv Set.univ` is **definitionally the same shape as HML's all-models `Equiv`** and is what
feeds the `LogicalEquivalence` instance (`eqv := Equiv Set.univ`), while the `≡[S]` index is a
Modal-specific enrichment layered exactly where the mathematics demands it. HML-consistency at
`S = Set.univ` *and* frame-class generality — not a trade-off.

### 3. The standalone's `∀ (World : Type v)` quantifier is the actually-inelegant part — and a fork deviation, not upstream

The standalone bakes a universe-polymorphic world-type quantifier *inside* the relation
(`Modal/LogicalEquivalence.lean:58`). Equivalence over "all world-types at a pinned universe `v`"
is a different mathematical object from "agreement over a model class on a given carrier," and it
pins a universe parameter onto every downstream use. Montesi's original fixed `World` as the
ambient section variable and quantified only over `m ∈ S` and `w` — the standard framing. Note
the provenance: the parametric design *is* the upstream/author design (the diff `-` side); the
standalone was introduced by this fork's own task-137 rewrite (`a084f9f2`). "Restore" therefore
means realigning with upstream; the fork made the deviation.

### Consequent refinements to the recommended move

- **Fix `World`.** Define `Proposition.Equiv (S : Set (Model World Atom))` over the ambient
  `World` section variable; **drop the `∀ World : Type v`** quantification. (Supersedes Open
  Question 3 — this is now a decided design point, not merely "acceptable".)
- **Drop `LogicallyEquivalent`, do not retain it as an abbrev.** `git grep` shows no external
  users, and carrying a second name for `Equiv Set.univ` re-introduces the "two notions of
  equivalence" smell the restoration exists to remove. Standardize on `≡`/`≡[S]`, matching HML and
  CLL. (Supersedes the "Optional refinement" above and Open Question 2.)

### The one condition that would flip this

If upstream were deliberately deprecating the `LogicalEquivalence` framework, defending the
standalone would become the forward-consistent choice. There is no such signal: HML and CLL both
still instantiate the framework, and PR #662 has **0 reviews** endorsing the equivalence redesign
— its body discusses only the `{atom,bot,imp,box}` primitive refactor, not the `Equiv` change,
indicating the removal was incidental rather than intentional.

## Standards Notes (CONTRIBUTING / NOTATION / ORGANISATION)

- Every touched file already begins with `import Cslib.Init` (transitively via `public import`);
  keep it.
- Re-added notation is `scoped` under `Cslib.Logic.Modal` (matches existing convention and the
  Foundations `≡` `infix:29`); no unscoped notation introduced — satisfies the Notation Policy.
- New/restored declarations need docstrings (docBlame); the diff `-` side already had them —
  port verbatim.
- Prop-valued `Proposition.equiv_*` are `theorem`s (defLemma-safe); lowerCamelCase where
  applicable; `Proposition.Equiv` is `def` (a relation), consistent with HML's `Proposition.Equiv`.
- No new axioms, no `sorry`, no vacuous definitions — zero-debt compliant.

## Files / Evidence

- `Cslib/Logics/Modal/LogicalEquivalence.lean` — current standalone version (lines 39–81).
- PR #662 diff, hunk `@@ -1,132 +1,83 @@` on that file — removed parametric design (`-` side).
- `Cslib/Foundations/Logic/LogicalEquivalence.lean:20,33` — framework class + `≡` notation.
- `Cslib/Foundations/Syntax/Context.lean:18,24,28`; `Congruence.lean:19` — supporting typeclasses.
- `Cslib/Logics/HML/LogicalEquivalence.lean:105`; `Cslib/Logics/LinearLogic/CLL/Basic.lean:653` — surviving framework instances.
- `Cslib/Logics/Modal/Basic.lean:205` (`Satisfies.Bundled`), `:209` (`HasInferenceSystem`), `:443` (`Proposition.valid` — parametric), `:116` (`Satisfies.box_iff_forall`).
- `Cslib/Logics/Modal/Cube.lean` — K/T/B/4/5/D as model classes using `Proposition.valid`.
- PR state: branch `feat/modal-formula-primitives`, base `main`, OPEN, mergeable, 0 reviews/comments (2026-07-02).

## Open Questions for User

1. ~~Confirm the goal is restoration of framework integration (Option A) vs. a written defense of
   the standalone (Option B).~~ **DECIDED (user, 2026-07-02): Option A — restore the parametric
   `Proposition.Equiv S` + `LogicalEquivalence` framework integration, in hybrid form (retain
   #662's `{atom,bot,imp,box}` primitives and `{hole,impL,impR,box}` Context). All three open
   questions are now resolved; the report is ready for `/plan`.**
2. ~~Keep the `LogicallyEquivalent` name as an abbrev, or revert to `≡`/`≡[S]` only?~~
   **DECIDED (see Rationale §Consequent refinements): drop `LogicallyEquivalent`; standardize on
   `≡`/`≡[S]`. No external users; retaining it re-introduces the two-notions smell.**
3. ~~Is reverting to a fixed `World` section variable acceptable?~~ **DECIDED (see Rationale §3):
   yes — fix `World`, drop the `∀ World : Type v` quantifier; it is the standard framing and the
   universe-polymorphic version is a fork deviation.**
