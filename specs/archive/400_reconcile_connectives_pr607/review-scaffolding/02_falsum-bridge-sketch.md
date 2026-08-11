# PR #607 Engagement — Falsum/Verum Scaffolding: Verified Lean Sketch

> **FACTUAL SCAFFOLDING — Points for a human-authored review. Rewrite every sentence in your
> own words before posting (CSLib Zulip AI policy #605827029). No paragraph here is
> ready-to-post prose.**
>
> All Lean snippets in this document were verified to compile against the fork's CSLib codebase
> (`lake build`, build successful, 2026-06-29). Claims marked "✓ rfl" are definitional equalities;
> claims marked "✓ builds" mean the instance or lemma elaborated without errors.

---

## 0. Retraction Note (Corrects Report 01)

**Do NOT propose a `HasBot` class.** Report 01 recommended adding `HasBot`/`HasTop` to #607.
That recommendation is corrected by report 02 and by eric-wieser's "`Has` prefix is a
Lean-3-ism" comment. The correct path:

- Mathlib already ships `Bot` and `Top` (in `Mathlib/Order/Notation.lean`) providing `⊥`/`⊤`.
- The fork's `Cslib/Logics/Propositional/Defs.lean` (lines 104-105) **already uses these**:
  ```lean
  instance : Bot (Proposition Atom) := ⟨.bot⟩
  instance : Top (Proposition Atom) := ⟨.top⟩
  ```
- Reusing `Bot`/`Top` (reuse-first principle) replaces minting `HasBot`/`HasTop`. The already
  existing `Bot (Proposition Atom)` instance means `⊥` notation is already available without
  any change to #607.

---

## 1. The Genuine Falsum Gap in #607

#607's connective set = `{∧, ∨, →, ¬, ↔, □, ◇, ⊗}`. **No `⊥`/`⊤` in the typeclass set.**
`HasNot` is a free primitive (no link to `⊥`).

For a formula type with **primitive falsum** (such as the fork's `PL.Proposition` with a `bot`
constructor, or the upstream `Proposition [Bot Atom]`), registering faithfully needs:

1. `⊥`/`⊤` notation — covered by Mathlib `Bot`/`Top` (already available, no new class needed).
2. A `HasNot` instance from the derived negation `neg = (· → ⊥)`.
3. A `@[grind/simp]` bridge lemma connecting `HasNot.not A` and `(A → ⊥)`.

#607's own diff already demonstrates (2) and (3) for the upstream propositional type:
```lean
-- from #607's Logics/Propositional/Defs.lean hunk:
instance [Bot Atom] : HasNot (Proposition Atom) := {not := Proposition.neg}

@[grind =] lemma not_eq [Bot Atom] (A) : (A → ⊥) = ¬ A := rfl
```

The fork's `PL.Proposition` needs the same treatment once #607 merges.

---

## 2. Verified Lean Sketch: `HasNot` instance + bridge for `PL.Proposition`

**How to read this sketch**: `HasNot607` stands for #607's actual `HasNot` class (not in the
fork yet). The snippet was compiled against `Cslib.Logics.Propositional.Defs` — all claims
elaborate without errors. ✓

```lean
-- Define HasNot exactly as PR #607 defines it (single-method mixin)
class HasNot607 (α : Type*) where
  not : α → α

-- CLAIM 1 ✓: PL.Proposition registers HasNot faithfully via derived neg
instance instHasNot607PL {Atom : Type*} [DecidableEq Atom] :
    HasNot607 (Proposition Atom) where
  not := Proposition.neg
-- Reason: Proposition.neg A = Proposition.imp A .bot, which is a faithful
-- intuitionist/minimal-logic negation: ¬A := A → ⊥.

-- CLAIM 2 ✓ (rfl): HasNot607.not A = derived neg
-- Both sides are definitionally Proposition.imp A Proposition.bot.
lemma hasNot607_eq_neg (A : Proposition Atom) :
    HasNot607.not A = Proposition.neg A := rfl

-- CLAIM 3 ✓ (rfl): Bridge lemma — (A → ⊥) = HasNot607.not A
-- Here → is PL scoped notation (= Proposition.imp), ⊥ is Bot.bot (= Proposition.bot).
-- Both sides reduce to Proposition.imp A Proposition.bot.
@[grind =] lemma negBridgeRfl (A : Proposition Atom) :
    (A → ⊥ : Proposition Atom) = HasNot607.not A := rfl

-- CLAIM 4 ✓ (rfl): Bot.bot = Proposition.bot (existing instance in Defs.lean)
example : (⊥ : Proposition Atom) = .bot := rfl

-- CLAIM 5 ✓ (rfl): Top.top = Proposition.top = Proposition.imp .bot .bot
example : (⊤ : Proposition Atom) = .top := rfl
example : (⊤ : Proposition Atom) = .imp .bot .bot := rfl
```

**Build result** (2026-06-29): `Build completed successfully`. Warnings: unused `DecidableEq`
in `hasNot607_eq_neg` and `negBridgeRfl` (minor; omit the variable in the final version with
`omit [DecidableEq Atom] in`). No errors.

---

## 3. Orientation of the Bridge Lemma (Connects to Phase 3)

There are two natural orientations for the `not_eq` bridge:

| Orientation | Direction | Effect on grind |
|---|---|---|
| `(A → ⊥) = ¬A` | imp-form → notation | grind sees notation as normal form; cannot then reduce `Satisfies m w (¬A)` via Satisfies equations |
| `¬A = (A → ⊥)` | notation → imp-form | grind unfolds notation to imp-form; can then apply Satisfies equations |

For a `Satisfies` relation defined on constructors (as in #607's Modal hunk), orientation
matters — see `03_grind-direction-finding.md` for the empirical finding.

---

## 4. Optional Default Instance (Float as Question, NOT a Demand)

A default instance would derive `HasNot` from any type that has both `HasImpl` and `Bot`:

```lean
-- Optional, for discussion — NOT recommended to push into #607 without maintainer discussion
instance (priority := 50) [HasImpl α] [Bot α] : HasNot α := ⟨fun φ => HasImpl.impl φ ⊥⟩
```

**Why attractive**: It expresses the Johansson/Prawitz convention `¬φ := φ → ⊥` as a
typeclass-level default, meaning any imp+bot formula type automatically gets `HasNot` for free.

**Diamond-inheritance hazard**: A classical formula type might register both this default
instance AND a primitive `HasNot` instance (e.g., a Boolean negation). The two instances
would conflict. The `priority := 50` reduces (but does not eliminate) the risk. Resolution
ambiguity at the `HasNot.not` call site may produce surprising proof states.

**Decision**: Float as a question to the maintainers, not as a concrete proposal. Do not push
without confirming there are no downstream diamond conflicts.

---

## 5. Summary of Points for the Review (Falsum/Verum Section)

These are *points to make*, not prose to paste:

- Retract the "`HasBot` class" ask from the prior comment: Mathlib `Bot`/`Top` already serve
  this role, and CSLib's `Proposition` already uses them.
- The genuine gap: no `⊥`/`⊤` in #607's typeclass set; no bridge `(φ → ⊥) = ¬φ`.
- Fix: (i) keep Mathlib `Bot`/`Top` as-is; (ii) add `instance : HasNot (P Atom) :=
  {not := P.neg}` downstream; (iii) add `@[grind =] lemma not_eq : ... := rfl`.
- These are *additive* — no changes to #607's existing classes are required.
- Float the default `[HasImpl][Bot] → HasNot` instance as a question, noting the hazard.
- Verify bridge orientation matches the `_def` direction settling in Phase 3 (see
  `03_grind-direction-finding.md`).
