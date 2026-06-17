# Review Findings: PR #648 Alignment with Primitive ⊥ Perspective

**Task**: 228 — PR #648 primitive bot cleanup
**Date**: 2026-06-17

## Context

PR #648 (`feat/propositional-v2`) makes `⊥` a primitive constructor of `Proposition`,
removing `[Bot Atom]` constraints throughout the propositional logic module. This report
identifies minor issues where the PR's code or documentation does not fully align with
the algebraic perspective on primitive `⊥` developed in task 227.

## Finding 1: `intuitionisticCompletion` Docstring Is Now Misleading

**File**: `Cslib/Logics/Propositional/Defs.lean`
**Lines**: Around the definition of `intuitionisticCompletion`

### Current state

```lean
/-- Attach a bottom element to a theory `T`, and the principle of explosion for that bottom. -/
@[reducible]
def intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  (WithBot.some <$> T) ∪ IPL
```

### Problem

The docstring says "Attach a bottom element" but with primitive `⊥`, the bottom element
is already a constructor of `Proposition` — it was never missing. The function no longer
"attaches" a bottom element. What it actually does is:

1. Embed `T` into a theory over an extended atom type `WithBot Atom` via `WithBot.some <$>`.
2. Add efq axioms (`⊥ → A` for all `A`) to make the result intuitionistic.

With bot-as-atom (old design), `WithBot.some <$>` had the effect of mapping the old
`⊥` atom (`Bot.bot : Atom`) to `WithBot.some Bot.bot` — no longer the bottom. The new
`⊥` was `none : WithBot Atom`. This "detached" the old bot, which was crucial for
conservativity arguments.

With primitive `⊥`, `<$>` uses `subst`, and `subst` maps `.bot => .bot` (substitution
invariance). So `WithBot.some <$>` leaves `.bot` invariant — T's formulas keep their `⊥`.
The `WithBot` now just extends the atom type with a fresh atom but doesn't touch `⊥`.

### Recommendation

Update the docstring to reflect the actual semantics:

```lean
/-- Extend a theory `T` to an intuitionistic theory over a larger atom type by
adding the principle of explosion. The atom type is extended with `WithBot` to
ensure the result is over a strictly larger language. -/
```

### Note on potential simplification

With primitive `⊥`, the simpler `T ∪ IPL : Theory Atom` (same atom type, no `WithBot`)
would also produce an intuitionistic theory. The `WithBot` extension was originally needed
because `⊥` was an atom that had to be "replaced." Whether to simplify the function or
keep `WithBot` for compatibility is a separate design question — not required for this PR.

## Finding 2: Docstring in `Connectives.lean` — "Signature" Terminology

**File**: `Cslib/Foundations/Logic/Connectives.lean`
**Lines**: Module docstring

### Current state

```
The hierarchy adopts a hybrid five-primitive propositional signature `{atom, bot, imp, and, or}`,
```

### Problem

`atom` is a generator injection (the way atomic propositions enter the term algebra), not
an operation in the algebraic signature. The algebraic signature is `{⊥, →, ∧, ∨}` — one
nullary and three binary operations. Listing `atom` alongside the connectives as part of
the "signature" conflates generators with operations, which is precisely the distinction
that the primitive `⊥` argument relies on.

### Recommendation

Change "five-primitive propositional signature" to "five constructors":

```
The hierarchy adopts a hybrid approach with five constructors `{atom, bot, imp, and, or}`,
```

This accurately describes the Lean inductive type without making an algebraic claim that
could be challenged.

## Finding 3: No Issues Found (Confirmation)

The following aspects of the PR are all correctly aligned:

- `| bot => .bot` in `Proposition.subst` — substitution invariance ✓
- All `[Bot Atom]` constraints removed from `IsIntuitionistic`, `IsClassical`,
  `IPL`, `CPL`, `LEM`, `Pierce`, and variable declarations ✓
- `[Inhabited Atom]` removed from `derivationTop`, `derivable_iff_equiv_top` ✓
- `neg := (· → .bot)`, `top := .bot → .bot` — correct derived connectives ✓
- `impl` → `imp` rename consistent throughout ✓
- `substAtom` correctly handles the `bot` case via monadic bind ✓
- `instIsIntuitionisticIntuitionisticCompletion` instance is correct ✓
- `PropositionalConnectives` extends `HasBot` and `HasImp` — correct ✓
- `HasAnd` / `HasOr` as standalone classes — fine for now ✓
