# Supplementary Report: Justification for Primitive `bot` Constructor

**Task**: 188 — first_propositional_upstream_pr
**Date**: 2026-06-14
**Topic**: Why `bot` must be a primitive constructor in `Proposition`, and why this does not break minimal logic

---

## Question

Does having `bot` as a primitive constructor in the `Proposition` type make minimal logic
impossible in the ND system? Upstream CSLib uses `{atom, and, or, impl}` with no primitive
`bot` — is their approach better for supporting minimal logic?

## Answer: Primitive `bot` Is Required, Not Harmful

**No.** Primitive `bot` does not break minimal logic. In fact, all standard references
agree that minimal logic **requires** `⊥` in its formula language. The concern confuses
two distinct things:

1. **`⊥` as a formula** (syntactic — present in all three logics)
2. **`⊥ → A` as an inference rule** (ex falso quodlibet — absent in minimal logic)

Johansson's Minimalkalkül (1937) explicitly retains `⊥` and defines negation as
`¬A := A → ⊥`. What it removes is the ex falso principle: you cannot derive an arbitrary
formula from falsum. The formula language is identical across minimal, intuitionistic,
and classical logic.

## Literature Evidence

### Johansson 1937 [Johansson1937]

Johansson defined the Minimalkalkül by removing the ex falso axiom `⊥ → A` from
Heyting's intuitionistic system. The formula language is unchanged — `⊥` remains a
primitive. Negation `¬A := A → ⊥` requires `⊥` to exist. Without `⊥`, negation is
undefined and minimal logic collapses to the positive fragment (a strictly weaker system).

**Citation**: I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer
Formalismus*, Compositio Mathematica 4 (1937), pp. 119–136.

### Prawitz 1965 [Prawitz1965]

Prawitz treats minimal logic with the same formula language as intuitionistic logic.
The difference is purely in which inference rules are available. Chapter I covers
both systems using `{⊥, →, ∧, ∨}` as primitives.

### Troelstra & van Dalen 1988 [TroelstraVanDalen1988]

Section 10.4 presents natural deduction systems for intuitionistic logic with `⊥`
as a primitive connective. Minimal logic is obtained by omitting the `⊥`-elimination
(ex falso) rule. The formula language is shared.

### nLab (Minimal Logic)

"Minimal logic is usually formulated using the same syntax as intuitionistic propositional
logic, with implication →, conjunction ∧, disjunction ∨, and **falsum or absurdity ⊥**
as the basic connectives."

## How CSLib's ND System Handles This Correctly

The `Theory.Derivation` inductive in `NaturalDeduction/Basic.lean` has **10 primitive
constructors**: `ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE`.

**There is no `botE` constructor.** Bottom elimination is a *derived rule* in
`DerivedRules.lean`, gated by `[IsIntuitionistic T]`:

```lean
def Theory.Derivation.botE [IsIntuitionistic T]
    (d : T.Derivation Γ ⊥) : T.Derivation Γ A :=
  Derivation.impE (Derivation.ax (IsIntuitionistic.efq A)) d
```

For `MPL = ∅` (the empty theory), `IsIntuitionistic` is **not satisfied**, so `botE` is
**unavailable** in minimal logic. This is exactly correct:

- You CAN write `⊥` as a formula (it's a constructor)
- You CAN derive `⊥` from contradictory assumptions (e.g., from `A` and `¬A = A → ⊥`)
- You CANNOT derive an arbitrary `B` from `⊥` (no ex falso — `botE` requires `[IsIntuitionistic T]`)
- You CAN derive `¬B` from `B → ⊥` (since `¬B := B → ⊥`, available via `impI`)

## Comparison: Upstream's No-Primitive-Bot Approach

Upstream uses `{atom, and, or, impl}` with `bot` only via `[Bot Atom]`:

```lean
instance instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
```

| Aspect | Upstream (`atom ⊥`) | Ours (`bot` constructor) |
|--------|---------------------|-------------------------|
| `⊥` always available | No — requires `[Bot Atom]` | Yes |
| Formula induction | 4 cases | 5 cases (includes `bot`) |
| Negation `¬A := A → ⊥` | Requires `[Bot Atom]` | Always available |
| Minimal logic | Positive fragment only (no `⊥`) | Johansson's full system with `⊥` |

**Upstream's approach is not more correct.** It models "positive minimal logic" (without
falsum), which is a valid but non-standard formulation. Johansson's original Minimalkalkül
explicitly includes `⊥`. Our approach is more faithful to the literature.

**Upstream's approach has a practical downside**: any theorem involving negation requires
threading `[Bot Atom]` through all type signatures. Our approach makes negation uniformly
available without constraints.

## Implications for PR Strategy

This analysis strengthens the case for our `{atom, bot, imp, and, or}` formula type:

1. It resolves ctchou's PR #635 objection (and/or are primitive, not derived)
2. It faithfully models Johansson's minimal logic (bot is present, ex falso is not)
3. It follows the standard Gentzen/Prawitz/Troelstra & van Dalen presentation
4. It enables uniform negation `¬A := A → ⊥` without type constraints

The PR description should explicitly justify primitive `bot` with these literature references,
preempting any reviewer question about whether it conflicts with minimal logic.

## Confidence: HIGH

Based on direct verification against Johansson 1937, Prawitz 1965, Troelstra & van Dalen
1988, and the nLab entry on minimal logic. The ND system's typeclass guard on `botE` was
verified by reading the source code.
