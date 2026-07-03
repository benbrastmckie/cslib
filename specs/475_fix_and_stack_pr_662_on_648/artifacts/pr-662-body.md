## Summary

This PR is now **stacked on #648** (`feat/propositional-v2`) rather than targeting `main`
directly. It has been slimmed down to only the genuine modal-logic contribution — six files —
so it can be reviewed independently of #648's propositional-logic churn.

**Base branch**: `feat/propositional-v2` (#648)
**This branch**: `feat/modal-formula-primitives` (single squashed commit)

Everything propositional (`Cslib/Logics/Propositional/*`) is inherited unchanged from #648; this
PR touches only:

- `Cslib/Logics/Modal/Basic.lean`
- `Cslib/Logics/Modal/Cube.lean`
- `Cslib/Logics/Modal/Denotation.lean`
- `Cslib/Logics/Modal/LogicalEquivalence.lean`
- `Cslib/Foundations/Logic/Connectives.lean`
- `Cslib.lean` (module registration for the above)

## Design

### Primitives: box, not diamond

`Modal.Proposition` uses `{atom, bot, imp, box}` as primitive constructors — no native
`and`/`or`/`not`/`diamond`. Negation, conjunction, disjunction, and diamond are all derived
connectives via the Łukasiewicz convention:

```
¬φ  := φ → ⊥
φ ∧ ψ := ¬(φ → ¬ψ)
φ ∨ ψ := ¬φ → ψ
◇φ  := ¬□¬φ
```

Box is primitive (not diamond) because the necessitation rule (`if ⊢ φ then ⊢ □φ`) and the K
axiom (`□(φ → ψ) → (□φ → □ψ)`) are pure proof rules on a single primitive. With diamond as the
primitive, necessitation instead becomes the interaction law `¬◇¬` (the diamond-first
convention used by Blackburn–de Rijke–Venema, *Modal Logic*, Ch. 1). Box corresponds to
universal quantification over accessible worlds (`∀ w', r w w' → φ`), preserves conjunction
(`□(φ ∧ ψ) ↔ □φ ∧ □ψ`), and distributes over implication — the box-first presentation used by
Chagrov–Zakharyaschev, *Modal Logic*, §3.1.

Diamond's derivation (`◇φ := ¬□¬φ`) relies on excluded middle and is only valid in **classical**
modal logic; it fails in intuitionistic/minimal modal logic where box and diamond are
independent operators. Once non-classical modal logics are formalized in CSLib, a primitive
`HasDia` typeclass should be added alongside `HasBox` (noted as a design TODO in both
`Basic.lean` and `Connectives.lean`) — deferred here, not attempted.

### `HasBox` / `ModalConnectives` (self-owned `Connectives.lean`, Option A)

`Cslib/Foundations/Logic/Connectives.lean` introduces a small typeclass hierarchy shared across
propositional and modal formula types:

- Atomic classes: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`
- Bundled classes: `PropositionalConnectives` (`HasBot` + `HasImp`), `ModalConnectives`
  (`PropositionalConnectives` + `HasBox`)

This follows the operator-typeclass direction of @fmontesi's PR #607 (one class per operator).
Per the task-469 decision, this PR **self-owns** `Connectives.lean` (Option A) rather than
depending on #607, since #607 is unmerged and currently lacks `HasBot`/bundled classes. Full
decoupling onto #607's shared hierarchy is deferred to a joint follow-up once #607 lands — this
is a known, intentional piece of duplication, not an oversight.

`Modal.Proposition` registers `instance : ModalConnectives (Proposition Atom) where bot := .bot;
imp := .imp; box := .box` directly — it does **not** depend on
`Cslib/Logics/Propositional/Defs.lean`'s `PropositionalConnectives` registration. This is what
makes the modal layer cleanly separable from the propositional layer for this stacked-PR split.

### K/T/B/4/5/D validity and canonicity

`Basic.lean` proves each Sahlqvist axiom is valid under its corresponding frame condition, and
(for T/B/4/5/D) that the frame condition is also *necessary* — i.e. any model validating the
axiom schema for all propositions must satisfy the frame condition:

| Axiom | Frame condition | Validity | Canonicity |
|-------|-----------------|----------|------------|
| K | (none — all models) | `Satisfies.k` | — |
| T | reflexive | `Satisfies.t` | `Satisfies.t_refl` |
| B | symmetric | `Satisfies.b` | `Satisfies.b_symm` |
| 4 | transitive | `Satisfies.four` | `Satisfies.four_trans` |
| 5 | (right-)Euclidean | `Satisfies.five` | `Satisfies.five_rightEuclidean` |
| D | serial | `Satisfies.d` | `Satisfies.d_serial` |

Most of these are proved directly by `grind` given the relevant `Std.Refl`/`Std.Symm`/
`IsTrans`/`Relation.RightEuclidean`/`Relation.Serial` instance in scope; `Satisfies.four` uses
an explicit `intro`/`obtain`/`exact` derivation through `diamond_iff` rather than `grind`, since
the two-step existential witness composition is clearer written out. `Cube.lean` builds the
fifteen named modal logics of the modal cube (K, T, B, 4, 5, D, D4, D5, D45, DB, TB, KB5, S4,
S5, K45) as unions of these axiom sets over the relevant model classes, and proves the standard
cube inclusions (`k_subset_d`, `k_subset_b`, `k_subset_four`, `k_subset_five`, `d_subset_t`,
`k_subset_t`).

### Task-472 integration: parametric `Proposition.Equiv S`

`LogicalEquivalence.lean` defines logical equivalence via the shared
`Cslib.Foundations.Logic.LogicalEquivalence` framework, parametric in the model class `S`:

```
def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) : Prop :=
  ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]
```

with notation `≡[S]` / `≡` (`:= Proposition.Equiv Set.univ`). This replaces an earlier
non-parametric `LogicallyEquivalent` definition that fixed `S := Set.univ` structurally; the
parametric version lets equivalence be stated relative to any frame class in the modal cube
above (e.g. the T/B/4/5/S4/S5 classes), not just the class of all models. `Proposition.Equiv S`
is proved to be both an equivalence relation (`IsEquiv`) and a congruence
(`Congruence (Proposition Atom) (Proposition.Equiv S)`) with respect to one-hole contexts
(`Proposition.Context`), and Modal Logic K's equivalence (`S := Set.univ`) is registered as an
instance of the shared `LogicalEquivalence` framework.

## Why the split from #648

@fmontesi flagged in [Zulip](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603)
that the original PR was too large to review productively, mixing propositional-logic changes
(from #648) with the modal-logic contribution. This PR is the result of stacking cleanly on
#648: it now touches exactly the six files listed above, with no propositional-file changes and
no duplication of #648's propositional work.

## AI Disclosure

Claude (Anthropic) was used to assist with rebasing, file selection/transplantation, and CI
verification for this PR split. All Lean proofs were authored by the human contributors listed
in file headers; AI assistance was limited to mechanical git operations and drafting this PR
description.
