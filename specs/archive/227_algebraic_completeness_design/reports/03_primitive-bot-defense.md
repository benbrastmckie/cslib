# The Case for Primitive ⊥ in Algebraic Propositional Semantics

**Task**: 227 — Algebraic completeness design
**Date**: 2026-06-17

---

## 1. The Design Question

CSLib's propositional `Proposition` type has five constructors:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom | bot | imp | and | or
```

The algebraic evaluator interprets these in a `GeneralizedHeytingAlgebra`:

```lean
def AlgEvaluate [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => AlgEvaluate v bot_val a ⇨ AlgEvaluate v bot_val b
  | .and a b => AlgEvaluate v bot_val a ⊓ AlgEvaluate v bot_val b
  | .or a b => AlgEvaluate v bot_val a ⊔ AlgEvaluate v bot_val b
```

The `bot_val` parameter enables three tiers of validity:

- **GHAValid** (MPL): `∀ (H) [GHA H] (v) (bot_val), AlgEvaluate v bot_val φ = ⊤`
- **HAValid** (IPL): `∀ (H) [HA H] (v), AlgEvaluate v ⊥ φ = ⊤`
- **BAValid** (CPL): `∀ (H) [BA H] (v), AlgEvaluate v ⊥ φ = ⊤`

A critic objects: primitive `⊥` and the `bot_val` parameter are inelegant. Why not
remove `⊥` from the formula type and treat it as a distinguished atom via `[Bot Atom]`?
Why not define three separate evaluation functions to avoid the parameter? This report
examines these alternatives and defends the current design on its merits.

## 2. Substitution Invariance: The Decisive Argument

### 2.1 Formulas as a Free Algebra

Formulas over an atom type `Atom` form the free algebra on `Atom` over the signature
`{⊥, →, ∧, ∨}`. Substitution `σ : Atom → Proposition Atom'` is the unique homomorphism
extending `σ` — the monadic `bind`:

```lean
def subst (f : Atom → Proposition Atom') : Proposition Atom → Proposition Atom'
  | .atom x => f x
  | .bot => .bot
  | .imp A B => .imp (A.subst f) (B.subst f)
  | .and A B => .and (A.subst f) (B.subst f)
  | .or A B => .or (A.subst f) (B.subst f)
```

The line `| .bot => .bot` is the crux. It says: **⊥ is a nullary operation in the
signature, fixed by every substitution**. This is not a convention — it follows from the
definition of homomorphism: a homomorphism of algebras preserves all operations, and a
nullary operation (constant) is an operation.

### 2.2 Consequences for Axiom Schemes

Axiom schemes must be closed under substitution. When `efq` says `⊥ → A` for all `A`,
and we substitute `σ` for atoms, we get `⊥ → σ(A)`. The scheme is preserved because `⊥`
is invariant under `σ`. CSLib proves this directly:

- `subst_preserves_axiom`: `PropositionalAxiom φ → PropositionalAxiom (φ.subst f)`
- `subst_preserves_intAxiom`: `IntPropAxiom φ → IntPropAxiom (φ.subst f)`
- `subst_preserves_minAxiom`: `MinPropAxiom φ → MinPropAxiom (φ.subst f)`
- `hilbertSubstitution`: generic substitution over derivation trees
- `Theory.Derivation.substAtom`: substitution transport for natural deduction

All of these work because `.bot => .bot` is unconditional.

### 2.3 What Breaks with ⊥-as-Atom

With `⊥` encoded as an atom via `[Bot Atom]`, substitution `σ` sends `⊥ ↦ σ(⊥)`, which
can be any formula. The scheme `⊥ → A` becomes `σ(⊥) → σ(A)`. To preserve closure, every
substitution must satisfy `σ(⊥) = ⊥` — a side condition that infects every theorem about
substitution.

This means the "free monad" on `Atom` is no longer free. You are working in a subcategory
of pointed-set-preserving maps. The monadic `bind` does not give you the correct notion of
substitution without a constraint. Every use of `substAtom`, `hilbertSubstitution`,
`subst_preserves_axiom` acquires a hypothesis `hf : f Bot.bot = .atom Bot.bot`.

### 2.4 Universal Algebra Makes This Precise

In every algebraic treatment of propositional logic (Rasiowa 1974, Blok-Pigozzi 1989,
Font 2016), `⊥` is a nullary operation symbol in the similarity type — the same ontological
kind as `→`, `∧`, `∨`. Atoms are generators; connectives (including nullary ones) are
operations. This distinction determines what "homomorphism" means:

- A homomorphism **preserves operations** (must map `⊥` to `⊥`).
- A homomorphism **can send generators anywhere**.

With `⊥`-as-atom, the concept of homomorphism is wrong unless manually constrained. An
algebra homomorphism extending a map on generators would be free to move `⊥`, breaking
the Lindenbaum construction: the canonical quotient map must send formula-`⊥` to a
specific element of the quotient algebra.

## 3. The Johansson Algebra Perspective

### 3.1 "Arbitrary Constant" ≠ "Arbitrary Variable"

A critic might argue: in minimal logic, `⊥` has no axioms. It behaves like an
arbitrary symbol. That is exactly what an atom is.

This is a category error. An **arbitrary constant** is fixed under substitution — it
evaluates to the same element across an entire evaluation. An **arbitrary variable** is
not — substitution can map it to any formula. Johansson's `⊥` is a constant symbol in
the signature with no non-logical axioms constraining its interpretation, not a variable
that can be replaced.

The `bot_val` parameter captures this correctly: `⊥` evaluates to a fixed (but
unconstrained) element `bot_val` of the algebra. The element is arbitrary, but it is the
same element throughout the evaluation. With `⊥`-as-atom, substitution could map `⊥` to
different formulas in different contexts, breaking this invariance.

### 3.2 The Three-Tier Hierarchy

The algebraic hierarchy that governs propositional logic is:

| Logic | Algebra | What constrains `⊥` |
|-------|---------|---------------------|
| MPL   | GHA + arbitrary constant | Nothing — `bot_val` is unconstrained |
| IPL   | HeytingAlgebra | `bot_val = ⊥` (bottom element: `⊥ ≤ a` for all `a`) |
| CPL   | BooleanAlgebra | `bot_val = ⊥` + complementation |

The `bot_val` parameter is the Johansson algebra's designated constant, unbundled into
the evaluator signature. Adding the axiom `⊥ ≤ a` (equivalently: `efq`) upgrades MPL to
IPL. Adding `a ∨ aᶜ = ⊤` (equivalently: `peirce`/`dne`) upgrades IPL to CPL.

No new typeclass is needed. Mathlib's existing `GeneralizedHeytingAlgebra` /
`HeytingAlgebra` / `BooleanAlgebra` hierarchy maps directly to the three logic tiers.
The `bot_val` parameter serves the role that `JohanssonAlgebra.designated_bot` would,
without introducing a typeclass that Mathlib does not have.

## 4. Why Not Three Separate Evaluation Functions?

An alternative: avoid `bot_val` by defining three separate evaluators, one per tier.

```lean
def HAEvaluate [HeytingAlgebra H] (v : Atom → H) : Proposition Atom → H
  | .bot => ⊥           -- hardcoded
  | .imp a b => HAEvaluate v a ⇨ HAEvaluate v b
  | ...
```

This works for IPL and CPL but not for MPL. A `GHAEvaluate` still needs the parameter,
because `GeneralizedHeytingAlgebra` genuinely does not have a bottom element — there
is no `⊥` to hardcode:

```lean
def GHAEvaluate [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H) :
    Proposition Atom → H
  | .bot => bot_val      -- forced: GHA has no ⊥
  | ...
```

So "three functions" means: `GHAEvaluate v bot_val` (with parameter),
`HAEvaluate v := GHAEvaluate v ⊥` (trivial specialization), and
`BAEvaluate v := GHAEvaluate v ⊥` (trivial specialization). Two of the three are
definitional wrappers around the first.

The current design already does this at the validity level. `HAValid` and `BAValid`
hardcode `bot_val = ⊥`; `GHAValid` quantifies over all `bot_val`. The soundness proofs
exploit the factoring: `int_alg_axiom_sound` delegates 8 of 9 cases to
`min_alg_axiom_sound` by instantiating `bot_val = ⊥`.

Splitting into three functions would either duplicate those 8 shared cases or define a
shared function to factor them out — recreating `AlgEvaluate` by another name.

The only way to truly eliminate `bot_val` is to **drop MPL** — define only `HAEvaluate`
and `BAEvaluate`, and never state anything about minimal logic. This forecloses the
unified completeness theorem and the conservative extension result, both of which depend
on the relationship between the parameterized and specialized evaluations.

## 5. What the Critic Gets Right

The `bot_val` parameter is genuinely unusual. No other Lean 4 formalization surveyed
(FormalizedFormalLogic/Foundation, Trufaş 2024, Mathlib examples) uses it — they all
hardcode `⊥ ↦ False` or `⊥ ↦ ⊥`. This is because none of them support three logic tiers
in a single framework.

The parameter does look ad hoc without context. The docstrings should make the algebraic
lineage explicit: the parameter is the designated constant of a Johansson algebra
(Johansson 1937, Rasiowa 1974), and the three-tier specialization is the standard
algebraic hierarchy from Rasiowa-Sikorski.

## 6. Convergent Evidence

### 6.1 Proof-Theoretic Tradition

In natural deduction (Gentzen 1935, Prawitz 1965), `⊥` has its own elimination rule
(⊥E / ex falso). In sequent calculus, it has its own left rule (⊥L). Troelstra and
Schwichtenberg (*Basic Proof Theory*) list `⊥` as a primitive nullary symbol alongside
`→`. Van Dalen (*Logic and Structure*) calls `⊥` an "indecomposable proposition" and
lists it alongside atoms but categorizes it distinctly.

### 6.2 Formalization Practice

Every Lean 4 formalization of propositional logic surveyed uses `⊥` as a primitive
constructor:

- **FormalizedFormalLogic/Foundation** (iehality/lean4-logic): five constructors including
  `falsum`.
- **Trufaş 2024** (arXiv:2410.23765, IPL in Lean 4): dedicated `⊥` constructor.
- **Coq propositional calculus** (arXiv:1503.08744): all connectives including `⊥` as
  primitive constructors.

No formalization was found using the `⊥`-as-atom approach.

### 6.3 Type-Theoretic Perspective

In the Curry-Howard correspondence, `⊥` corresponds to the empty type (`Empty`/`False`).
The empty type is a type former in every type theory (MLTT, HoTT, CIC) — it lives in the
universe of types, not as a term of any particular type. This is analogous to `⊥` being
a constant of the formula algebra, not a generator.

### 6.4 The Kripke Parallel

CSLib's Kripke semantics has exactly the same structure:

```lean
def IForces (v : World → Atom → Prop) (bot_forces : World → Prop)
    (w : World) : Proposition Atom → Prop
  | .bot => bot_forces w
```

The `bot_forces` parameter is the Kripke counterpart of `bot_val`:

| | Kripke | Algebraic |
|---|---|---|
| MPL | `bot_forces` arbitrary (upward-closed) | `bot_val` arbitrary |
| IPL | `bot_forces = fun _ => False` | `bot_val = ⊥` |

Both parameterize the interpretation of `⊥` for the same reason: MPL requires `⊥` to be
unconstrained. The designs are independently motivated but converge on the same structure.

### 6.5 Downstream Modal and Temporal Logics

Modal and temporal logics define `⊥` as a primitive constructor and build all derived
connectives through it:

```lean
abbrev neg (φ)     := .imp φ .bot           -- ¬φ := φ → ⊥
abbrev top         := .imp .bot .bot        -- ⊤ := ⊥ → ⊥
abbrev or  (φ₁ φ₂) := .imp (.imp φ₁ .bot) φ₂
abbrev and (φ₁ φ₂) := .imp (.imp φ₁ (.imp φ₂ .bot)) .bot
abbrev diamond (φ) := .neg (.box (.neg φ))  -- ◇φ := ¬□¬φ
abbrev allFuture (φ) := .neg (.someFuture (.neg φ))
```

These are classical logics where `⊥ ↦ False` is hardcoded in the satisfaction relation
(`| .bot => False`). The `bot_val` parameter does not appear. This is the correct
specialization: classical modal logic includes `efq`, so `bot_val = ⊥` in any model, and
the formula type already makes this structural.

Removing `⊥` from the formula type would require either `[Bot Atom]` on every
modal/temporal formula type (infecting every theorem with an extra typeclass constraint)
or replacing `⊥` with additional primitive constructors for `¬`, `∧`, `∨` (increasing
case counts in every induction without reducing complexity).

## 7. Primitive `∧` and `∨`

The critic correctly notes that making `∧` and `∨` primitive is independently needed for
nonclassical logics where they are not interdefinable from `→` and `⊥`. CSLib's
propositional type already does this (five constructors). But this is orthogonal to the
`⊥` question:

- Primitive `∧` and `∨` are needed because `∧`/`∨`-elimination rules and
  `∧`/`∨`-introduction rules are structurally different from their `→`/`⊥`-encodings
  in intuitionistic and minimal logic.
- Primitive `⊥` is needed because `⊥` is a nullary operation in the algebraic signature,
  invariant under substitution.

These are independent design requirements. Having primitive `∧` and `∨` does not
eliminate the need for primitive `⊥`, nor does having primitive `⊥` eliminate the need
for primitive `∧` and `∨`.

Note that CSLib's modal and temporal types take the opposite approach for `∧`/`∨`:
they derive them from `→` and `⊥`. This is appropriate for classical modal logic where
the interdefinability holds. If CSLib later supports intuitionistic modal logic, those
types will need primitive `∧`/`∨` as well — but they will still need primitive `⊥`.

## 8. Summary

The case for primitive `⊥` rests on one decisive argument and several convergent lines
of evidence:

**Decisive**: `⊥` is a nullary operation in the algebraic signature. As such, it must be
invariant under substitution (homomorphisms preserve operations). With `⊥`-as-atom, every
theorem about substitution acquires a side condition `σ(⊥) = ⊥`, the free monad structure
is broken, and the Lindenbaum construction requires manual constraints on homomorphisms.

**Convergent**: (1) Universal algebra classifies `⊥` as an operation, not a generator.
(2) Every surveyed formalization uses primitive `⊥`. (3) Proof theory treats `⊥` as a
logical constant with its own rules. (4) The Curry-Howard correspondence maps `⊥` to a
type former, not a term. (5) The Kripke semantics independently requires the same
parameterization (`bot_forces`). (6) Johansson's "arbitrary constant" is a constant
(substitution-invariant), not a variable. (7) The `bot_val` parameter is forced by GHA
lacking a bottom element and cannot be eliminated without abandoning MPL.

The `bot_val` parameter is the price of supporting three logic tiers in a single
algebraic framework. The alternative (⊥-as-atom) does not eliminate the parameter — it
moves it into the valuation, where it is less visible but structurally unsound without
constraints that the primitive-⊥ approach provides for free.

## References

- Johansson, I. (1937). "Der Minimalkalkül, ein reduzierter intuitionistischer
  Formalismus." *Compositio Mathematica*, 4, 119–136.
- Rasiowa, H. (1974). *An Algebraic Approach to Non-Classical Logics.* North-Holland.
- Rasiowa, H. & Sikorski, R. (1963). *The Mathematics of Metamathematics.* PWN.
- Blok, W. J. & Pigozzi, D. (1989). "Algebraizable Logics." *Memoirs of the AMS*, 396.
- Font, J. M. (2016). *Abstract Algebraic Logic.* College Publications.
- Troelstra, A. S. & Schwichtenberg, H. (2000). *Basic Proof Theory.* 2nd ed. Cambridge.
- van Dalen, D. (2013). *Logic and Structure.* 5th ed. Springer.
- Gentzen, G. (1935). "Untersuchungen über das logische Schließen."
  *Mathematische Zeitschrift*, 39, 176–210.
- Prawitz, D. (1965). *Natural Deduction.* Almqvist & Wiksell.
- Trufaş, L. (2024). "Formalizing Intuitionistic Propositional Logic in Lean."
  arXiv:2410.23765.
