# Why ⊥ should be a primitive constructor (Zulip comment)

---

The main reason to keep `⊥` as a primitive constructor rather than encoding it as a distinguished atom via `[Bot Atom]` is **substitution invariance**.

Formulas over an atom type form the free algebra on `Atom` over the logical signature `{⊥, →, ∧, ∨}`. Substitution is the unique homomorphism extending a map on atoms — monadic `bind`. With primitive `⊥`, the substitution function has:

```lean
| .bot => .bot
```

This makes `⊥` invariant under every substitution, which is what the algebra requires: `⊥` is a nullary operation in the signature, and homomorphisms preserve operations. Axiom schemes like `⊥ → A` are automatically closed under substitution — substituting `σ` gives `⊥ → σ(A)`, not `σ(⊥) → σ(A)`.

With `⊥`-as-atom, `bind σ` sends `⊥ ↦ σ(⊥)`, which can be anything. Every theorem about substitution closure acquires a side condition `σ(⊥) = ⊥`. The free monad isn't free anymore — you're working in a subcategory of pointed-set-preserving maps.

This isn't a convention or a stylistic preference. In universal algebra (Rasiowa 1974, Blok-Pigozzi 1989, Font 2016), `⊥` is classified as a nullary operation symbol — same ontological kind as `→` and `∧`. Atoms are generators; connectives (including nullary ones) are operations. The distinction determines what "homomorphism" means.

The Johansson algebra point is subtle but important: in minimal logic, `⊥` has no axioms constraining it, but "arbitrary constant" ≠ "arbitrary variable." A constant is fixed under substitution; a variable is not. Johansson's `⊥` is a constant symbol in the signature with no non-logical axioms — not a variable that substitution can replace.

For what it's worth, every Lean 4 formalization I've found (FormalizedFormalLogic/Foundation, Trufaş 2024) uses primitive `⊥`, as do the standard proof-theory references (Troelstra-Schwichtenberg, van Dalen).
