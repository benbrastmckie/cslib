# Notation

Overview of the notation for common concepts.

## Equivalences
- Alpha equivalence: `m =α n`
- Bisimilarity: `p ~[lts] q` (`p` is bisimilar to `q` in the LTS `lts`)

## Operational semantics

### Option A
This option uses an extra arrow head to denote reflexive and transitive closure.

When there is only 'one' semantics:
- Reduction: `m → n`.
- Multi-step reduction (possibly zero): `m ↠ n`.
- Transition: `p [μ]→ q`, where `μ` is a transition label.
- Multi-step transition (possibly zero): `p [μs]↠ q`, where `μs` is a list of transition labels.
- Saturated transitions: `p [μ]⇒ q`.
- Multi-step saturated transitions: `p [μs]➾ q`.

When there are 'alternative' semantics, we suffix the arrow with the name of the transition relation or LTS under use. For example `m →[cbv] n` means that there is a reduction from `m` to `n` under the `cbv` reduction relation.
Another example: transitions look like `p [μ]→[late] q`, where `late` is an `LTS`.

### Option B

As Option A, but uses `*` to denote reflexive and transitive closure.
- Multi-step reduction (possibly zero): `m →* n`.
- Multi-step transition (possibly zero): `p [μs]→* q`, where `μs` is a list of transition labels.
- Saturated transitions: `p [μ]⇒ q`.
- Multi-step saturated transitions: `p [μs]⇒* q`.

### Option C
Like Option A, but with triangle heads (`⭢`) to distinguish arrows from the usual implication in Lean (`→`). E.g., `(m ⭢ n) → (n ⭢ s) → (m ⯮ s)`.

When there is only 'one' semantics:
- Reduction: `m ⭢ n`.
- Multi-step reduction (possibly zero): `m ⯮ n`.
- Transition: `p μ⭢ q`, where `μ` is a transition label.
- Multi-step transition (possibly zero): `p [μs]⯮ q`, where `μs` is a list of transition labels.
- Saturated transitions: `p μ⇒ q`.
- Multi-step saturated transitions: `p μs➾ q`.

When there are 'alternative' semantics, we suffix the arrow with the name of the transition relation or LTS under use. For example `m ⭢cbv n` means that there is a reduction from `m` to `n` under the `cbv` reduction relation.
Another example: transitions look like `p μ⭢late q`, where `late` is an `LTS`.

## Logic notation scoping

Single-letter identifiers are reused across the logic hierarchy with unrelated meanings. Scoped
notation makes this safe *within* a namespace, but a file that `open`s a logic namespace while
also referring to the generic proof-system layer sees both senses at once.

### The `S` collision

The token `S` currently carries three unrelated meanings:

- **`S` as the *Since* temporal operator** — scoped infix notation for `Formula.since`
  (`Cslib/Logics/Bimodal/Syntax/Formula.lean`), with a Temporal counterpart. Visible only where
  `Bimodal` or `Temporal` is open.
- **`S` as the proof-system type parameter** — the generic inference-system tag in
  `Cslib/Foundations/Logic/ProofSystem.lean`, e.g. `class ModusPonens (S : Type*) [HasImp F]
  [InferenceSystem S F]`. This is an ordinary binder name, not notation.
- **`S` as the combinatory-logic S-axiom** — docstring prose only, in the classic K/S/I
  axiom-schema naming for Hilbert systems (`ProofSystem.lean:33`, `MinimalHilbert` (K, S, MP)).
  The type-checker never sees it, so a careless rename corrupts it invisibly.

### Rule

When a file opens `Bimodal` or `Temporal` **and** applies a generic proof-system lemma, supply
the proof-system tag **positionally via `@`**, not as a named argument:

```lean
-- Wrong: the parser reads `S :=` as an application of the scoped `S` notation.
theorem foo := generic_lemma (S := Bimodal.HilbertTM) ...

-- Right:
theorem foo := @generic_lemma Bimodal.HilbertTM ...
```

Files relying on this workaround carry a local `NOTE:` comment explaining it. Those notes are
load-bearing while the collision exists and should be removed only together with a rename that
actually resolves it.

### Guidance for new notation

Prefer a distinctive symbol or a multi-character token over a bare capital letter for scoped
notation, and declare it `scoped` so it cannot leak into files that did not opt in.
