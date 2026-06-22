# Teammate B Findings: Alternative Patterns for Propositional Logic in CSLib

**Focus**: Alternative patterns, prior art, and how other projects handle propositional logic formalization.

---

## Key Findings

The Zulip thread (23 messages, participants: Benjamin Brast-McKie, Thomas Waring, Matthew Doty, Ching-Tsun Chou) centers on three interconnected design conflicts:

1. **`⊥` as primitive constructor vs. atom**: Whether falsum should be a dedicated `| bot` constructor in the `Proposition` inductive type (Benjamin + Ching-Tsun Chou) or treated as a special atom allowing its absence in minimal logic (Thomas Waring).

2. **`Prop`-valued vs. `Bool`-valued semantics**: Whether `Evaluate` should return `Prop` (needed for canonical model construction via Lindenbaum/Zorn) or `Bool` (needed for computable DPLL/SAT procedures) (Matthew Doty).

3. **Algebraic generality**: Whether semantics should be polymorphic over `GeneralizedHeytingAlgebra` (Thomas Waring's proposal) or use separate evaluators for different value types (the current dual-evaluator approach with `Evaluate` + `BoolEvaluate` + `AlgEvaluate`).

The current CSLib state (as of the branch under PR #648) provides all three layers: `Evaluate` (Prop-valued), `BoolEvaluate` (Bool-valued), and `AlgEvaluate` (GHA-polymorphic), with bridge lemmas connecting them. This is already a working resolution of the central conflicts.

---

## Prior Art Survey

### 1. FormalizedFormalLogic (Lean 4)

The [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic) project formalizes superintuitionistic propositional logics, classical logic, and provability logic in Lean 4. Their approach:

- Uses an inductive formula type with `bot` as a **primitive constructor** (not an atom).
- Supports classical, intuitionistic, and intermediate logics from a single formula type.
- Establishes soundness and completeness for Kripke semantics.
- The book version is at: https://formalizedformallogic.github.io/Book/

**Design choice alignment**: Takes Benjamin's side on `⊥` as a primitive. Their completeness proofs require `bot` to be a constructor, not an atom, for the same reasons Benjamin articulates.

### 2. James Oswald's Typeclass Approach for Logic Formulae in Lean 4

A blog post ([A Simple Typeclass for Logic Formulae in Lean 4](https://jamesoswald.dev/posts/a-type-class-for-logic/)) proposes a typeclass-based approach where each logic registers connectives as typeclass instances. This is close to Thomas Waring's `HasInterp` design and CSLib's existing `PropositionalConnectives` hierarchy.

### 3. Intuitionistic Propositional Logic in Lean (arXiv:2410.23765)

This formalization (referenced in search results) verifies soundness and strong completeness with respect to both Kripke and Heyting algebra semantics. Key points:
- Uses `bot`, `imp`, `and`, `or` as primitive constructors (bot is primitive).
- Employs both Kripke and algebraic semantics as dual completeness witnesses.
- The connection between `Prop`-valued Kripke semantics and algebraic semantics is explicitly bridged.

### 4. Thomas Waring's Branch (`cslib_SKI/blob/kripke/...`)

Thomas Waring's own branch (cited in the thread) defines:

```lean
abbrev Valuation (Atom : Type*) (H : Type*) := Atom → H

def Valuation.interp {H : Type _} [GeneralizedHeytingAlgebra H] 
  (v : Valuation Atom H) : Proposition Atom → H
  | atom x => v x
  | Proposition.and A B => (v.interp A) ⊓ (v.interp B)
  | Proposition.or A B => (v.interp A) ⊔ (v.interp B)
  | impl A B => (v.interp A) ⇨ (v.interp B)
```

Note: **No `bot` case** in the evaluator — this is the MPL-as-base design where `⊥` is not a constructor, so the evaluator needs no `bot` case. The completeness theorem is:

```lean
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A 
```

This is elegant but has a tradeoff: it does not handle `⊥` as a fixed semantic constant, which is why a `botVal` field is needed in models when `⊥` is present.

### 5. Thomas Waring's Compromise Branch (`intuitionistic/...`)

Thomas Waring proposes a **compromise** in his `intuitionistic` branch: define intuitionistic propositions as a **separate inductive type** (with `bot` as a constructor) and provide translations between the MPL and IPL proposition types. This is the cleanest alternative to the current design.

### 6. Coq/Ssreflect Pattern

In standard Coq formalizations of propositional logic:
- `bot` is almost universally a primitive constructor.
- Semantics are typically `bool`-valued (for decidability and reflection tactics) with an explicit coercion to `Prop`.
- The `reflect` predicate bridges `bool` and `Prop` — analogous to CSLib's `BoolEvaluate_eq_iff`.

### 7. Mathlib: No Deep-Embedded Propositional Logic

Mathlib 4 does **not** formalize a deep-embedded propositional logic per se. Instead, it uses:
- `HeytingAlgebra`, `BooleanAlgebra`, `GeneralizedHeytingAlgebra` as algebraic structures for lattice theory.
- Propositional logic is handled at the meta-level via Lean's type theory.

This means CSLib's propositional logic module is filling a genuine gap that Mathlib leaves open.

---

## Alternative Design Patterns

### Pattern A: Two Separate Inductive Types (Waring's Compromise)

Define two formula types:
- `MinProposition Atom` — MPL, no `bot` constructor, signature `{atom, imp, and, or}`
- `Proposition Atom` — IPL/CPL, with `bot`, signature `{atom, bot, imp, and, or}`

Provide translations:
```lean
def MinProposition.toProposition : MinProposition Atom → Proposition Atom
def Proposition.botAsAtom : Proposition Atom → MinProposition (Option Atom)
```

**Pros**:
- Cleanly separates concerns: no `botVal` hack in minimal semantics.
- GHA semantics for `MinProposition` is pure (no `bot_val` parameter).
- Each formula type aligns exactly with its intended algebraic model class.

**Cons**:
- Doubles the formula infrastructure (substitution, `Monad`, `DecidableEq` instances, etc.).
- Every theorem about propositional logic must be stated for both types or bridged.
- The embedding from MPL to IPL requires a type change, complicating reuse.

### Pattern B: Unified Type with `bot` Primitive + `bot_val` Parameter (Current CSLib Approach)

Keep `Proposition Atom` with primitive `bot`, use an explicit `bot_val : H` parameter in `AlgEvaluate` for GHA semantics.

```lean
def AlgEvaluate {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .bot => bot_val
  | ...
```

For IPL/CPL, hardcode `bot_val = ⊥`. For MPL, quantify over all `bot_val`.

**Pros**:
- Single formula type covers all three logic strengths.
- Substitution (`Monad` instance) works cleanly: `| .bot => .bot` — `⊥` is a fixed point of every substitution.
- Axiom schemas like `⊥ → A` are automatically closed under substitution without side conditions.
- Kripke semantics for intuitionistic/minimal logic uses the same `botForces` parameter pattern.
- Currently implemented and working in CSLib.

**Cons**:
- The `bot_val` parameter in `AlgEvaluate` and `botForces` in `KripkeModel` are "unnatural" from a GHA perspective (as Thomas Waring notes) — GHA does not have a bottom.
- Requires specifying `bot_val = ⊥` as a side condition when stating IPL/CPL completeness.

### Pattern C: GHA Polymorphism via `Atom` Extension (Waring's Bot-as-Atom)

Treat `⊥` as a special atom. The formula type has no `bot` constructor. IPL is encoded by adding `⊥` to the theory as an axiom schema.

```lean
-- No bot constructor:
inductive MinProposition (Atom : Type u) where
  | atom (x : Atom) | imp ... | and ... | or ...

-- IPL via theory extension:
abbrev IPL (Atom : Type u) : Theory (MinProposition Atom) :=
  Set.range (MinProposition.imp (.atom ⊥) ·)
```

**Pros**:
- Clean GHA semantics (no `bot_val` parameter).
- Minimal in constructors.
- Technically feasible (Thomas Waring's existing code).

**Cons**:
- `⊥` as an atom violates the free-algebra principle: substitution sends `atom ⊥ ↦ σ(⊥)`, which can be any formula. Every theorem about axiom-schema closure under substitution requires a side condition `σ(⊥) = ⊥`.
- Breaks the monad/Kleisli structure: `bind σ` no longer commutes with the logical status of `⊥`.
- Ching-Tsun Chou agrees with Benjamin that a separate `bot` constructor is cleaner.
- Does not align with FormalizedFormalLogic, arXiv:2410.23765, or standard Coq practice.

### Pattern D: Polymorphic Evaluate over HeytingAlgebra (Matthew Doty's Proposal)

```lean
def Evaluate {Atom A : Type u} [HeytingAlgebra A]
    (v : Atom → A) : Proposition Atom → A
  | .atom p => v p
  | .bot => ⊥
  | .imp φ ψ => Evaluate v φ ⇨ Evaluate v ψ
  | .and φ ψ => Evaluate v φ ⊓ Evaluate v ψ
  | .or φ ψ => Evaluate v φ ⊔ Evaluate v ψ
```

**Key problem** (identified by Thomas Waring): This makes MPL completeness false. In MPL, we need valuations where `v ⊥ ≠ ⊥` in the algebraic model — but hardcoding `| .bot => ⊥` eliminates that freedom. Every HeytingAlgebra model would validate EFQ, so MPL and IPL become indistinguishable. **This pattern is wrong for MPL**.

For CPL-only work (like Matthew's DPLL), it is fine since DPLL doesn't need MPL completeness.

---

## Recommended Approach

### Short Term (for PR #648 and immediate follow-ups)

The current CSLib design is **correct and defensible**. The key elements that should be preserved:

1. **Keep `bot` as a primitive constructor** in `Proposition Atom`. This is the right choice for substitution invariance, monad structure, and alignment with standard practice (FormalizedFormalLogic, arXiv:2410.23765, Coq).

2. **Keep the dual evaluator design**: `Evaluate` (Prop-valued), `BoolEvaluate` (Bool-valued), `AlgEvaluate` (GHA-polymorphic) with bridge lemmas. This already solves the `Prop` vs `Bool` conflict Matthew raised.

3. **Keep `bot_val` as an explicit parameter** in `AlgEvaluate`. This is the correct way to handle MPL semantics in GHA without a bottom element — exactly the same role as `botForces` in Kripke semantics.

### Medium Term

Consider adopting Thomas Waring's **compromise Pattern A** (two separate inductive types) as an **opt-in** for users who specifically need MPL without `bot`:

- Export `MinProposition` (no `bot`) for users focused on pure GHA semantics.
- Keep `Proposition` (with `bot`) as the primary type for IPL/CPL and the logics hierarchy.
- Provide translations `MinProposition.toProposition` and `Proposition.minimalFragment`.

This avoids forcing a single design decision on all CSLib users.

### On the Namespace Question (Matthew Doty's Suggestion)

Matthew suggested `Cslib.Logic.Structural` instead of `Cslib.Logic.PL`. This is a taste issue. `PL` is standard in logic textbooks. `Structural` suggests structural proof theory more than propositional logic. The current `Cslib.Logic.PL` is fine.

---

## Evidence / Key Code Examples

### Current CSLib: All Three Evaluators Coexist

From `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Bool.lean`:
```lean
-- Prop-valued (canonical model construction)
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop
  | .bot => False

-- Bool-valued (DPLL/SAT)
def BoolEvaluate (v : BoolValuation Atom) : PL.Proposition Atom → Bool
  | .bot => false

-- Bridge lemma
theorem BoolEvaluate_eq_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ
```

From `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra.lean`:
```lean
-- GHA-polymorphic (unifies all three logics)
def AlgEvaluate {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .bot => bot_val
```

### Kripke Semantics uses the Same Pattern

From `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Kripke.lean`:
```lean
structure KripkeModel (World : Type*) (Atom : Type*) [Preorder World] where
  botForces : World → Prop  -- analogous to bot_val in algebraic semantics
```

This shows that `bot_val` / `botForces` is not an accidental complexity — it is the correct semantic tool for handling `⊥` in models that may not validate EFQ.

### Substitution Invariance (Benjamin's Key Argument)

From `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean`:
```lean
def Proposition.subst {Atom Atom' : Type u} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | bot => .bot        -- ⊥ is fixed: no side condition σ(⊥) = ⊥ needed
  | imp A B => .imp (A.subst f) (B.subst f)
```

This would break under Pattern C (bot-as-atom): `atom ⊥ ↦ f ⊥` could produce any formula.

---

## Confidence Level

**High** on the following:

- The current `bot`-as-primitive design is correct and well-grounded in standard practice.
- The `Prop`/`Bool` conflict is already resolved by the dual-evaluator approach.
- The `AlgEvaluate` with `bot_val` parameter is the correct resolution to the GHA vs. HA debate.
- Pattern D (Doty's HeytingAlgebra polymorphism without `bot_val`) is **wrong for MPL** and should not be adopted.

**Medium** on the following:

- Whether Thomas Waring's two-type compromise (Pattern A) should be adopted long-term is a community preference question. It has real merit for the MPL-focused use case but doubles infrastructure cost.
- Whether the `Evaluate` (Prop-valued) should be unified with `AlgEvaluate` (setting `H = Prop`) is technically possible but may not improve ergonomics in practice.

**Low** uncertainty:

- The thread has converged: Benjamin's arguments for `bot`-as-primitive are technically sound, Ching-Tsun Chou agrees, and Thomas Waring's final message acknowledges the community may prefer `IPL` as the base theory. The path forward is clear.

---

*Sources*:
- Zulip thread: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/with/604219492 (fetched via API, 23 messages, IDs 602336739–605341190)
- CSLib codebase: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/`
- Thomas Waring's branch: https://github.com/thomaskwaring/cslib_SKI/blob/kripke/Cslib/Logics/Propositional/Semantics/Heyting.lean
- FormalizedFormalLogic: https://formalizedformallogic.github.io/Book/
- arXiv:2410.23765 — Intuitionistic Propositional Logic in Lean
