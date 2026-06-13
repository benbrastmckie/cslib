# Teammate B Findings: Architecture Alternatives for Min/Int/Classical Propositional Logic

## Summary

The current PR #635 approach (Option A: `{atom, bot, imp}` primitives with derived connectives)
is already substantially correct and fully deployed across the CSLib codebase. All four formula
types (PL, Modal, Temporal, Bimodal) use the same `{atom, bot, imp, ...}` pattern. The question
of whether to adopt full primitives, typeclasses, or Mathlib alignment has an evidence-based
answer given how the codebase has developed.

---

## Key Findings

### Finding 1: The Core Problem Is Not Formula Type Correctness

The task framing says the PR #635 problem is "intuitionistically, and/or are NOT definable from
imp/bot." This is a logic-level concern, not a type-level concern. The CSLib approach is:

- `and/or` ARE defined as `abbrev`s over `imp/bot` using the Lukasiewicz encoding
- These abbrevs are **classically correct** but NOT proof-theoretically primitive for intuitionism
- CSLib distinguishes logics by **axiom predicates** and **inference rules**, not by constructor sets
- The `IntPropAxiom` inductive does NOT include an axiom for and-intro/and-elim separately; instead,
  conjunction is derivable as `neg (imp A (neg B))` within the theory

Reading `NaturalDeduction/Basic.lean`: the `botE` rule (ex falso) is a primitive inference rule,
not an axiom. This means the **structural** distinction between minimal and intuitionistic logic
is captured at the derivation level, not the formula level. The `Derivation` inductive in
`Basic.lean` includes `botE` as a constructor, which means ALL three logics share the same
derivation type — they are distinguished by what the `Theory T` contains (empty for minimal,
IPL for intuitionistic, CPL for classical).

This design is correct and elegant. The "and/or not definable intuitionistically from imp/bot"
concern applies to **Kripke semantics** (where `A ∧ B` and `A ∨ B` in the Kripke frame sense
have different semantics from the classical translation), but since CSLib uses the classical
encoding for its syntactic representation and separates logic-level distinctions into proof
system layers, the concern does not apply to the formula type architecture.

### Finding 2: The Current Architecture Is Already Option B in Spirit

Looking at the actual code:

**`ProofSystem/Axioms.lean`** defines three separate axiom predicates:
```
MinPropAxiom  = {implyK, implyS}
IntPropAxiom  = {implyK, implyS, efq}
PropositionalAxiom = {implyK, implyS, efq, peirce}
```

**`NaturalDeduction/Basic.lean`** defines `botE` (ex falso) as a primitive inference rule in the
derivation, but makes it available to all logics. The distinction is: in `T.Derivation`, `botE` is
always a valid constructor, but for "minimal logic" the `Theory T = ∅`, which means the `botE` rule
can still fire (from context), while for intuitionistic logic, `⊥ → A` is an AXIOM (in `Theory T`),
making ex falso available even without hypothesis.

Wait — reading more carefully: `botE` in `Basic.lean` is a constructor that takes `Derivation Γ ⊥`
and produces `Derivation Γ A`. This is ex falso as an **inference rule**, present in all three
logics. The Hilbert-system separation (`MinPropAxiom`/`IntPropAxiom`) in `Derivation.lean` takes a
different approach: the Hilbert system does NOT have `botE` as a rule; instead intuitionistic logic
adds the axiom schema `⊥ → A`.

**The two proof systems (natural deduction vs. Hilbert) make different design choices** which
creates a tension: the natural deduction system in `Basic.lean` is not a minimal logic system
(it has `botE`), while the Hilbert system in `Derivation.lean` is properly parameterized.

**This is the real architectural concern**: the natural deduction system in `Basic.lean` appears
to implement intuitionistic logic only (with `botE` as a rule), while claiming to support minimal
logic via `Theory MPL = ∅`. But `botE` as an inference rule already gives minimal logic ex falso
if the context contains `⊥`. For true minimal logic (Johansson's), `botE` should not be a rule.

### Finding 3: No PR #607 Operators Directory Exists on This Branch

The Operators directory (`Cslib/Foundations/Logic/Operators/`) does not exist on the current
`pr3/temporal-syntax` branch. The files proposed in PR #607 (And.lean, Box.lean, Diamond.lean,
etc.) are not present. PR #607 appears to be a separate upstream contribution proposal.

The current `Connectives.lean` provides:
- `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` (atomic classes)
- `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` (bundled)
- `ImpBotDerived` (specification artifact, intentionally uninstantiated)

This is a **typeclass-based Option C** architecture — each formula type registers instances of
connective typeclasses, enabling polymorphic axiom definitions in `Foundations/Logic/Axioms.lean`.

### Finding 4: The Mathlib Alignment Option (Option D) Is Inappropriate for CSLib

Mathlib's `HeytingAlgebra`, `BooleanAlgebra`, `Bot`, `HImp` are **semantic/algebraic** structures
designed for reasoning about mathematical objects (lattices, etc.), not syntactic formula types for
logic formalization.

The key issues with Mathlib alignment:
1. `HeytingAlgebra` requires a lattice (bounded distributive lattice + Heyting implication). CSLib
   formula types are free algebras over atoms, not lattice structures.
2. Mathlib's `HImp` is the Heyting arrow in a lattice, with `a ⇨ b = sSup {c | c ⊓ a ≤ b}`.
   This is NOT the syntactic implication constructor needed for proof-theoretic work.
3. CSLib formulas need `DecidableEq` for proof system reasoning; Mathlib lattice instances do not
   provide this.
4. eric-wieser's suggestion (from PR #635 review) to co-opt `Bot`, `HImp`, `Sup`, `Inf` classes
   would create confusion between syntactic formula operations and algebraic structure, complicating
   proof-theoretic reasoning.

Mathlib's `Mathlib.Tactic.ITauto.IProp` is the closest analog: a full-primitive inductive type
with `{top, bot, and, or, imp, neg, iff, xor, eq, ne}`. But it is a decision procedure artifact,
not a proof-theoretic formalization.

### Finding 5: The simp/grind Backwards Lemma Issue from PR #607 Review

The PR #607 review concern (chenson2018) about simp/grind lemmas being "backwards" is important.
The principle is:

**WRONG direction (away from notation)**:
```lean
@[simp] theorem and_def : A ∧ B = (A → (B → ⊥)) → ⊥ := rfl
```

**CORRECT direction (into notation)**:
```lean
@[simp] theorem neg_neg_def : imp (imp A bot) bot = A ∧ ... -- expands concrete to notation
```

However, for CSLib's approach this is mostly moot because `and/or/neg` are `abbrev`s, meaning they
unfold definitionally without any simp lemmas. The issue would only arise if CSLib switched to
`def` instead of `abbrev` for derived connectives.

The current use of `abbrev` means: `A ∧ B` IS definitionally equal to `.imp (.imp A .bot) .bot`
without any simp lemmas needed. This is the cleanest possible approach.

The concern about `grind` not seeing through typeclass indirection is also relevant. In
`Foundations/Logic/Axioms.lean`, axioms are written as `HasImp.imp` and `HasBot.bot` rather than
notation, which grind can reason about directly since `HasImp.imp` unfolds to `.imp` after instance
resolution.

---

## Option Comparison

### Option A (current PR #635): `{atom, bot, imp}` with derived abbrevs

**Mathematical correctness**: For syntactic proof theory purposes, correct. The Lukasiewicz
encoding of `and/or/neg` is classically correct and produces valid derivations in classical logic.
For intuitionistic proofs, it is also sound but note that `A ∧ B ≡_Int ¬(A → ¬B)` intuitionistically,
which is what the encoding gives. The encoding is sound for all three logics.

**Proof elegance**: Maximum. Induction/recursion on `Proposition` has 3 cases (atom, bot, imp).
Every function (`Evaluate`, `IForces`, `Satisfies`, `complexity`, `atoms`) has 3 cases. The
`subst`, `substAtom`, `Derivation.weak`, etc. all benefit from the minimal constructor set.

**Extensibility**: Modal adds `box` (4 cases). Temporal adds `untl, snce` (5 cases). Bimodal would
add `box, untl, snce` (6 cases). Each extension adds exactly the operators needed, no more.

**Lean 4 idioms**: `abbrev` for derived connectives means zero overhead: no simp lemmas, no
typeclass resolution, definitional equality works immediately.

**Verdict**: The right choice for CSLib's proof-theoretic purposes.

### Option B: `{atom, bot, imp, and, or}` as constructors

**Mathematical correctness**: Logically redundant (and/or are definable from imp/bot classically
and in intuitionistic Kripke semantics). Creates semantic mismatch: the inductive connective `and`
constructor would need to be semantically equivalent to the Lukasiewicz encoding.

**Proof elegance**: 5 cases in every recursion/induction. Every semantic function (`IForces`,
`Evaluate`) needs and-intro/or-intro/or-elim cases. Every substitution needs 2 extra cases. For
the temporal formula type, this would mean 7 constructors.

**Extensibility**: Would create inconsistency with existing Modal/Temporal/Bimodal formula types
which all use Option A. A refactor across all four formula types would be needed.

**Lean 4 idioms**: Would require proving `and_simp : A.and B = imp (imp A (imp B bot)) bot` to
connect the constructor with the Lukasiewicz encoding, or alternatively redefining semantics to
match. Creates friction with all existing proofs.

**Verdict**: Not recommended. Creates more problems than it solves and contradicts the established
pattern in CSLib.

### Option C (current `Connectives.lean`): Typeclass-based connective composition

The current architecture IS Option C, already deployed. `Cslib.Logic.PropositionalConnectives`
is the mixin typeclass. Each formula type (`PL.Proposition`, `Modal.Proposition`,
`Temporal.Formula`) registers as an instance. The `Axioms.lean` module uses the typeclass API
(`HasImp.imp`, `HasBot.bot`) for polymorphic axiom definitions that work across all formula types.

**This is working correctly.** The `ProofSystem.lean` typeclass hierarchy
(`MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`) provides the correct
stratification.

The PR #607 Operators/ approach would be an **extension** of Option C: per-operator files with
simp lemmas. The concern raised by ctchou (3-file organization: Modal, Tensor, Propositional) and
by chenson2018 (simp direction) would need to be addressed.

**Verdict**: Already implemented. The question is whether to add per-operator simp lemma files
(PR #607 proposal), which is separate from the formula type architecture question.

### Option D: Mathlib alignment (`Bot`, `HImp`, `Sup`, `Inf`)

As analyzed above: inappropriate for syntactic proof-theoretic formalization. Mathlib's algebraic
typeclass hierarchy does not match the needs of formula types.

**Verdict**: Not recommended. Mathlib alignment is valuable for **semantics** (HeytingAlgebra
instances for Kripke frames), but not for **syntax** (formula types).

---

## Recommended Approach

**Option A (current PR #635) is correct and should be maintained.**

The architecture is mathematically sound, Lean-idiomatic, and already consistent across all four
formula types in CSLib. The stratification of Min/Int/Classical logic is correctly handled at the
proof system layer (via `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert` typeclasses
and corresponding `DerivationTree Axioms` parameterization), not at the formula type layer.

### Specific Recommendations

1. **Formula type**: Keep `{atom, bot, imp}` as primitives with `abbrev` for derived connectives.
   Do not add `and`/`or` as constructors.

2. **NaturalDeduction/Basic.lean**: Address the `botE` rule question. Currently `botE` is a
   primitive inference rule in `Derivation`, making it available in all three logics. For true
   minimal logic support, the natural deduction system should be parameterized (similar to the
   Hilbert system), or `botE` should be documented as "ex falso as a structural rule available
   in context, not as an axiom." The Hilbert system approach in `Derivation.lean` is cleaner:
   `botE` is handled via the `efq` axiom schema, which is included/excluded by the axiom predicate.

3. **PR #607 interaction**: The Operators/ files (if they arrive) would add per-operator simp
   lemmas in the format `@[simp] theorem neg_def (A : F) [PropositionalConnectives F] :
   neg' A = HasImp.imp A HasBot.bot`. The simp lemmas should rewrite **away** from the raw
   typeclass form and **into** the notation form, per chenson2018's review comment. The concern
   about grind visibility can be addressed by adding `@[grind]` lemmas alongside.

4. **Theory-level distinction (Defs.lean)**: The `Theory.MPL/IPL/CPL` approach (lines 121-129 of
   `Defs.lean`) is elegant. Keep it. The `IsIntuitionistic`/`IsClassical` typeclasses correctly
   capture the theory-level distinctions without touching the formula type.

5. **Kripke semantics for intuitionistic logic**: The `Semantics/Kripke.lean` module correctly
   separates the `botForces` predicate, enabling both intuitionistic (`botForces = fun _ => False`)
   and minimal (`botForces` = upward-closed predicate) semantics over the SAME formula type. This
   is the right approach.

---

## Evidence: Code Sketch for Why Option A Handles All Three Logics

The following shows how the same formula type supports all three logics:

```lean
-- Same formula type for all three logics
inductive Proposition (Atom : Type u) where
  | atom | bot | imp

-- Semantics adapts to logic via Theory
abbrev MPL : Theory Atom := ∅                           -- minimal
abbrev IPL : Theory Atom := Set.range (⊥ → ·)          -- intuitionistic
abbrev CPL : Theory Atom := Set.range (¬¬· → ·)        -- classical

-- Proof system distinguishes via axiom predicate
inductive MinPropAxiom : Proposition → Prop where ...  -- {K, S}
inductive IntPropAxiom : Proposition → Prop where ...  -- {K, S, EFQ}
inductive PropositionalAxiom : Proposition → Prop where ...  -- {K, S, EFQ, Peirce}

-- Natural deduction includes botE as a rule (available to all),
-- but minimal logic restricts what is in Theory T = ∅
inductive Theory.Derivation {T : Theory Atom} ... where
  | botE : Derivation Γ ⊥ → Derivation Γ A   -- always available

-- Kripke semantics uses botForces parameter
def IForces (bot_forces : World → Prop) (w : World) : Proposition → Prop
  | .bot => bot_forces w   -- minimal: arbitrary predicate; intuitionistic: fun _ => False
```

This pattern is clean, correct, and already fully deployed.

---

## Confidence Level

**High** on core findings (Options A vs. B vs. C vs. D comparison, current architecture assessment).

**Medium** on the `botE` rule concern in NaturalDeduction/Basic.lean — this requires checking
whether the intended semantics is "ex falso as a structural rule in minimal logic" (which is
non-standard) or whether minimal logic is distinguished only at the Hilbert system level.

**High** on Mathlib alignment being inappropriate for formula types.

**Medium** on PR #607 interaction — PR #607 does not exist on this branch, so the analysis is
based on reading the review comments cited in the task description, not actual code.

---

## Tactic Survey Notes

The current proof system uses `grind` extensively (visible in `Defs.lean` with `@[scoped grind]`
annotations). The `grind` tactic can see through `abbrev` definitions, confirming that Option A's
use of `abbrev` for derived connectives is compatible with the proof automation strategy. Using `def`
instead of `abbrev` would break `grind` visibility and require explicit `simp` unfolding lemmas.

---

## Files Read

- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean`
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Derivation.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Instances.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/IntMinInstances.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Basic.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Kripke.lean`
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean`
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Axioms.lean`
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Syntax/Formula.lean`
