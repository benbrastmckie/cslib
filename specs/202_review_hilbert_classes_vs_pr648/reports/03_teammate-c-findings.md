# Teammate C (Critic) Findings: Bool vs Prop vs GeneralizedHeytingAlgebra

**Role**: Critic — challenge all positions
**Task**: 202, Round 3 — Evaluate the Bool/Prop/GHA debate for valuation types
**Date**: 2026-06-15

---

## Key Findings

1. **Doty's "Bool for DPLL portability" claim is technically weak**: DPLL does not require changing the core valuation type. A computable `boolEvaluate : (Atom -> Bool) -> Proposition Atom -> Bool` function can coexist alongside the existing `Evaluate : (Atom -> Prop) -> Proposition Atom -> Prop` without any change to the current semantics. These serve different purposes and are architecturally independent.

2. **Bool is NOT strictly more portable than Prop for DPLL**: DPLL operates on formulas and assignments, not on Lean's `Evaluate` function. A SAT solver implemented in Lean would define its own computable evaluation over `Atom -> Bool` regardless of what the metalogic uses. Changing `Valuation` from `Prop` to `Bool` saves a thin translation layer at most.

3. **Waring's `GeneralizedHeytingAlgebra` suggestion names the wrong class**: GHA extends `Lattice`, `OrderTop`, and `HImp` — it has `⊤` but NOT `⊥`. Since CSLib's `Proposition` has a primitive `bot` constructor, any algebraic value type must have `⊥`. The correct class is `HeytingAlgebra` (for intuitionistic semantics) or `BooleanAlgebra` (for classical semantics). GHA is strictly insufficient because `Evaluate v .bot` would have no image.

4. **The existing `Atom -> Prop` design genuinely requires Prop for the completeness proof**: The canonical valuation in `StrongCompleteness.lean` is `canonicalValuation S := fun p => Proposition.atom p ∈ S`. This maps atoms to membership in a set — which gives `Atom -> Prop`. Replacing this with `Atom -> Bool` requires decidable membership in the MCS, but the MCS is built via Lindenbaum/Zorn (noncomputable). No Bool-based canonical valuation can be extracted without additional classical axioms.

5. **The `Prop` and `Bool` targets are mathematically equivalent for classical logic**: Both `Prop` (with `Classical.propDecidable`) and `Bool` instantiate `BooleanAlgebra`, so they capture exactly the same class of tautologies. The choice is not about mathematical content but about proof style and intended use.

6. **Parameterizing over `HeytingAlgebra` is architecturally sound for the semantic layer, but creates a two-track system**: Intuitionistic semantics already uses `World -> Atom -> Prop` (Kripke models in `Kripke.lean`). If you parameterize classical semantics over `HeytingAlgebra`, you would need `BooleanAlgebra` to recover classical validity, not just HA. The Kripke model design is architecturally different from the bivalent truth-value design, and they serve different logics.

---

## Challenges to Each Position

### Challenge to Doty's `Atom -> Bool` Argument

**Claim**: "Bool is more portable for DPLL/SAT solvers."

**Challenge 1: The portability argument conflates two different evaluation functions.**

A DPLL implementation in Lean would define its own `decide : (Atom -> Bool) -> Proposition Atom -> Bool` — a purely computable function that has nothing to do with CSLib's metalogic `Evaluate`. CSLib's `Evaluate` is used for stating and proving soundness/completeness theorems, not for running algorithms. Changing `Valuation` from `Prop` to `Bool` does not make CSLib more "SAT-solver friendly" in any deep sense. At most, it eliminates a one-line coercion `(v a : Bool).decide`.

**Challenge 2: Bool cannot serve as the canonical valuation in strong completeness.**

The canonical valuation in `StrongCompleteness.lean` (line 72) is:
```lean
canonicalValuation S := fun p => Proposition.atom p ∈ S
```
This has type `Atom -> Prop` because `∈` on `Set` returns `Prop`. To get `Atom -> Bool`, you would need `Decidable (Proposition.atom p ∈ S)` for every `p`. But `S` is the MCS produced by Lindenbaum's lemma (which uses Zorn's lemma / `Classical.choice`). There is no decidable oracle for membership in an arbitrary set built by choice. This is not a technical inconvenience — it is a fundamental fact about the proof strategy.

If you want a Bool-based completeness proof, you need an entirely different proof strategy: either a syntactic model (finite countermodel for finite atom types) or an explicit classical coercion. This would duplicate the completeness proof work, not simplify it.

**Challenge 3: DPLL over `Prop` with `Decidable` is already available.**

The proof in `StrongCompleteness.lean` already uses:
```lean
attribute [local instance] Classical.propDecidable
```
This makes every `Prop` decidable for the duration of the proof. If you want computable DPLL for finite atom types, you do not need to change the core valuation type. You add:
```lean
instance [Fintype Atom] [DecidableEq Atom] : Decidable (Tautology φ) := ...
```
on top of the existing `Atom -> Prop` semantics. This is a pure addition, not a replacement.

**Challenge 4: `Bool` does not foreclose future non-classical logics but does require a choice.**

The current `Atom -> Prop` design already supports intuitionistic logic via the Kripke model in `Kripke.lean` where valuations have type `World -> Atom -> Prop`. These two designs are architecturally separate: classical logic uses bivalent truth, intuitionistic uses Kripke frames. Bool would be appropriate for the classical bivalent layer specifically, and it does not affect the Kripke layer. So the "forecloses non-classical" argument is overstated — but `Bool` valuations would create a two-tier system where classical uses `Bool` and intuitionistic still uses `Prop`, which is arguably less uniform.

**Challenge 5: The "Bool is more portable" claim is about convenience, not mathematical substance.**

Both `Prop` (classical) and `Bool` are `BooleanAlgebra` instances. They characterize exactly the same tautologies. The choice between them is: which is more idiomatic for Lean metalogic? The answer is `Prop`, because:
- Lean's `∀`, `∃`, `→`, `∧`, `∨` are all in `Prop`
- The completeness proof is a `Prop`-level statement
- Downstream usage (`SemanticEntails`, `Tautology`) quantifies over `Valuation Atom` which is a `Prop`-level type

---

### Challenge to the Current `Atom -> Prop` Design

**Claim**: The current design is natural and uncontroversial.

**Challenge 1: `Atom -> Prop` cannot express a computational decision procedure without additional machinery.**

The current `Evaluate v φ` produces a `Prop`, which is not computable in general. This is fine for metalogic but means you cannot `#eval` or `#decide` semantic questions. If CSLib ever wants to include verified DPLL, a separate computable path is needed. The current design does not provide this.

**Challenge 2: The current design does not make the classical/intuitionistic split explicit in the type.**

Both classical semantics (`Evaluate : (Atom -> Prop) -> ... -> Prop`) and intuitionistic semantics (`IForces : (World -> Atom -> Prop) -> ... -> Prop`) use the same `Prop` universe. The distinction between them is entirely in the proof strategy and the quantifiers. A type-level distinction (e.g., using `Bool` for classical or a tagged type) would make the semantic layer more explicit about which logic is being modeled.

**Challenge 3: Is `Atom -> Prop` being used for its generality, or as an unconsidered default?**

The design decision `abbrev Valuation (Atom : Type*) := Atom → Prop` (line 33 of `Semantics/Basic.lean`) does not have a stated rationale. The doc comment says "A (bivalent) propositional valuation assigns a truth value to each atom" — the word "bivalent" implies two values, yet `Prop` has infinitely many (one per truth-equivalent class under propext). The type works classically because `Classical.propDecidable` collapses all non-False props to "true", but this is an implicit assumption that should be stated.

**Challenge 4: The soundness proof uses `by_contra` and `Peirce`, which are classical.**

In `prop_axiom_sound`, the `peirce` case uses `by_contra`. This means the soundness proof implicitly invokes classical logic, as expected. The `Atom -> Prop` design is correct for classical logic but would be wrong for a constructive soundness proof (which would need a different semantics). This is not a flaw but a design assumption worth documenting.

**Challenge 5: Three `bot` declarations create redundancy.**

`Proposition.bot` (constructor), `Bot (Proposition Atom)` (Lean core instance), and `HasBot`/`PropositionalConnectives` (CSLib typeclass instance) all track the same value. This is acknowledged in teammate reports from round 2 and remains a mild coherence concern.

---

### Challenge to Waring's `GeneralizedHeytingAlgebra` Suggestion

**Claim**: Use `GeneralizedHeytingAlgebra` as the right level of generality for valuations.

**Challenge 1: GHA lacks `⊥`, making it wrong for any logic with falsum.**

`GeneralizedHeytingAlgebra` extends `Lattice`, `OrderTop`, and `HImp`. It has `⊤` but NOT `⊥` — it is specifically "generalized" by dropping the bottom element. CSLib's `Proposition` has `bot` as a primitive constructor. In `Evaluate`, the bot case maps to `False`. In a GHA-based evaluator, you would write `Evaluate v .bot = ???` with no element available. This was verified by code experiment:

```
-- lean_run_code: Bool DOES have GeneralizedHeytingAlgebra (with Algebra.Order.Ring.Defs)
-- lean_run_code: Prop DOES have HeytingAlgebra
-- lean_run_code: Bool DOES have HeytingAlgebra (with same imports)
-- But HeytingAlgebra is needed for ⊥, not GHA
```

To interpret falsum, you need `HeytingAlgebra` (which extends `GeneralizedHeytingAlgebra` with `OrderBot` and the `himp_bot` law). Waring should have said `HeytingAlgebra`, not `GeneralizedHeytingAlgebra`.

**Challenge 2: HeytingAlgebra semantics give intuitionistic validity, not classical.**

If you parameterize `Evaluate` over `[HeytingAlgebra V]`, you get a soundness result for intuitionistic propositional logic (IPL), not classical. The Peirce axiom (`¬¬P → P`) fails in a generic Heyting algebra. For classical soundness, you would need `[BooleanAlgebra V]`. So the suggestion requires further refinement:
- Intuitionistic completeness: parameterize over `HeytingAlgebra` (Prop instantiates it)
- Classical completeness: parameterize over `BooleanAlgebra` (Bool instantiates it)

**Challenge 3: The suggestion would require a dual-track semantic system.**

CSLib already has two tracks: bivalent truth (classical, in `Semantics/Basic.lean`) and Kripke forcing (intuitionistic/minimal, in `Semantics/Kripke.lean`). Adding a third track parameterized over `HeytingAlgebra` would either duplicate the Kripke semantics (since `World -> Atom -> Prop` Kripke models already give HA semantics) or require showing the HA-based evaluation is equivalent to Kripke forcing — a non-trivial theorem.

**Challenge 4: Is this over-engineering for the library's current needs?**

CSLib does not currently have intuitionistic logic applications that would benefit from plugging in a different Heyting algebra. The concrete semantics over `Prop` and Kripke frames already covers all three logic strengths (minimal, intuitionistic, classical). Abstracting to `HeytingAlgebra` would create more typeclass constraints in every downstream proof without any immediate user.

**Challenge 5: Would `HeytingAlgebra` constraints be practical for contributors?**

Every soundness theorem would now have signature like:
```lean
theorem int_soundness {V : Type*} [HeytingAlgebra V] (v : Atom -> V) ...
```
This adds a universe and typeclass constraint to every call site. For contributors working with the specific case of `Prop`, this creates boilerplate. The benefit is generality — but the question is whether CSLib currently has users who would instantiate this at non-`Prop` types.

**Challenge 6: `Bool` does NOT instantiate `HeytingAlgebra` without additional imports.**

The code experiments revealed that `Bool` instantiates `HeytingAlgebra` only with `Mathlib.Algebra.Order.Ring.Defs` imported — an unexpected dependency. This means "use GHA/HA for generality to cover both Prop and Bool" is import-sensitive and fragile. A recommendation to use `HeytingAlgebra` for portability should come with explicit instance tracking.

---

## What's Being Missed in This Debate

### Point 1: The two-function architecture already exists.

CSLib has both:
- `Evaluate : (Atom -> Prop) -> Proposition Atom -> Prop` (in `Semantics/Basic.lean`)
- `IForces : (World -> Atom -> Prop) -> (World -> Prop) -> World -> Proposition Atom -> Prop` (in `Semantics/Kripke.lean`)

The natural extension is not to change either, but to add:
```lean
def BoolEvaluate (v : Atom -> Bool) : Proposition Atom -> Bool
  | .atom x => v x
  | .bot => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or a b => BoolEvaluate v a || BoolEvaluate v b
```
This is a completely computable function suitable for DPLL, and it can be proved equivalent to `Evaluate` via a decidability lemma. Adding this does not require changing the existing `Valuation` type or any existing proofs.

### Point 2: The real coercion between Prop and Bool.

The bridge theorem would be:
```lean
theorem Evaluate_eq_BoolEvaluate_decide [DecidableEq Atom] 
    (v : Atom -> Bool) (φ : Proposition Atom) :
    Evaluate (fun a => v a = true) φ ↔ BoolEvaluate v φ = true
```
This makes the classical isomorphism `Prop ≅ Bool` explicit and computable for the specific case of CSLib's evaluation function.

### Point 3: The real reason `Atom -> Prop` exists is for the canonical valuation.

The Lindenbaum construction requires:
1. Atoms map to membership predicates: `fun p => Proposition.atom p ∈ S`
2. MCS membership is in `Prop` (set membership is always `Prop`)
3. Therefore `canonicalValuation : Atom -> Prop` is the ONLY natural choice

Any Bool-based completeness proof would need to reconstruct this via `Classical.decide` applied to set membership, which is noncomputable anyway. There is no gain.

### Point 4: The Prop/Bool distinction does not affect the Kripke semantics at all.

The intuitionistic semantics in `Kripke.lean` uses `val : World -> Atom -> Prop` and the forcing relation in `Prop`. This would remain unchanged whether the classical semantics uses `Atom -> Prop` or `Atom -> Bool`. The two semantic layers are independent.

### Point 5: The actual question is about Decidable instances, not value types.

What Doty probably wants is: for finite atom types, can you decide tautologies? The answer is YES with the current design, using:
```lean
instance [Fintype Atom] [DecidableEq Atom] {φ : Proposition Atom} : 
    Decidable (Tautology φ) := ...
```
This leverages `Bool`-valued evaluation internally but does NOT require changing `Valuation`. The public API of `Tautology` stays the same.

---

## Risk Assessment

| Claim | Verdict | Risk if Adopted |
|-------|---------|-----------------|
| Switch to `Atom -> Bool` for DPLL portability | Technically unnecessary; thin benefit | Breaks canonical valuation proof; requires new completeness proof strategy |
| Use `GeneralizedHeytingAlgebra` for generality | Wrong class — GHA has no ⊥ | Immediate breakage: cannot interpret `.bot` in GHA |
| Use `HeytingAlgebra` for generality | Correct class but wrong scope | Over-engineering for current needs; intuitionistic semantics already covered by Kripke layer |
| Keep `Atom -> Prop` as-is | Correct for metalogic; weak for algorithms | No risk; minor: cannot run DPLL computably without addition |
| Add `BoolEvaluate` alongside `Evaluate` | Best option for both goals | No risk; pure addition |

---

## Confidence Level

**High confidence**:
- GHA is wrong (lacks ⊥) — verified by `lean_run_code` experiments
- Bool cannot serve as canonical valuation in Lindenbaum proof — proven by inspection of `canonicalValuation` definition
- Both `Prop` and `Bool` instantiate `BooleanAlgebra` and characterize the same classical tautologies — verified
- A separate `BoolEvaluate` function is the cleanest solution — architectural judgment

**Medium confidence**:
- `HeytingAlgebra` would be the correct class for an algebraically general semantic layer — dependent on design goals
- Bool/HA instances are import-sensitive (additional imports needed) — observed but not fully traced

**Low confidence**:
- Whether Doty's actual concern was about verification-based DPLL or about algorithmic efficiency — his specific motivation is not known from the question framing
- Whether Waring's suggestion was about the `Valuation` type specifically or about the semantic value type in a more general algebraic framework — the context "right generality" is ambiguous
