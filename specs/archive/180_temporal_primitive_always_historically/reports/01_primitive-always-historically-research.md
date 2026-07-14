# Research Report: Primitive Always/Historically for Temporal Logic

## Task 180 — temporal_primitive_always_historically

### Motivation

The current Temporal.Formula type uses `{atom, bot, imp, and, or, untl, snce}` with four derived temporal operators:

| Operator | Name | Current derivation | Uses negation? |
|----------|------|--------------------|---------------|
| F (someFuture) | Eventually | `⊤ U φ` | No |
| P (somePast) | Once | `⊤ S φ` | No |
| G (allFuture) | Globally/Always | `¬F(¬φ) = ¬(⊤ U ¬φ)` | **Yes (twice)** |
| H (allPast) | Historically | `¬P(¬φ) = ¬(⊤ S ¬φ)` | **Yes (twice)** |

F and P are definable without negation (using ⊤ = ⊥ → ⊥ and the Until/Since operators), so they remain valid derivations in intuitionistic and minimal logic. But G and H use negation essentially — `¬F(¬φ)` requires double negation to express universal future quantification, which fails intuitionistically:

- **Classical**: `Gφ ↔ ¬F(¬φ)` — valid by double negation elimination.
- **Intuitionistic**: `¬F(¬φ)` is strictly weaker than `Gφ`. The former says "it's not the case that ¬φ eventually holds"; the latter says "φ holds at all future points." Intuitionistically, the absence of a counterexample does not imply universal truth.
- **Minimal**: Even weaker — without explosion, `¬F(¬φ)` carries less information still.

### Why G and H Appear in Axioms

G and H cannot be avoided in temporal axiom schemas. Key axioms that reference them directly:

| Axiom | Schema | Appears in |
|-------|--------|-----------|
| Future induction | `G(A → FA) → (A → GA)` | Axioms.lean |
| Past induction | `H(A → PA) → (A → HA)` | Axioms.lean |
| G distribution | `G(A → B) → (GA → GB)` | Derived theorems |
| H distribution | `H(A → B) → (HA → HB)` | Derived theorems |
| G/H interaction | `A → GP(A)` and `A → HF(A)` | Axioms.lean |
| Perpetuity | `GA ↔ A ∧ G(A)` | Derived |

Since these axioms cannot be restated using only U and S without G/H, the operators must be primitive for any non-classical temporal logic.

### Why F and P Stay Derived

Unlike G/H, the "eventually" operators have negation-free definitions:
- `F(φ) = ⊤ U φ` — "truth holds until φ" — structural, no negation
- `P(φ) = ⊤ S φ` — "truth held since φ" — structural, no negation

These definitions work in all three propositional bases (minimal, intuitionistic, classical). Making them primitive would add unnecessary constructors and case analysis without mathematical benefit.

### Proposed Primitive Set

```
Temporal.Formula: {atom, bot, imp, and, or, untl, snce, allFuture, allPast}
                   ─────────────────────────  ─────────  ──────────────────
                   propositional (task 173)    Kamp basis  new primitives
```

9 constructors total. Every pairing reflects a classical equivalence that breaks intuitionistically:
- `bot`/`imp` vs derived `neg` — minimal logic
- `and`/`or` vs Lukasiewicz encoding — intuitionistic connectives (tasks 173, 176)
- `allFuture`/`allPast` vs `¬F¬`/`¬P¬` — intuitionistic temporal operators (this task)

### Semantics

Structural forcing clauses for the new primitives:
- `(M, t) ⊨ G(φ)` iff `∀s ≥ t. (M, s) ⊨ φ` — universal future quantification
- `(M, t) ⊨ H(φ)` iff `∀s ≤ t. (M, s) ⊨ φ` — universal past quantification

Both are direct — no negation in the semantic clause. Compare with the current derived semantics which unfolds to `¬∃s ≥ t. (M, s) ⊨ ¬φ` — logically equivalent classically but structurally different.

### Scope Assessment

**Files requiring modification** (estimated from task 176 temporal and/or propagation):

| Category | Files | Change type |
|----------|-------|------------|
| Syntax/Formula.lean | 1 | New constructors + match cases (~200 lines) |
| Semantics/Satisfies.lean | 1 | Structural G/H clauses |
| ProofSystem/Axioms.lean | 1 | Axioms now reference constructors directly |
| ProofSystem/Instances.lean | 1 | Instance registration |
| Metalogic/Soundness.lean | 1 | G/H axiom soundness cases |
| Metalogic/DenseSoundness.lean | 1 | Same |
| Metalogic/MCS.lean | 1 | MCS helpers for G/H |
| Metalogic/Chronicle/TruthLemma.lean | 1 | G/H truth lemma cases |
| Metalogic/Completeness.lean | 1 | G/H in completeness proof |
| FromPropositional.lean | 0 | No change (propositional has no temporal ops) |
| **Total** | **~10-15** | Smaller than task 176 |

Note: Many temporal files that were modified in task 176 (for and/or) already handle the full constructor set and may need only minor additions for allFuture/allPast. The scope is smaller than the and/or propagation because G/H already appear extensively in the codebase as abbreviations — the change is from abbreviation to constructor, not introducing new concepts.

### Key Complication: swapTemporal

The `swapTemporal` function swaps future and past operators. Currently:
- `swapTemporal(allFuture φ) = allPast(swapTemporal φ)` — via the abbreviation expansion
- With primitive constructors: `| .allFuture φ => .allPast (swapTemporal φ)` and vice versa

This is straightforward but must be verified against the duality proofs in Soundness.lean.

### Classical Equivalence as Theorem

After making G/H primitive, the classical equivalences become theorems:
- `G(φ) ↔ ¬F(¬φ)` — provable from Peirce's law + temporal axioms
- `H(φ) ↔ ¬P(¬φ)` — symmetric

This validates conservative extension for classical temporal logic.

### Intuitionistic Temporal Logic Background

Intuitionistic temporal logics are less standardized than intuitionistic modal logics, but key references include:

- Boudou, J., Diéguez, M., & Fernández-Duque, D. (2017). A decidable intuitionistic temporal logic. *CSL*.
- Davies, R. (2017). A temporal-logic approach to binding-time analysis. *LICS* (original 1996).
- Kojima, K. & Igarashi, A. (2011). Constructive linear-time temporal logic: proof systems and Kripke semantics. *Information and Computation*.

The primitive G/H approach aligns with Boudou et al.'s framework where G and F are independent.

### References

- Boudou, J., Diéguez, M., & Fernández-Duque, D. (2017). A decidable intuitionistic temporal logic. *Proc. CSL 2017*.
- Davies, R. (1996/2017). A temporal-logic approach to binding-time analysis. *Proc. LICS*.
- Kojima, K. & Igarashi, A. (2011). Constructive linear-time temporal logic. *Information and Computation*, 209(12), 1491-1503.
- Kamp, H. (1968). *Tense Logic and the Theory of Linear Order*. PhD thesis, UCLA.
