# Research Report: Primitive Diamond for Modal Logic

## Task 179 — modal_primitive_diamond

### Motivation

The current Modal.Proposition type uses `{atom, bot, imp, and, or, box}` with diamond derived as `◇φ := ¬□¬φ`. This derivation is only valid in classical logic:

- **Classical**: `□A ↔ ¬◇¬A` and `◇A ↔ ¬□¬A` — either derives the other.
- **Intuitionistic**: Neither derivation works. `¬□¬A` is strictly weaker than `◇A` because double negation elimination fails.
- **Minimal**: Even worse — without explosion, negation is weaker still, so `¬□¬A` carries less information.

Making diamond primitive enables intuitionistic and minimal modal logics (IK, IT, IS4, IS5) where □ and ◇ are genuinely independent operators.

### Upstream Comparison

Upstream CSLib uses `{atom, not, and, diamond}` as primitives, deriving box as `□φ := ¬◇¬φ`. This is the opposite choice from the fork. Neither is logic-neutral alone — having both as primitive is the correct approach for a library supporting all three propositional bases.

| System | Primitives | Derived | Logic-neutral? |
|--------|-----------|---------|---------------|
| Upstream | `{atom, not, and, dia}` | box, or, imp | No (derives box classically) |
| Fork (current) | `{atom, bot, imp, and, or, box}` | dia, neg, top | No (derives diamond classically) |
| Fork (proposed) | `{atom, bot, imp, and, or, box, dia}` | neg, top | Yes |

### Intuitionistic Modal Logic Background

The well-studied intuitionistic modal logics that become expressible:

| System | Axioms over IK | Status in literature |
|--------|---------------|---------------------|
| IK | K: □(A→B) → (□A→□B) | Well-studied (Fischer Servi 1984, Simpson 1994) |
| IT | IK + T: □A → A | Well-studied |
| IS4 | IK + T + 4: □A → □□A | Very well-studied (connects to topological semantics, Fitch-style modal types) |
| IS5 | IK + T + 4 + 5 | Studied but less common |
| IK + D | IK + D: □A → ◇A | Requires primitive ◇ to state |
| IK + B | IK + B: A → □◇A | Requires primitive ◇ to state |

Systems involving axiom D (`□A → ◇A`) and axiom B (`A → □◇A`) cannot even be *stated* without primitive diamond, since they reference ◇ directly in their axiom schemas.

### Frame Semantics

Classical modal frames: `(W, R)` with a single accessibility relation.

Intuitionistic modal frames: `(W, ≤, R)` — bi-relational:
- `≤` is a preorder (intuitionistic base)
- `R` is the modal accessibility relation
- Interaction conditions (Fischer Servi): if `w ≤ v` and `wRu`, then `∃v'. vRv' ∧ u ≤ v'`

Forcing clauses for the primitive modalities:
- `w ⊩ □φ` iff `∀v ≥ w. ∀u. vRu → u ⊩ φ` (monotone box)
- `w ⊩ ◇φ` iff `∃u. wRu ∧ u ⊩ φ` (existential diamond)

Both are structural — neither requires negation in its definition.

### Scope Assessment

**Files requiring modification** (estimated from task 175 and/or propagation):

| Category | Files | Change type |
|----------|-------|------------|
| Basic.lean | 1 | New constructor + Satisfies clause |
| Semantic infrastructure | 2-3 | .dia cases in Denotation, LogicalEquivalence |
| ProofSystem/Instances | 15 | Diamond axiom constructors per system |
| Metalogic/DerivationTree | 1 | .dia constructor in derivation tree |
| Metalogic/TruthLemma | 3 | .dia truth lemma cases (3 families) |
| Metalogic/Systems/*/Soundness | 15 | Diamond axiom soundness cases |
| Metalogic/Systems/*/Completeness | 15 | Diamond axiom hypotheses threaded |
| FromPropositional | 0 | No change (propositional has no modality) |
| **Total** | **~55** | Similar scope to task 175 |

### Axiom Design

For classical systems, diamond axioms are derivable from box + negation. For intuitionistic systems, they need explicit axiom constructors. Recommended approach:

1. Add dual axioms as optional typeclass instances:
   - `diaK`: `◇(A ∨ B) → ◇A ∨ ◇B` (diamond distributes over disjunction)
   - `diaDual`: `◇A ↔ ¬□¬A` (classical systems only)
   - `diaBox`: `□A → ◇A` (axiom D — serial frames)

2. For classical systems: prove `diaDual` as a theorem from Peirce's law, then derive all diamond axioms from box axioms + duality.

3. For intuitionistic systems: diamond axioms are independent and stated directly.

### Classical Equivalence as Theorem

The key deliverable: after making diamond primitive, the equivalence `◇A ↔ ¬□¬A` should be provable as a theorem for classical systems (those with Peirce's law), not assumed as a definition. This validates that the primitive-constructor approach is a conservative extension of the current design for classical logic.

### References

- Fischer Servi, G. (1984). Axiomatisations for some intuitionistic modal logics. *Rendiconti del Seminario Matematico*, 42, 179-194.
- Simpson, A. (1994). *The Proof Theory and Semantics of Intuitionistic Modal Logic*. PhD thesis, University of Edinburgh.
- Plotkin, G. & Stirling, C. (1986). A framework for intuitionistic modal logics. *Theoretical Aspects of Reasoning about Knowledge*.
- Bierman, G. & de Paiva, V. (2000). On an intuitionistic modal logic. *Studia Logica*, 65, 383-416.
