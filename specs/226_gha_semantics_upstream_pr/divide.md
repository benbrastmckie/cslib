# Labor Division: Propositional Semantics (Post-PR #648)

Working document. Assumes PR #648 (primitive `bot`, `imp` naming) lands.

## 1. Fundamental Conflicts

These are design decisions where only one approach survives upstream.

### 1.1 Lindenbaum Algebra Core (~70% overlap)

Benjamin and Thomas both build `GeneralizedHeytingAlgebra` / `HeytingAlgebra` /
`BooleanAlgebra` instances on the Lindenbaum quotient using the same strategies
(`le_himp_iff` for GHA, `BooleanAlgebra.ofRegular` for BA). The canonical valuation,
truth lemma, and completeness proof are structurally identical.

**Resolution**: Only one version goes upstream. Benjamin's is already adapted to
primitive `bot` and `bot_val`. Thomas's would require mechanical rewriting (~80%
parameter threading, ~20% bot-handling rewrites). The natural choice is Benjamin's
version, since it already targets the `Proposition` type in PR #648.

Thomas's unique additions to the Lindenbaum machinery — `propHeytingOfLE`,
`propBooleanOfLE` (theory-inclusion-based instances), `Theory.Extension.toGeneralizedHeytingHom`
(theory extension morphisms) — are purely additive and should be contributed on top.

### 1.2 Evaluation Function Signature

| Author | Function | Bot handling |
|--------|----------|-------------|
| Benjamin | `AlgEvaluate v bot_val φ` | Explicit `bot_val : H` parameter |
| Thomas | `Valuation.interp v φ` (`v⟦A⟧`) | `v ⊥` via `[Bot Atom]` atom lookup |

**Resolution**: With primitive `bot` in the `Proposition` type, `AlgEvaluate` with
`bot_val` is the correct design — `bot` is a constructor that needs a semantic clause.
Thomas's `Valuation.interp` would need a `| .bot => bot_val` case added.

### 1.3 Validity Predicate Style

Benjamin defines separate `GHAValid`/`HAValid`/`BAValid` predicates. Thomas uses a
single parametric `v ⊨ T` (theory validity) with algebra-tier constraints as hypotheses.

**Resolution**: Both are expressible. Thomas's `v ⊨ T` pattern is more general and
composes better with theory-parametric completeness theorems. Benjamin's separate
predicates can be defined as abbreviations. This is a surface-level API choice, not a
fundamental conflict — settle it in review.

## 2. Resolvable Conflicts

### 2.1 Naming: `imp` vs `impl`

PR #648 uses `imp`. Thomas and Matthew use `impl`. PR #648 states "open to reverting
if reviewers prefer `impl`." This needs a Zulip decision before further PRs.

### 2.2 Notation: `v⟦A⟧` vs plain function application

Thomas wraps the evaluator in a `CoeFun` instance giving `v⟦A⟧` notation. Benjamin
uses `AlgEvaluate v bot_val φ`. The notation is ergonomic but requires a `Valuation`
structure rather than a bare function. Adoptable in either direction.

### 2.3 `Preorder` vs `PartialOrder` for Kripke frames

Benjamin uses `Preorder`; Thomas uses `PartialOrder`. Standard references support
either. `Preorder` is more general. Low-stakes decision for review.

### 2.4 Kripke completeness route

Benjamin: direct canonical model via MCS/prime theories.
Thomas: indirect via algebraic semantics + prime filters (`KripkeModel.ofHeyting`).

Both are valid and produce different theorems. Not a conflict — they can coexist,
with Thomas's route providing an alternative proof that Kripke completeness follows
from algebraic completeness.

### 2.5 Context-as-meet vs universal-lower-bound for ND soundness

Benjamin: `∀ Φ, (∀ B ∈ Γ, Φ ≤ eval B) → Φ ≤ eval A`.
Thomas: `v⟦Γ⟧ ≤ v⟦B⟧` where `v⟦Γ⟧ = ⨅ (A ∈ Γ), v⟦A⟧`.

Thomas's formulation is cleaner for sequent-style reasoning. Benjamin's is used for
Hilbert-level soundness (which Thomas doesn't have). Both can coexist — Thomas's for
ND, Benjamin's for Hilbert.

## 3. Labor Division

### Benjamin's Contributions

Work only he has, targeting primitive `bot` + `bot_val`:

| Content | Files | LOC | Notes |
|---------|-------|-----|-------|
| GHA evaluation + validity | `Semantics/Algebra.lean` | 145 | `AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid`, `AlgTValid` |
| Bool + Prop evaluation | `Semantics/Bool.lean` | 149 | `Evaluate`, `BoolEvaluate`, bridge lemmas |
| Algebra-to-Bool bridge | `Semantics/Algebra/Bridge.lean` | 84 | `propEvaluateEq`, `boolEvaluateEq` |
| Kripke semantics | `Semantics/Kripke.lean` | 170 | `KripkeModel`, `IForces`, `botForces`, persistence, `IValid`/`MValid` |
| Semantic consequence | `Semantics/SemanticConsequence.lean` | 180 | `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails` |
| Hilbert axiom systems | `ProofSystem/Axioms.lean` | 231 | `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom` |
| Hilbert derivation | `ProofSystem/Derivation.lean` | 164 | `DerivationTree`, `Deriv`, `Derivable` |
| Theory instances | `ProofSystem/Instances.lean` | 120 | `MPL`, `IPL`, `CPL` theory definitions |
| Int/Min instances | `ProofSystem/IntMinInstances.lean` | 169 | `IsIntuitionistic`/`IsMinimal` instances |
| Algebraic soundness | `Semantics/Algebra/Soundness.lean` | 264 | Per-axiom-scheme soundness for all three systems |
| Lindenbaum quotient | `Semantics/Algebra/Lindenbaum.lean` | 426 | GHA/HA/BA instances on quotient |
| Algebraic completeness | `Semantics/Algebra/Completeness.lean` | 242 | `Theory.alg_complete`, per-logic completeness |
| Bot-free analysis | `Semantics/Algebra/Conservative.lean` | 101 | `IsBotFree`, validity subsumption (sorry on conservative ext) |
| Deduction theorem | `Metalogic/DeductionTheorem.lean` | 210 | |
| MCS foundations | `Metalogic/MCS.lean` | 162 | |
| Min soundness + Lindenbaum + completeness | `Metalogic/Min*.lean` | 876 | Strong completeness for MPL |
| Int soundness + Lindenbaum + completeness | `Metalogic/Int*.lean` | 968 | Strong completeness for IPL |
| Classical soundness + completeness | `Metalogic/Soundness.lean`, `StrongCompleteness.lean` | 655 | Strong completeness for CPL |
| ND equivalence + derived rules | `NaturalDeduction/Equivalence.lean`, `FromHilbert.lean`, `HilbertDerivedRules.lean`, `DerivedRules.lean` | 1440 | Hilbert ↔ ND equivalence |
| **Total** | | **~6756** | |

### Thomas's Contributions

Work only he has, to be adapted to primitive `bot`:

| Content | Source | Est. LOC | Notes |
|---------|--------|----------|-------|
| `v ⊨ T` notation + `ctxInterpret` | `Heyting.lean` | ~60 | Theory validity notation, context-as-meet |
| `Valuation.SValid` (sequent validity) | `Heyting.lean` | ~30 | `v⟦Γ⟧ ≤ v⟦B⟧` |
| GHA homomorphism preservation | `Heyting.lean` | ~40 | `GeneralizedHeytingHom.map_interpret` |
| Theory extension morphisms | `Heyting.lean` | ~50 | `Theory.Extension.toGeneralizedHeytingHom` |
| Theory-inclusion instances | `Heyting.lean` | ~40 | `propHeytingOfLE`, `propBooleanOfLE` |
| Consistency from non-top valuation | `Heyting.lean` | ~30 | `consistent_of_interpret_ne_top`, `MPL/IPL/CPL_consistent` |
| Kripke-from-algebra construction | `Heyting.lean` | ~80 | `KripkeModel.ofHeyting`, `ofHeyting_forces_iff` |
| Kripke model operations | `Heyting.lean` | ~60 | `KripkeModel.disj`, `.restrict`, upper set forcing |
| `Proposition.flip` | `Heyting.lean` | ~30 | Classical two-valued completeness |
| **Total** | | **~420** | Rebase cost: mechanical, ~80% param threading |

### Matthew's Contributions

Work only he has, to be adapted to primitive `bot`:

| Content | Source | Est. LOC | Notes |
|---------|--------|----------|-------|
| Dedekind-MacNeille completion | `DedekindMacneille.lean` | ~200 | `CompleteLattice`, `HeytingAlgebra`, `OrderEmbedding` instances |
| Canonical valuation into DM | `Heyting.lean` (additions) | ~40 | `Theory.canonicalVDM`, `canonicalVDM_spec` |
| HA-strengthened completeness | `Heyting.lean` (additions) | ~30 | `Theory.complete` over `HeytingAlgebra` |
| Tseitin transformation | `SAT/Tseitin.lean` | ~300+ | Separate SAT infrastructure (independent PR track) |
| **Total (semantics-relevant)** | | **~270** | Resolves `ipl_conservative_over_mpl` sorry |

## 4. PR Sequence

All PRs stack sequentially. Each is under 500 LOC. Author listed is the natural
owner based on existing work; co-review is expected.

### PR 2: Algebraic Semantics Definitions (Benjamin)

**Stacks on**: PR #648
**Files**: `Semantics/Algebra.lean`, `Semantics/Bool.lean`, `Semantics/Algebra/Bridge.lean`
**LOC**: ~378
**Content**: `AlgEvaluate` with `bot_val`, `Evaluate` (Prop-valued), `BoolEvaluate`
(Bool-valued), bridge lemmas connecting all three. Validity predicates
(`GHAValid`/`HAValid`/`BAValid`/`AlgTValid`).
**Why Benjamin**: Already adapted to primitive `bot`; no rebase needed.
**Review note**: Invite Thomas to comment on whether `v ⊨ T` notation layer should
be added here or in a follow-up.

### PR 3: Hilbert Proof Systems (Benjamin)

**Stacks on**: PR 2
**Files**: `ProofSystem/Axioms.lean`, `ProofSystem/Derivation.lean`,
`ProofSystem/Instances.lean`, `ProofSystem/IntMinInstances.lean`
**LOC**: ~500 (may need minor trimming)
**Content**: `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom` inductive types.
`DerivationTree` and `Deriv` (context-free derivation). `MPL`/`IPL`/`CPL` theory
definitions. `IsIntuitionistic`/`IsMinimal` instances.
**Why Benjamin**: Only he has this; no overlap with Thomas/Matthew.

### PR 4: Algebraic Soundness + Lindenbaum Algebra (Benjamin)

**Stacks on**: PR 3
**Files**: `Semantics/Algebra/Soundness.lean`, `Semantics/Algebra/Lindenbaum.lean`
**LOC**: ~500 (264 + 426 = 690 — will need splitting or trimming)
**Content**: Per-axiom soundness for all three systems. Lindenbaum quotient with
GHA/HA/BA instances. This is the overlapping core — Benjamin's version is used
because it targets primitive `bot`.
**Why Benjamin**: His Lindenbaum construction is already `bot`-adapted. Thomas's
would need ~20% rewrite.
**Risk**: 690 LOC exceeds 500. Options: (a) split Lindenbaum into its own PR,
(b) trim docstrings/whitespace, (c) accept ~690 since it's a natural unit.

### PR 5: Algebraic Completeness (Benjamin, Thomas reviews)

**Stacks on**: PR 4
**Files**: `Semantics/Algebra/Completeness.lean`
**LOC**: ~242
**Content**: `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`,
`alg_complete_classical`. Canonical valuation + truth lemma.
**Why Benjamin**: Already `bot`-adapted.
**Thomas's role**: Review for alignment with his `Theory.complete` theorem statement.
Propose `v ⊨ T` notation if desired.

### PR 6: Dedekind-MacNeille Completion + Conservative Extension (Matthew)

**Stacks on**: PR 5
**Files**: `Semantics/Algebra/DedekindMacneille.lean` (new),
`Semantics/Algebra/Conservative.lean` (resolves sorry)
**LOC**: ~300
**Content**: DM completion giving `HeytingAlgebra` from `GeneralizedHeytingAlgebra`.
`Theory.canonicalVDM` + `canonicalVDM_spec`. HA-strengthened `Theory.complete`.
Resolution of `ipl_conservative_over_mpl`.
**Why Matthew**: He's already implemented this. Needs mechanical adaptation to
primitive `bot` (add `bot_val` parameter to DM valuation).
**Benjamin's role**: Provide `Conservative.lean` with the sorry as scaffolding.

### PR 7: Homomorphism Theory + Notation (Thomas)

**Stacks on**: PR 5 (or PR 6 if independent)
**Files**: New file(s) under `Semantics/Algebra/`
**LOC**: ~250
**Content**: `GeneralizedHeytingHom.map_interpret`, `Theory.Extension.toGeneralizedHeytingHom`,
`propHeytingOfLE`/`propBooleanOfLE`, `consistent_of_interpret_ne_top`, `v ⊨ T`
notation, `ctxInterpret`.
**Why Thomas**: These are his unique contributions; he knows the API best.
**Adaptation needed**: Add `bot_val` parameter threading. Mechanical.

### PR 8: Kripke Semantics (Benjamin, Thomas reviews)

**Stacks on**: PR 5
**Files**: `Semantics/Kripke.lean`, possibly `Semantics/SemanticConsequence.lean`
**LOC**: ~350
**Content**: `KripkeModel`, `IForces`, `botForces`, persistence, `IValid`/`MValid`,
semantic consequence definitions.
**Why Benjamin**: His Kripke semantics use `botForces` which is the primitive-`bot`
analogue of Thomas's `[Bot Atom]`-derived forcing.
**Thomas's role**: Consider contributing `KripkeModel.ofHeyting` (Kripke-from-algebra)
and `KripkeModel.disj` as a follow-up or addition to this PR.

### PR 9+: Hilbert Metalogic (Benjamin)

**Stacks on**: PR 3, PR 8
**Files**: All `Metalogic/*.lean` files
**LOC**: ~2871 total — needs 5-6 PRs of ~500 each
**Content**: Deduction theorem, MCS, Lindenbaum extension, strong soundness and
completeness for MPL/IPL/CPL via canonical models.
**Why Benjamin**: Only he has this. No overlap.
**Suggested split**:
- PR 9a: `DeductionTheorem.lean` + `MCS.lean` (~372)
- PR 9b: `MinSoundness.lean` + `MinLindenbaum.lean` (~539 — tight)
- PR 9c: `MinStrongCompleteness.lean` (~337)
- PR 9d: `IntSoundness.lean` + `IntLindenbaum.lean` (~626 — needs trimming)
- PR 9e: `IntStrongCompleteness.lean` (~342)
- PR 9f: `Soundness.lean` + `StrongCompleteness.lean` (~655 — tight)

### PR 10+: ND Equivalence (Benjamin)

**Stacks on**: PR 9
**Files**: `NaturalDeduction/Equivalence.lean`, `FromHilbert.lean`,
`HilbertDerivedRules.lean`, `DerivedRules.lean`
**LOC**: ~1440 total — needs 3 PRs
**Content**: Hilbert ↔ ND equivalence, derived rules for both systems.

### Parallel Track: SAT/DPLL (Matthew, independent)

**Stacks on**: PR 2 (only needs `BoolEvaluate`)
**Content**: Tseitin transformation, CNF, DPLL decision procedure.
**Why Matthew**: Already underway. Independent of the algebraic semantics stack.

## 5. Open Questions for Zulip

1. **`imp` vs `impl`**: PR #648 uses `imp`; Thomas and Matthew use `impl`. Needs a
   community decision before further PRs.

2. **Lindenbaum PR size**: The Lindenbaum algebra (426 LOC) + soundness (264 LOC) is
   690 LOC together. Split into two PRs, or accept one larger PR since they're a
   natural unit?

3. **`v ⊨ T` notation**: Should the theory-parametric validity notation go into
   PR 2 (definitions) or PR 7 (Thomas's notation PR)? If PR 2, should Benjamin
   or Thomas write it?

4. **Kripke frame order**: `Preorder` (more general) vs `PartialOrder` (Thomas's
   choice, matches Mathlib's `PartialOrder` on Lindenbaum quotient)?

5. **Two routes to Kripke completeness**: Benjamin's direct canonical model vs
   Thomas's algebraic-to-Kripke functor. Both are valuable. Should they coexist
   in separate files, or should one be primary?

6. **DM completion scope**: Matthew's `DedekindMacneille.lean` may be useful beyond
   propositional logic (it's a general lattice-theoretic construction). Should it
   live under `Foundations/` rather than `Semantics/Algebra/`?
