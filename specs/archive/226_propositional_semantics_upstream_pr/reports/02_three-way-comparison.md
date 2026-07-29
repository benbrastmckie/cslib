# Research Report: Three-Way Comparison of Propositional Semantics Implementations

**Task 226**: propositional_semantics_upstream_pr
**Session**: sess_1781736993_cab15d
**Date**: 2026-06-17

## 1. Current Implementation Audit

### 1.1 Sorries

There is **one sorry** in the codebase, in `Semantics/Algebra/Conservative.lean:99`:

```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry
```

The docstring explicitly states this requires the Dedekind-MacNeille completion of the Lindenbaum algebra. This is the exact technique Matthew Doty has implemented in his fork.

### 1.2 Completeness Status by Logic Strength

| Logic | Semantics | Soundness | Completeness | Strong Completeness | Notes |
|-------|-----------|-----------|--------------|---------------------|-------|
| MPL | GHA (algebraic) | `min_alg_axiom_sound` | `MPL.alg_complete` | -- | ND-level, sorry-free |
| MPL | Kripke | `min_soundness` | `min_completeness` | `min_strong_completeness` | Hilbert-level, sorry-free |
| IPL | HA (algebraic) | `int_alg_axiom_sound` | `IPL.alg_complete` | -- | ND-level, sorry-free |
| IPL | Kripke | `int_soundness` | `int_completeness` | `int_strong_completeness` | Hilbert-level, sorry-free |
| CPL | BA (algebraic) | `prop_alg_axiom_sound` | `alg_complete_classical` | -- | ND-level, sorry-free |
| CPL | Bivalent | `prop_soundness` | `prop_completeness` | `prop_strong_completeness` | Hilbert-level, sorry-free |

All **18 major theorems** are sorry-free. The only sorry is the conservative extension result (deferred, not blocking).

### 1.3 File Structure and LOC

| File | LOC | Content |
|------|-----|---------|
| `Semantics/Algebra.lean` | 145 | `AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid`, `AlgTValid` |
| `Semantics/Algebra/Soundness.lean` | 264 | Three-tier axiom soundness + derivation-level soundness |
| `Semantics/Algebra/Lindenbaum.lean` | 426 | Lindenbaum quotient GHA/HA/BA instances |
| `Semantics/Algebra/Completeness.lean` | 242 | Algebraic completeness via canonical valuation |
| `Semantics/Algebra/Bridge.lean` | 84 | `propEvaluateEq`, `boolEvaluateEq` |
| `Semantics/Algebra/Conservative.lean` | 101 | `IsBotFree`, validity subsumption, conservative extension (sorry) |
| `Semantics/Bool.lean` | 149 | `Evaluate`, `BoolEvaluate`, bridge lemmas |
| `Semantics/Kripke.lean` | 170 | `IForces`, `KripkeModel`, `IValid`, `MValid` |
| `Semantics/SemanticConsequence.lean` | 180 | `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails` |
| **Total** | **1761** | |

The Metalogic/ directory (Hilbert-level strong completeness) adds another ~1700 LOC across 10 files, all sorry-free.

## 2. Three-Way Comparison

### 2.1 Fundamental Design Divergence: `Proposition` Type

This is the most significant structural difference across the three implementations:

| Aspect | Our Implementation | Thomas Waring | Matthew Doty |
|--------|-------------------|---------------|--------------|
| `bot` in `Proposition` | **Primitive constructor** `.bot` | **Not a constructor**; `bot` is `atom ⊥` via `[Bot Atom]` | Same as Thomas |
| `Atom` constraint | None (`Type u`) | Requires `[Bot Atom]` for IPL/CPL | Same as Thomas |
| Connective name | `.imp` | `.impl` | `.impl` |
| `top` definition | `.imp .bot .bot` | `.impl (.atom default) (.atom default)` via `[Inhabited Atom]` | Same as Thomas |
| Monad | `pure := .atom` | `pure := .atom` | Same |

**Impact**: Our `AlgEvaluate` needs an explicit `bot_val : H` parameter because `bot` is a primitive constructor that must map somewhere in a GHA (which has no canonical bottom). Thomas's `Valuation.interp` has no bot case -- `bot` is just `atom ⊥`, so the valuation `v : Atom -> H` handles it via `v ⊥`. When `[Bot Atom]` is available and `v ⊥ = ⊥` (in HA), this gives the same semantics as our `bot_val = ⊥`.

**Our approach advantages**:
- No extra typeclass constraint on `Atom` for basic propositional logic
- Explicit separation of logical constants from atomic propositions
- `bot_val` parameter makes the GHA/HA/BA hierarchy cleanly visible

**Thomas's approach advantages**:
- Simpler evaluator (no extra parameter)
- `v ⊥ = ⊥` condition is a natural hypothesis for IPL validity
- `[Bot Atom]` is lightweight and composes well with `[Inhabited Atom]`

### 2.2 Evaluation Function Signatures

| Implementation | Function | Signature | Bot Handling |
|---------------|----------|-----------|--------------|
| Ours | `AlgEvaluate` | `(v : Atom -> H) (bot_val : H) : Proposition Atom -> H` | `bot_val` parameter |
| Thomas | `Valuation.interp` | `(v : Atom -> H) : Proposition Atom -> H` | `v ⊥` (atom lookup) |
| Matthew | Same as Thomas | Same as Thomas | Same as Thomas |

Thomas's evaluator is a `CoeFun` instance (`v⟦A⟧` notation), which is cleaner syntactically. Our approach is a plain function.

### 2.3 Validity Predicates

| Predicate | Ours | Thomas |
|-----------|------|--------|
| GHA valid (MPL) | `GHAValid φ := ∀ H [GHA H] v bot_val, AlgEvaluate v bot_val φ = ⊤` | `v ⊨ MPL` (theory validity) |
| HA valid (IPL) | `HAValid φ := ∀ H [HA H] v, AlgEvaluate v ⊥ φ = ⊤` | `v ⊥ = ⊥ -> v ⊨ A` |
| BA valid (CPL) | `BAValid φ := ∀ H [BA H] v, AlgEvaluate v ⊥ φ = ⊤` | `v ⊥ = ⊥ -> v ⊨ A` (over BA) |
| Theory valid | `AlgTValid T v bot_val := ∀ B ∈ T, AlgEvaluate v bot_val B = ⊤` | `v ⊨ T := ∀ A ∈ T, v⟦A⟧ = ⊤` |

Thomas's `v ⊨ T` pattern is more general: validity is parametric in the theory, so soundness and completeness are one theorem each with `T` as parameter. Our approach defines separate `GHAValid`/`HAValid`/`BAValid` predicates.

### 2.4 Completeness Theorems

| Theorem | Ours | Thomas | Matthew |
|---------|------|--------|---------|
| General | `Theory.alg_complete` | `Theory.complete` | `Theory.complete` (with DM completion) |
| MPL | `MPL.alg_complete` | `MPL.complete` | `MPL.complete` (HA strengthening via DM) |
| IPL | `IPL.alg_complete` | `IPL.complete` | `IPL.complete` |
| CPL | `alg_complete_classical` | `CPL.complete` | `CPL.complete` |

**Key difference in Thomas (kripke branch) vs Matthew (488309e)**:

Thomas's `Theory.complete` in the kripke branch states:
```lean
DerivableIn T A ↔ ∀ {H : Type u} [GeneralizedHeytingAlgebra H]
    {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

Matthew's `Theory.complete` strengthens this to:
```lean
DerivableIn T A ↔ ∀ {H : Type u} [HeytingAlgebra H]
    {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

The strengthening from GHA to HA is achieved via the **Dedekind-MacNeille completion**: Matthew's `DedekindMacneille.lean` provides a completion that turns the GHA Lindenbaum quotient into a HA while preserving the evaluation (using `Theory.canonicalVDM` and `Theory.canonicalVDM_spec`).

This is significant because:
- The GHA quotient is NOT a Heyting algebra in general (no canonical `⊥`)
- The Dedekind-MacNeille completion adds a `⊥` and gives a `HeytingAlgebra` instance
- The embedding preserves `⊓`, `⊔`, `⇨` so evaluation is preserved
- This enables `MPL.complete` to quantify over `HeytingAlgebra` rather than `GHA`

### 2.5 Conservative Extension

| Implementation | Approach |
|---------------|----------|
| Ours | Stated but `sorry` -- notes "requires Dedekind-MacNeille completion" |
| Thomas (kripke) | Not attempted in Heyting.lean |
| Matthew | Has `DedekindMacneille.lean` providing the infrastructure; `Theory.complete` implicitly gives this |

Matthew's DM completion is the missing piece for our `ipl_conservative_over_mpl` sorry.

### 2.6 Kripke Semantics

| Aspect | Ours | Thomas |
|--------|------|--------|
| Structure | `KripkeModel` record + standalone `IForces` | `KripkeModel` structure with `Forces` method |
| Preorder vs PartialOrder | `Preorder` | `PartialOrder` |
| Bot forcing | `botForces : World -> Prop` in model | Not in model; derived from algebra |
| Completeness route | Direct canonical model (prime theories) | Via algebraic semantics (prime filters) |

Thomas's Kripke completeness goes through the algebraic semantics: he constructs a Kripke model from prime filters of a GHA (`KripkeModel.ofHeyting`), proves that forcing agrees with algebra membership (`ofHeyting_forces_iff`), and derives Kripke completeness from algebraic completeness (`KripkeModel.complete`).

Our approach is the traditional direct canonical model construction using maximally consistent sets (for CPL) and prime theories (for MPL/IPL).

### 2.7 Additional Features in Thomas's Development

Thomas has several features we lack:
- `Proposition.flip` / `derivationFlip` for classical two-valued completeness
- `GeneralizedHeytingHom.map_interpret` for homomorphism preservation
- `Theory.Extension.toGeneralizedHeytingHom` for theory extension morphisms
- `KripkeModel.disj` for disjoint union of Kripke models
- `KripkeModel.restrict` and `restrict_forces_iff_of_isUpperSet`
- Separate `Hom` section for GHA homomorphism theory

### 2.8 Additional Features in Matthew's Development

Matthew adds:
- `DedekindMacneille.lean` -- full Dedekind-MacNeille completion with `CompleteLattice`, `HeytingAlgebra`, and `OrderEmbedding` instances (attributed to Yijun Yuan)
- `Theory.canonicalVDM` -- canonical valuation into the DM completion
- Strengthened `Theory.complete` quantifying over `HeytingAlgebra` instead of `GHA`

## 3. Coordination Strategy

### 3.1 The `bot` Design Decision

This is the central question for coordination. Three options:

**Option A: Keep our `bot` primitive** (current state). Our `AlgEvaluate` with explicit `bot_val` works but differs from Thomas/Matthew's evaluator. We would need:
- A bridge showing our `AlgEvaluate v bot_val` agrees with Thomas's `v.interp` when `bot_val = v ⊥`
- Agreement from Thomas/Matthew that both representations can coexist

**Option B: Switch to Thomas's bot-as-atom** (`[Bot Atom]`). This would require:
- Rewriting `Proposition` to remove the `bot` constructor (breaking change)
- Rewriting all evaluation functions, soundness/completeness proofs
- Very large refactor (~3500 LOC affected)

**Option C: Coordinate on an adapter layer**. Keep both `Proposition` definitions during transition, with a mapping between them. This is complex and temporary.

**Recommendation**: Option A is the pragmatic choice. Our `bot`-as-primitive is already merged in PR #648. Thomas and Matthew's work builds on their own fork which has `bot`-as-atom. The upstream PR should use our `Proposition` type (with `bot` primitive) and our `AlgEvaluate` with `bot_val`. Thomas's GHA soundness proof approach (the `v ⊨ T` pattern) can be adapted to our evaluator. The `bot_val` parameter actually adds expressiveness -- it makes the GHA/HA/BA hierarchy visible in the type signature.

### 3.2 What Should Go Into the Semantics PR (~400-500 LOC)

Given that our Semantics/ directory already has 1761 LOC, the question is what subset is appropriate for a focused upstream PR that builds on PR #648.

**Core semantics (already implemented, ready for PR)**:
1. `Semantics/Algebra.lean` (145 LOC) -- `AlgEvaluate`, validity predicates, `AlgTValid`
2. `Semantics/Bool.lean` (149 LOC) -- `Evaluate`, `BoolEvaluate`, bridge lemmas
3. `Semantics/Algebra/Bridge.lean` (84 LOC) -- `propEvaluateEq`, `boolEvaluateEq`

**Subtotal**: 378 LOC -- fits within 400-500 LOC budget.

**Strong candidates if LOC budget permits**:
4. `Semantics/SemanticConsequence.lean` (180 LOC) -- `SetDerivable`, semantic consequence defs

**Should NOT go in this PR** (defer to subsequent metalogic PR):
- `Semantics/Algebra/Soundness.lean` (264 LOC) -- depends on proof system axioms
- `Semantics/Algebra/Lindenbaum.lean` (426 LOC) -- large, proof-heavy
- `Semantics/Algebra/Completeness.lean` (242 LOC) -- depends on Lindenbaum
- `Semantics/Algebra/Conservative.lean` (101 LOC) -- has sorry
- `Semantics/Kripke.lean` (170 LOC) -- depends on proof system for completeness
- All Metalogic/ files -- separate PR scope

### 3.3 Alignment with Collaborators

**Thomas Waring alignment**:
- Our `AlgEvaluate` is structurally similar to his `Valuation.interp` (same GHA operations)
- Our `AlgTValid` corresponds to his `v ⊨ T`
- Our `GHAValid`/`HAValid`/`BAValid` correspond to his tier-specific validity
- His `v ⊨ T` pattern is cleaner; we could adopt it in the PR description as the conceptual framework
- Key difference: our explicit `bot_val` vs his implicit `v ⊥`; both work but document the relationship

**Matthew Doty alignment**:
- Our `BoolEvaluate` serves the same purpose as his Bool instantiation of `Valuation.interp`
- Our `BoolEvaluate_eq_iff` bridge corresponds to what he needs for DPLL/SAT
- His Dedekind-MacNeille work would resolve our sorry in Conservative.lean
- We should reference his DM completion work as the path to the conservative extension theorem

### 3.4 Recommended PR Scope

**Files to include** (targeting 400-500 LOC):

1. `Semantics/Algebra.lean` -- Core AlgEvaluate + validity predicates (145 LOC)
2. `Semantics/Bool.lean` -- Bivalent + Boolean evaluators with bridges (149 LOC)
3. `Semantics/Algebra/Bridge.lean` -- AlgEvaluate-to-Evaluate/BoolEvaluate correspondence (84 LOC)

**Total: ~378 LOC** -- clean, self-contained, no sorry.

If the reviewer requests it, `SemanticConsequence.lean` (180 LOC) could be added, but it depends on the proof system `Derivation` type which may not be in scope yet.

### 3.5 PR Description Talking Points

The PR description should:
1. Reference the Zulip Propositional Logic thread discussion
2. Acknowledge Thomas Waring's GHA direction as the design basis
3. Explain the `bot_val` parameter design and how it relates to Thomas's `[Bot Atom]` approach
4. Note that `BoolEvaluate` accommodates Matthew Doty's DPLL/SAT needs
5. Note that soundness/completeness proofs are implemented locally but deferred to a subsequent PR
6. Reference the Dedekind-MacNeille completion path (Matthew's work) for the conservative extension

## 4. Open Questions for User

1. **PR stacking**: Is PR #648 merged yet? The semantics PR should stack on it.
2. **`impl` vs `imp`**: Our `Proposition` uses `.imp` while Thomas/Matthew use `.impl`. This is a naming convention question that should be settled.
3. **`Kripke.lean` inclusion**: The task description mentions possibly including Kripke semantics. At 170 LOC it fits the budget, but Kripke completeness depends on the proof system. Should the bare definitions go in without completeness?
4. **Lindenbaum algebra**: The Lindenbaum quotient construction (426 LOC) is arguably the most important piece for the community, but it exceeds the LOC budget alone. Should it be a separate PR?
5. **Conservative extension sorry**: Should we flag Matthew's DM completion as a known path to resolving this, or wait until coordination produces a concrete plan?

## 5. Summary of Findings

- The current implementation is in **excellent shape**: 18 major theorems sorry-free, only one sorry in a deferred conservative extension result
- The **fundamental design divergence** is `bot`-as-primitive (ours) vs `bot`-as-atom (Thomas/Matthew). Our approach is already upstream via PR #648; changing it would be a large breaking refactor
- **Thomas's `v ⊨ T` pattern** is cleaner than our separate validity predicates; we should document the correspondence
- **Matthew's Dedekind-MacNeille completion** resolves our only sorry; this should be acknowledged and referenced
- The **recommended PR scope** is Algebra.lean + Bool.lean + Bridge.lean at ~378 LOC -- clean, self-contained, no sorry, and provides the foundation both collaborators need
- **Thomas's Kripke completeness via prime filters** is an elegant alternative to our direct canonical model construction; both approaches are valid and could coexist
