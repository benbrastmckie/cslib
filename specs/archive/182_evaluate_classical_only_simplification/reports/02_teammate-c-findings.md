# Conservative Extension Proof Strategy

## Task 182 — Teammate C: Proof Strategy, Infrastructure, and Implementation Path

### 1. Precise Definition in CSLib's Framework

**Conservative extension** for task 182 means: if a propositional formula phi is derivable in the upper system (Modal K, Temporal BX, or Bimodal F), then phi was already derivable in Classical Propositional Logic (CPL).

The exact types involved for the Modal case:

```lean
-- Propositional side
PL.Proposition Atom                           -- formula type (5 constructors: atom, bot, imp, and, or)
PL.PropositionalAxiom : PL.Proposition Atom -> Prop  -- 10 axiom constructors
PL.Derivable : (PL.Proposition Atom -> Prop) -> PL.Proposition Atom -> Prop
  -- = Nonempty (DerivationTree Axioms [] phi)
PL.Evaluate : Valuation Atom -> PL.Proposition Atom -> Prop
PL.Tautology : PL.Proposition Atom -> Prop    -- forall v, Evaluate v phi

-- Modal side
Modal.Proposition Atom                         -- formula type (6 constructors: atom, bot, imp, and, or, box)
Modal.KAxiom : Modal.Proposition Atom -> Prop  -- 11 axiom constructors (10 prop + modalK)
Modal.Derivable : (Modal.Proposition Atom -> Prop) -> Modal.Proposition Atom -> Prop
  -- = Nonempty (DerivationTree Axioms [] phi)
Modal.Satisfies : Model World Atom -> World -> Proposition Atom -> Prop
Modal.Model World Atom := { r : World -> World -> Prop, v : World -> Atom -> Prop }

-- Embedding
PL.Proposition.toModal : PL.Proposition Atom -> Modal.Proposition Atom
  -- maps atom->atom, bot->bot, imp->imp, and->and, or->or (constructor-to-constructor)
```

The conservative extension theorem for Modal K:

```lean
theorem modal_conservative_extension (phi : PL.Proposition Atom) :
    Modal.Derivable (@Modal.KAxiom Atom) phi.toModal ->
    PL.Derivable PL.PropositionalAxiom phi
```

### 2. Existing Infrastructure

#### 2.1 Propositional Layer (COMPLETE)

| Component | Location | Status |
|-----------|----------|--------|
| `PL.Evaluate` | `Propositional/Semantics/Basic.lean` | Complete |
| `PL.Tautology` | `Propositional/Semantics/Basic.lean` | Complete |
| `prop_axiom_sound` | `Propositional/Metalogic/Soundness.lean` | Complete |
| `soundness_tautology` | `Propositional/Metalogic/Soundness.lean` | Complete: `Derivable PropositionalAxiom phi -> Tautology phi` |
| `prop_completeness` | `Propositional/Metalogic/Completeness.lean` | Complete: `Tautology phi -> Derivable PropositionalAxiom phi` |
| `completeness_iff_tautology` | `Propositional/Metalogic/Completeness.lean` | Complete: biconditional |

Key fact: **CPL completeness is fully proven.** This is one of the two essential legs.

#### 2.2 Modal K Soundness (COMPLETE)

| Component | Location | Status |
|-----------|----------|--------|
| `k_axiom_sound` | `Modal/Metalogic/Systems/K/Soundness.lean` | Complete |
| `k_soundness_derivable` | `Modal/Metalogic/Systems/K/Soundness.lean` | Complete: `Derivable KAxiom phi -> forall m w, Satisfies m w phi` |
| Parameterized soundness | `Modal/Metalogic/Soundness.lean` | Complete |

Key fact: **K soundness is fully proven.** This is the other essential leg.

#### 2.3 Semantic Bridge (COMPLETE)

| Component | Location | Status |
|-----------|----------|--------|
| `modal_satisfies_toModal_iff_evaluate` | `Modal/FromPropositional.lean` | Complete: `Satisfies m w phi.toModal <-> Evaluate (m.v w) phi` |
| `tautology_iff_toModal_valid` | `Modal/FromPropositional.lean` | Complete: `Tautology phi <-> forall World m w, Satisfies m w phi.toModal` |
| `toModal_valid_implies_tautology` | `Modal/FromPropositional.lean` | Complete |
| `tautology_toModal_valid` | `Modal/FromPropositional.lean` | Complete |

Key fact: **The semantic bridge is fully proven.** The bridge uses a single-world model with empty accessibility relation to reduce modal validity to propositional tautology.

#### 2.4 Temporal Embedding (PARTIAL)

| Component | Location | Status |
|-----------|----------|--------|
| `PL.Proposition.toTemporal` | `Temporal/FromPropositional.lean` | Complete (structural embedding) |
| `toTemporal` simp lemmas | `Temporal/FromPropositional.lean` | Complete |
| Semantic bridge | -- | **MISSING**: No `temporal_satisfies_toTemporal_iff_evaluate` lemma exists |
| `soundness_thderivable` | `Temporal/Metalogic/Soundness.lean` | Complete: `ThDerivable phi -> forall D M t, Satisfies M t phi` |

#### 2.5 Bimodal Embedding (PARTIAL)

| Component | Location | Status |
|-----------|----------|--------|
| `PL.Proposition.toBimodal` | `Bimodal/Embedding/PropositionalEmbedding.lean` | Complete (structural embedding) |
| Semantic bridge | -- | **MISSING**: No `truthAt_toBimodal_iff_evaluate` lemma exists |
| Bimodal soundness | -- | Uses `truthAt` rather than `Satisfies` (different semantic structure) |

#### 2.6 Existing Bimodal Conservative Extension (DIFFERENT SCOPE)

The existing `Bimodal/Metalogic/ConservativeExtension/` directory proves that the **extended** Bimodal system F+ (with a fresh irreflexivity atom) is a conservative extension of the **base** Bimodal system F. This is a purely syntactic proof-theoretic result using substitution and lifting. It does **not** prove conservativity over CPL. It is structurally unrelated to what task 182 needs but demonstrates an alternative (purely syntactic) approach to conservative extension.

### 3. Proof Strategy

#### 3.1 Modal K Conservative Extension (PRIMARY)

The proof chain:

```
Modal.Derivable KAxiom (phi.toModal)
  --[k_soundness_derivable]--> forall World m w, Satisfies m w (phi.toModal)
  --[toModal_valid_implies_tautology]--> PL.Tautology phi
  --[prop_completeness]--> PL.Derivable PropositionalAxiom phi
```

**Every step in this chain is already proven.** The conservative extension theorem for Modal K is a 3-line composition.

```lean
theorem modal_conservative_extension (phi : PL.Proposition Atom) :
    Modal.Derivable (@Modal.KAxiom Atom) phi.toModal ->
    PL.Derivable PL.PropositionalAxiom phi := by
  intro h_deriv
  apply prop_completeness
  exact toModal_valid_implies_tautology (fun World m w => k_soundness_derivable h_deriv m w)
```

**Important type-theoretic subtlety**: The `k_soundness_derivable` result produces `Satisfies m w phi` where `phi : Modal.Proposition Atom`, but `toModal_valid_implies_tautology` expects the hypothesis quantified over `(World : Type)` not `(World : Type*)`. Need to check universe compatibility. Looking at the signatures:

- `k_soundness_derivable` has `{World : Type*}` (universe polymorphic)
- `toModal_valid_implies_tautology` expects `forall (World : Type)` (universe 0)

This may require a small universe adjustment. The single-world model construction in `toModal_valid_implies_tautology` uses `Unit`, which is `Type 0`. But `k_soundness_derivable` can be instantiated at any universe including 0. So the composition should work: instantiate `k_soundness_derivable` at `Type` worlds.

**Estimated complexity**: 5-15 lines for the theorem statement and proof.

#### 3.2 Temporal BX Conservative Extension

For Temporal, we need:

```
Temporal.ThDerivable (phi.toTemporal)
  --[soundness_thderivable]--> forall D M t, Temporal.Satisfies M t (phi.toTemporal)
  --[NEW: temporal_toTemporal_valid_implies_tautology]--> PL.Tautology phi
  --[prop_completeness]--> PL.Derivable PropositionalAxiom phi
```

The missing piece is the **semantic bridge lemma** for Temporal:

```lean
-- NEEDS PROOF: Bridge between temporal satisfaction and propositional evaluation
theorem temporal_satisfies_toTemporal_iff_evaluate
    {D : Type*} [LinearOrder D]
    (M : TemporalModel D Atom) (t : D)
    (phi : PL.Proposition Atom) :
    Temporal.Satisfies M t phi.toTemporal <-> PL.Evaluate (M.valuation t) phi
```

This is straightforward by structural induction on `phi`. The `toTemporal` embedding never introduces `untl` or `snce`, so the temporal operators do not appear. Each case is:
- `atom`: both reduce to `M.valuation t p`
- `bot`: both are `False`
- `imp`: both are material conditional (inductive step)
- `and`: both are conjunction (inductive step)
- `or`: both are disjunction (inductive step)

Then the conservative extension follows by constructing a single-point temporal model:

```lean
-- NEEDS PROOF: Temporal validity implies tautology
theorem toTemporal_valid_implies_tautology
    (h : forall (D : Type) [LinearOrder D] [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Temporal.Satisfies M t phi.toTemporal) :
    PL.Tautology phi := by
  intro v
  -- Use Integer line as the temporal domain
  let M : TemporalModel Int Atom := { valuation := fun _ => v }
  exact (temporal_satisfies_toTemporal_iff_evaluate M 0 phi).mp (h Int M 0)
```

Note: The temporal model uses a constant valuation (same at every time point). This requires `Int` which is a `LinearOrder` with `NoMaxOrder` and `NoMinOrder`. The construction is clean because `toTemporal` never introduces temporal operators.

**Estimated complexity**: 30-50 lines total (semantic bridge + validity-implies-tautology + conservative extension theorem).

#### 3.3 Bimodal Conservative Extension

For Bimodal, the situation is more complex because:

1. The Bimodal semantic structure uses `truthAt` with task models, world histories, and domains -- significantly more complex than Modal/Temporal.
2. There is no straightforward "single-point model" construction because the bimodal semantics requires histories with domain membership.

**Two possible approaches**:

**Approach A: Route through Modal or Temporal (RECOMMENDED)**

Since Bimodal includes both Modal and Temporal as sub-logics, and we can already prove conservativity of those over CPL, we could:

1. Show that any Bimodal derivation of `phi.toBimodal` (where phi has no box/untl/snce) can be projected to a Modal derivation of `phi.toModal` (using the modal embedding).
2. Then use the Modal conservative extension.

This requires a **syntactic lifting theorem**: if the Bimodal system derives a formula in the propositional fragment, that derivation can be projected to the Modal sub-system. This is structurally similar to the existing `lift_derivation_qfree` in the ConservativeExtension directory.

**Approach B: Direct semantic proof**

Build a bimodal semantic bridge `truthAt_toBimodal_iff_evaluate` and construct a single-point task model. This is possible but involves more overhead (constructing a valid TaskFrame, WorldHistory, etc.).

**Recommendation**: Approach A is cleaner and reuses more infrastructure. However, it requires understanding the relationship between Bimodal, Modal, and Temporal axiom systems. The Bimodal axiom set subsumes both Modal and Temporal axioms.

**Estimated complexity**: 80-150 lines (syntactic lifting is non-trivial).

### 4. Post-Revert Considerations

After the revert (removing `and`/`or` constructors from upper layers), the proof strategy **simplifies**:

- The `toModal` embedding will map `PL.and` and `PL.or` (primitive in Propositional) to `Modal.Formula.and` and `Modal.Formula.or` (abbreviations via Lukasiewicz encoding in Modal). This is fine -- the semantic bridge lemma still works because the abbreviation has the same denotation.
- The semantic bridge lemma `modal_satisfies_toModal_iff_evaluate` will need 2 extra cases (for `and` and `or`) that unfold the abbreviation and use the fact that `Satisfies m w (neg (imp phi (neg psi))) <-> Satisfies m w phi /\ Satisfies m w psi` in classical models (which follows from `by_contra`).
- Alternatively, if `and`/`or` remain as abbreviations in Modal, the `Satisfies` function won't have explicit `and`/`or` cases -- they reduce through `imp`/`bot`. So the semantic bridge may become even simpler (no `and`/`or` cases needed; they unfold to `imp`/`bot` automatically via the abbreviation).

**Key insight**: After the revert, `Modal.Formula.and phi psi` unfolds to `neg (imp phi (neg psi))` which unfolds to `imp (imp phi (imp psi bot)) bot`. At the Satisfies level: `Satisfies m w (imp (imp phi (imp psi bot)) bot)` which (in classical models with `by_contra`) is equivalent to `Satisfies m w phi /\ Satisfies m w psi`. The bridge lemma needs to show this equivalence.

### 5. Key Lemmas Needed

#### For Modal Conservative Extension (5-15 lines)

| Lemma | Status | Lines |
|-------|--------|-------|
| `modal_conservative_extension` | New (composition of existing results) | 5-10 |

Everything else already exists.

#### For Temporal Conservative Extension (30-50 lines)

| Lemma | Status | Lines |
|-------|--------|-------|
| `temporal_satisfies_toTemporal_iff_evaluate` | New (semantic bridge) | 15-20 |
| `toTemporal_valid_implies_tautology` | New (single-point model) | 10-15 |
| `temporal_conservative_extension` | New (composition) | 5-10 |

#### For Bimodal Conservative Extension (80-150 lines)

| Lemma | Status | Lines |
|-------|--------|-------|
| Approach A: syntactic projection from Bimodal to Modal | New | 50-100 |
| `bimodal_conservative_extension` | New (composition or projection) | 10-20 |
| OR Approach B: `bimodal_truthAt_toBimodal_iff_evaluate` | New | 30-50 |
| OR Approach B: single-point task model construction | New | 30-50 |

### 6. Complexity Estimate

| Layer | Lines of New Code | Difficulty | Dependencies |
|-------|-------------------|------------|-------------|
| Modal K | 5-15 | Trivial (composition) | All infrastructure exists |
| Temporal BX | 30-50 | Easy (standard induction) | Needs semantic bridge |
| Bimodal F | 80-150 | Moderate (syntactic or semantic) | Most complex; choose approach |
| **Total** | **115-215** | | |

This is a **medium-sized development** -- closer to 150 lines than 500, assuming the revert has already been completed (so `and`/`or` are abbreviations).

### 7. Proof Strategy Summary

The overarching strategy is **Soundness + Semantic Bridge + Completeness**:

```
Upper-layer Derivability
    --[Soundness]--> Upper-layer Validity (over all models)
    --[Semantic Bridge]--> Propositional Tautology (via single-point model)
    --[Completeness]--> CPL Derivability
```

For Modal K, all three steps exist. For Temporal, step 2 needs a new lemma. For Bimodal, the approach depends on whether we go semantic (direct) or syntactic (projection to Modal).

### 8. Implementation Ordering

Recommended phase ordering:

1. **Phase 1**: Modal conservative extension (trivial composition, validates approach)
2. **Phase 2**: Temporal semantic bridge + conservative extension
3. **Phase 3**: Bimodal conservative extension (most complex, may need design decision)

Phase 1 can be done independently of the revert. Phases 2 and 3 should wait until after the revert is complete, since the `toTemporal` and `toBimodal` embeddings will change (mapping `PL.and`/`PL.or` to abbreviations instead of constructors).

### 9. Universe Issues

The key universe concern: `k_soundness_derivable` uses `{World : Type*}` while `toModal_valid_implies_tautology` expects `(World : Type)`. This should not be a problem because:

1. `k_soundness_derivable` can be instantiated at `Type 0 = Type`
2. The single-world model construction uses `Unit : Type`
3. Lean 4 handles universe instantiation smoothly here

If universe issues arise, the fix is to make `toModal_valid_implies_tautology` universe-polymorphic (change `Type` to `Type*`), or instantiate `k_soundness_derivable` explicitly at universe 0.

### 10. Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|------------|------------|
| Universe mismatch | Low | Explicit universe annotation |
| Bimodal semantic complexity | Medium | Use syntactic projection (Approach A) instead |
| Post-revert abbreviation unfolding | Low | `simp` + `unfold` handle abbreviation cases |
| Temporal model construction (`Int`) | Low | `Int` is a `LinearOrder` with `NoMaxOrder`/`NoMinOrder` in Mathlib |
| Proof-theoretic projection for Bimodal | Medium | Could defer Bimodal to a follow-up if complex |
