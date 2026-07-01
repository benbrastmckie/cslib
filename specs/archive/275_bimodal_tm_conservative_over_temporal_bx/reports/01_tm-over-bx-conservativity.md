# Research Report: Bimodal TM Conservative over Temporal BX

**Task**: 275 -- bimodal_tm_conservative_over_temporal_bx
**Session**: sess_1782161605_f646ec_275
**Date**: 2026-06-22

## 1. Problem Statement

Prove that Bimodal TM is a conservative extension of Temporal BX for temporal formulas: if
`phi : Temporal.Formula Atom` and `phi.toBimodal` is TM-derivable (i.e.,
`Bimodal.Bimodal.ThDerivable phi.toBimodal`), then `phi` is BX-derivable (i.e.,
`Temporal.ThDerivable phi`).

The target theorem statement:

```lean
theorem bimodal_conservative_over_temporal
    [Infinite Atom] [DecidableEq Atom]
    {phi : Temporal.Formula Atom}
    (h : Bimodal.Bimodal.ThDerivable phi.toBimodal) :
    Temporal.ThDerivable phi
```

## 2. Structural Analysis

### 2.1 Formula Types

**Temporal.Formula** (5 constructors):
- `atom`, `bot`, `imp`, `untl`, `snce`

**Bimodal.Formula** (6 constructors):
- `atom`, `bot`, `imp`, `box`, `untl`, `snce`

The key difference: Bimodal adds `box` (modal necessity). The embedding
`Temporal.Formula.toBimodal` maps each temporal constructor to its bimodal counterpart
(identity on all 5 shared constructors).

### 2.2 Proof Systems

**Temporal BX** (6 inference rules):
1. `axiom` (26 axiom schemas: 4 propositional + 22 temporal)
2. `assumption`
3. `modus_ponens`
4. `temporal_necessitation` (Gphi from phi)
5. `temporal_duality` (swapTemporal)
6. `weakening`

**Bimodal TM** (7 inference rules):
1. `axiom` (42 axiom schemas: 4 prop + 5 modal + 22 temporal + 1 interaction + 5 uniformity + 2 prior + 1 Z1 + 2 density)
2. `assumption`
3. `modus_ponens`
4. `necessitation` (box phi from phi) -- EXTRA rule
5. `temporal_necessitation` (allFuture phi from phi)
6. `temporal_duality` (swapTemporal)
7. `weakening`

**Extra in TM over BX**:
- Inference rule: `necessitation` (modal box)
- Axioms: 5 S5 modal (modal_t, modal_4, modal_b, modal_5_collapse, modal_k_dist)
- Axiom: `modal_future` (box phi -> box(G phi))
- Axioms: 5 uniformity (discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd, discrete_box_necessity)
- Axioms: 2 prior (prior_UZ, prior_SZ)
- Axiom: z1

### 2.3 Frame Classes

Both systems define independent `FrameClass` types with constructors `.Base`, `.Dense`,
`.Discrete`. The conservativity result operates at `FrameClass.Base` level (since
`ThDerivable` = `Deriv [] phi` = `Nonempty (DerivationTree FrameClass.Base [] phi)`).

At `.Base` level:
- Temporal BX has 26 axioms (4 prop + 22 temporal)
- Bimodal TM has 37 axioms (4 prop + 5 modal + 22 temporal + 1 interaction + 5 uniformity)

## 3. Existing Infrastructure

### 3.1 The `toBimodal` Embedding

**File**: `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean`

```lean
def Temporal.Formula.toBimodal : Temporal.Formula Atom -> Bimodal.Formula Atom
  | .atom p => .atom p
  | .bot => .bot
  | .imp phi1 phi2 => .imp (phi1.toBimodal) (phi2.toBimodal)
  | .untl phi2 phi1 => .untl (phi2.toBimodal) (phi1.toBimodal)
  | .snce phi2 phi1 => .snce (phi2.toBimodal) (phi1.toBimodal)
```

Simp lemmas exist for all 5 constructors plus `neg`. The embedding is definitionally
identity on all constructors (just changes the type).

### 3.2 The Propositional Conservative Extension

**File**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`

This uses the **semantic approach**: construct a trivial TaskModel, prove that
`truthAt M Omega tau t phi.toBimodal <-> PL.Evaluate v phi` by structural induction,
combine with TM soundness and CPL completeness.

This approach works for propositional formulas because temporal/modal operators
contribute vacuously in the trivial model.

### 3.3 The Temporal Conservative Extension over CPL

**File**: `Cslib/Logics/Temporal/ConservativeExtension.lean`

Same semantic approach: construct a constant temporal model on Z, use temporal BX
soundness, apply semantic bridge lemma, conclude with CPL completeness.

### 3.4 The `lift_derivation_qfree` Infrastructure

**File**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean`

This is the **syntactic approach** infrastructure. It provides:

- `ExtFormula Atom`: Formula type with `Atom + Unit` atoms (adds a fresh atom `q`)
- `ExtDerivationTree`: Derivation trees over `ExtFormula`
- `embedFormula` / `embedDerivation`: Embed base formulas/derivations into Ext
- `substFormula`: Substitution sigma[q -> bot]
- `substDerivation`: Substitution preserves derivations in Ext
- `liftDerivationWith`: Combined lifting via fresh atom replacement + unembedding
- `lift_derivation_qfree`: Main theorem -- if `ExtDerivationTree fc (L.map embedFormula) (embedFormula phi)` then `Nonempty (DerivationTree fc L phi)`

**Critical observation**: `lift_derivation_qfree` operates entirely within the bimodal
language. Both input (`ExtDerivationTree`) and output (`DerivationTree`) use bimodal
formula types. It does NOT translate between bimodal and temporal derivations.

The infrastructure was designed for the **irreflexivity rule** (IRR) conservative
extension, where a bimodal derivation with an extra axiom (using a fresh atom `q`) is
projected back to a bimodal derivation without that axiom. It is not directly applicable
to the temporal conservativity problem.

## 4. Proof Strategy Analysis

### 4.1 Approach A: Semantic Bridge (Recommended)

**Idea**: Exploit soundness of TM and completeness of BX.

1. Assume `Bimodal.Bimodal.ThDerivable phi.toBimodal`.
2. By TM soundness, `phi.toBimodal` is valid in all bimodal task models (over any linear order).
3. Every temporal model can be extended to a bimodal task model (the temporal flow structure
   is already linear; add a trivial accessibility relation or use the universal relation for S5).
4. Therefore `phi.toBimodal` is true in every such extended model.
5. The semantic bridge lemma: for temporal formulas (no box), truth of `phi.toBimodal` in the
   task model reduces to truth of `phi` in the temporal model.
6. Therefore `phi` is valid in all temporal models.
7. By BX completeness, `phi` is BX-derivable.

**Key required lemma**: A semantic bridge showing that for box-free (temporal) formulas,
satisfaction of `phi.toBimodal` in any task model at any point is equivalent to satisfaction
of `phi` in the underlying temporal model.

**Feasibility**: HIGH. The semantic bridge lemma should be straightforward by structural
induction on `phi`, since `phi` has no `box` constructor and the embedding is identity on
all other constructors. The bimodal `truthAt` function and temporal `Satisfies` function
agree on atoms, bot, imp, untl, and snce (they both use the linear order structure).

**Prerequisites**:
- TM soundness: `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean` -- exists
- BX completeness: `Cslib/Logics/Temporal/Metalogic/Completeness.lean` -- exists
- Semantic bridge: NEW (but follows the established pattern from PropositionalConservativity.lean)

### 4.2 Approach B: Syntactic Derivation Translation

**Idea**: Directly translate a bimodal derivation tree into a temporal derivation tree.

1. Take a `Bimodal.DerivationTree FrameClass.Base [] phi.toBimodal`.
2. By induction on the derivation tree, translate each rule:
   - `axiom`: Map each bimodal axiom to a temporal axiom (for temporal axioms) or derive it
     in temporal BX (for modal/interaction/uniformity axioms). THIS IS THE HARD PART.
   - `modus_ponens`: Translate both subderivations, apply temporal MP.
   - `necessitation` (box phi): This rule applies to the empty context. If `phi` is
     box-free, `box phi` is NOT box-free, so this case should be impossible if the
     conclusion is box-free. But the derivation tree may use `box` internally.
   - `temporal_necessitation`, `temporal_duality`: Direct translation.
   - `weakening`: Direct translation.

**Problem**: The derivation tree may internally use `box` even if the final conclusion is
box-free. For example, `necessitation` followed by `modal_t` gives `box phi -> phi`, and
then `phi` follows. The intermediate steps involve non-temporal formulas.

**This makes the syntactic approach extremely difficult**, because:
- You cannot simply recurse on the derivation tree and translate node-by-node.
- You would need a sub-formula property or normal form theorem to ensure that box-free
  conclusions only need box-free derivations.
- Such a property essentially IS the conservativity result.

**Feasibility**: LOW without significant additional infrastructure (cut-elimination or
similar normalization results).

### 4.3 Approach C: Hybrid (Syntactic + Semantic)

**Idea**: Use the semantic bridge to establish the truth of `phi` in all temporal models,
then apply BX completeness.

This is essentially Approach A. The "hybrid" aspect would be if we could avoid full
completeness by using some syntactic translation for the temporal fragment. But since BX
completeness already exists, this adds complexity without benefit.

## 5. Detailed Plan for Approach A

### 5.1 The Semantic Bridge Lemma

The core new content needed. Given:
- A task model `M : TaskModel Atom F` over some `F : TaskFrame D` where `D` is a linear order
- The temporal model extracted from this task model

We need to show that for any `phi : Temporal.Formula Atom`:
```
truthAt M Omega tau t phi.toBimodal <-> Satisfies (extractTemporalModel M tau t) t phi
```

**Or more simply**: construct a temporal model from the task model's linear order and
valuation, and show satisfaction coincides.

The bimodal truth function uses:
- `truthAt M Omega tau t (.atom p)` uses the valuation at world state `tau(t)` and
  the task frame's accessibility
- `truthAt M Omega tau t (.untl ...)` uses the strict ordering on `D`
- `truthAt M Omega tau t (.snce ...)` uses the strict ordering on `D`
- `truthAt M Omega tau t (.box ...)` uses the accessibility relation

The temporal satisfaction function uses:
- `Satisfies M t (.atom p)` uses the valuation at time `t`
- `Satisfies M t (.untl ...)` uses the strict ordering on `D`
- `Satisfies M t (.snce ...)` uses the strict ordering on `D`

For box-free formulas, the box case never arises, so the agreement should be clean.

### 5.2 Model Extraction

We need a function that extracts a temporal model from a bimodal task model:

```lean
def extractTemporalModel (M : TaskModel Atom F) (tau : WorldHistory F) :
    TemporalModel D Atom :=
  { valuation := fun t p => M.valuation (tau.worldAt t) p }
```

(Or whatever the right extraction is, depending on how `truthAt` is defined.)

### 5.3 Proof Outline

```lean
theorem bimodal_conservative_over_temporal
    [Infinite Atom] [DecidableEq Atom]
    {phi : Temporal.Formula Atom}
    (h : Bimodal.Bimodal.ThDerivable phi.toBimodal) :
    Temporal.ThDerivable phi := by
  -- Step 1: Apply BX completeness (contrapositively if needed)
  apply completeness
  -- Step 2: Show phi is valid in all temporal models
  intro D _lo M t
  -- Step 3: Extend M to a task model
  let taskModel := extendToTaskModel M
  -- Step 4: By TM soundness, phi.toBimodal is true in taskModel
  have h_true := soundness ... h ...
  -- Step 5: By semantic bridge, phi is true in M
  exact (semantic_bridge ...).mp h_true
```

### 5.4 Dependencies to Check

Before implementing, verify:
1. **Bimodal soundness signature**: What exactly does `soundness` require? Need to check
   the exact statement in `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean`.
2. **Temporal completeness signature**: What exactly does `completeness` provide? It should
   give `ThDerivable phi` from `Valid phi`.
3. **Model compatibility**: Can we construct a bimodal task model from a temporal model?
   The temporal model provides a linear order `D` and a valuation `D -> Atom -> Prop`.
   A bimodal task model requires:
   - A `TaskFrame D` (linear order + accessibility relation + world states)
   - A valuation on world states
   - A world history (assignment of world states to time points)

## 6. Key Findings

### 6.1 What "Temporal Formulas" Means

There is no explicit `IsTemporal` predicate in CSLib. Instead, "temporal formulas" are
precisely the image of `Temporal.Formula.toBimodal`: bimodal formulas that use only
`{atom, bot, imp, untl, snce}` constructors and no `box`. This is structurally enforced
by the type: `Temporal.Formula Atom` simply does not have a `box` constructor.

### 6.2 The `lift_derivation_qfree` Infrastructure Is Not Directly Applicable

The lifting infrastructure in `ConservativeExtension/` was built for a different purpose:
projecting derivations that use an extended atom set back to the base atom set. It operates
entirely within the bimodal language and does not translate between bimodal and temporal
derivation trees.

### 6.3 The Semantic Approach Follows an Established Pattern

The existing `bimodal_conservative_extension` (over CPL) and `temporal_conservative_extension`
(over CPL) both use the semantic approach. The new theorem should follow the same pattern:
soundness + semantic bridge + completeness.

### 6.4 Frame Class Mismatch Is Manageable

The two `FrameClass` types are in different namespaces but structurally identical. The
mapping between them is trivial but must be handled explicitly.

## 7. Feasibility Assessment

**Overall**: FEASIBLE with the semantic approach (Approach A).

**Risk factors**:
- LOW: The semantic bridge lemma for box-free formulas follows by straightforward structural
  induction (5 cases, no box case)
- MEDIUM: Model extraction -- need to verify the exact signatures of `truthAt` and
  `Satisfies` and ensure they agree on temporal operators
- LOW: Soundness and completeness already exist
- MEDIUM: May need to construct a `WorldHistory` / `TaskFrame` from a temporal model,
  which involves some boilerplate

**Estimated implementation effort**: One implementation phase (~300-500 lines), following
the pattern of `PropositionalConservativity.lean`.

## 8. Detailed Semantic Analysis

### 8.1 Bimodal truthAt (exact definition)

```lean
def truthAt (M : TaskModel Atom F) (Omega : Set (WorldHistory F))
    (tau : WorldHistory F) (t : D) : Formula Atom -> Prop
  | Formula.atom p => exists (ht : tau.domain t), M.valuation (tau.states t ht) p
  | Formula.bot => False
  | Formula.imp phi psi => truthAt M Omega tau t phi -> truthAt M Omega tau t psi
  | Formula.box phi => forall (sigma : WorldHistory F), sigma in Omega ->
      truthAt M Omega sigma t phi
  | Formula.untl psi phi => exists s, t < s /\ truthAt M Omega tau s phi /\
      forall r, t < r -> r < s -> truthAt M Omega tau r psi
  | Formula.snce psi phi => exists s, s < t /\ truthAt M Omega tau s phi /\
      forall r, s < r -> r < t -> truthAt M Omega tau r psi
```

Requirements on `D`: `AddCommGroup D`, `LinearOrder D`, `IsOrderedAddMonoid D`.
Uses `TaskFrame D`, `TaskModel Atom F`, `WorldHistory F`, `Set (WorldHistory F)`.

### 8.2 Temporal Satisfies (exact definition)

```lean
def Satisfies (M : TemporalModel D Atom) (t : D) : Formula Atom -> Prop
  | .atom p => M.valuation t p
  | .bot => False
  | .imp phi psi => Satisfies M t phi -> Satisfies M t psi
  | .untl psi phi => exists s, t < s /\ Satisfies M s phi /\
      forall r, t < r -> r < s -> Satisfies M r psi
  | .snce psi phi => exists s, s < t /\ Satisfies M s phi /\
      forall r, s < r -> r < t -> Satisfies M r psi
```

Requirements on `D`: `LinearOrder D`.
Uses `TemporalModel D Atom` = `{ valuation : D -> Atom -> Prop }`.

### 8.3 Structural Agreement on Temporal Connectives

For `bot`, `imp`, `untl`, `snce`: the definitions are structurally identical modulo:
- Temporal uses `Satisfies M t phi` recursively
- Bimodal uses `truthAt M Omega tau t phi` recursively

For `atom`: they differ:
- Temporal: `M.valuation t p` (direct)
- Bimodal: `exists (ht : tau.domain t), M.valuation (tau.states t ht) p`
  (requires domain membership + world state extraction)

The `box` case does not arise for temporal formulas.

### 8.4 Semantic Bridge Strategy

To bridge between these, given a temporal model `(D, LinearOrder D, NoMaxOrder D,
NoMinOrder D, M_temp)`, we construct a bimodal task model:

1. **Time domain**: Use `Z` (integers) which has `AddCommGroup`, `LinearOrder`,
   `IsOrderedAddMonoid`, and `Nontrivial`.

   However, the temporal completeness theorem quantifies over arbitrary `D` with
   `LinearOrder D`, `Nontrivial D`, `NoMaxOrder D`, `NoMinOrder D`. We need to show
   validity at ALL such `D`. So we cannot fix `D = Z`.

   **Alternative**: For each temporal model `(D, M_temp)`, construct a task model on `D`.
   But `D` may not have `AddCommGroup`. The bimodal soundness requires `AddCommGroup D`.

   **Solution**: Use the existing pattern from `PropositionalConservativity.lean`:
   fix `D = Z` and construct ONE specific task model. TM soundness gives truth in that
   model. The semantic bridge gives `Evaluate v phi`. Then we use a DIFFERENT route to
   get temporal validity.

   Wait -- the completeness theorem for temporal BX requires validity over ALL serial
   linear orders, not just Z. Let me re-examine.

### 8.5 Proof Architecture (Revised)

The temporal completeness theorem states:
```lean
theorem completeness [Denumerable (Formula Atom)] {phi : Formula Atom}
    (h_valid : forall (D : Type) [LinearOrder D] [Nontrivial D]
      [NoMaxOrder D] [NoMinOrder D]
      (M : TemporalModel D Atom) (t : D), Satisfies M t phi) :
    Temporal.ThDerivable phi
```

So we need to show `Satisfies M t phi` for ALL `D` with the required properties and
ALL temporal models `M` and ALL times `t`.

The bimodal soundness theorem states:
```lean
theorem soundness (Gamma : Context Atom) (phi : Formula Atom)
    (d : DerivationTree FrameClass.Base Gamma phi)
    (D : Type) [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [Nontrivial D] (F : TaskFrame D) (M : TaskModel Atom F)
    (Omega : Set (WorldHistory F)) (h_sc : ShiftClosed Omega)
    (tau : WorldHistory F) (h_mem : tau in Omega) (t : D)
    (h_ctx : forall psi in Gamma, truthAt M Omega tau t psi) :
    truthAt M Omega tau t phi
```

**The gap**: Temporal completeness needs `LinearOrder D` (no `AddCommGroup`), while
bimodal soundness provides `truthAt` which needs `AddCommGroup D`. These don't directly
compose: we can't just take an arbitrary temporal model and extend it to a task model
because the temporal model's domain may lack `AddCommGroup`.

**Resolution**: Two approaches:

**Approach A1 (Direct semantic bridge on Z)**:
1. For any temporal model `M_temp` on `D` (with `LinearOrder`, `Nontrivial`, `NoMaxOrder`,
   `NoMinOrder`), construct a task model on `Z` (which has `AddCommGroup`).
2. Map the temporal model's valuation to a `Z`-indexed valuation.
3. Apply bimodal soundness on `Z`.
4. Extract temporal truth on `Z`.
5. This only gives validity on `Z`, not on arbitrary `D`. Insufficient for completeness.

**Approach A2 (Semantic bridge for each D with AddCommGroup)**:
1. Fix `D` with ALL the required properties (`LinearOrder`, `Nontrivial`, `NoMaxOrder`,
   `NoMinOrder`, `AddCommGroup`, `IsOrderedAddMonoid`).
2. For each temporal model `M_temp` on this `D`, construct a task model on `D`.
3. Apply bimodal soundness.
4. Semantic bridge gives temporal satisfaction.
5. But completeness needs validity on ALL D with `LinearOrder` etc., including D without
   `AddCommGroup`. So this is also insufficient.

**Approach A3 (Z is enough -- use temporal soundness on Z)**:
Actually, looking more carefully at the completeness proof, it constructs a countermodel
on a specific domain (a subtype of Q). The key question is: does the contrapositive
approach work if we can show validity on Z alone?

No -- completeness requires validity on ALL serial linear orders, not just Z.

**Approach A4 (Direct semantic bridge -- avoid soundness/completeness loop)**:

The most natural approach is:
1. From `Bimodal.ThDerivable phi.toBimodal`, extract the derivation tree `d`.
2. Construct a function that translates `Bimodal.DerivationTree` of a temporal formula
   into a `Temporal.DerivationTree`.
3. This is the syntactic approach (Approach B from section 4.2).

But we noted this is hard due to internal use of `box`.

**Approach A5 (Semantic bridge on Q via embedding)**:

Actually, re-reading the temporal completeness proof, it works on a `ChronicleSubtype`
which is a subtype of Q. Both Z and Q have `AddCommGroup`. The real question is whether
we can establish temporal validity from bimodal validity by choosing D appropriately.

Key insight: We need `Satisfies M t phi` for ALL `(D, LinearOrder, Nontrivial, NoMaxOrder,
NoMinOrder, M, t)`. For those `D` that ALSO have `AddCommGroup` and `IsOrderedAddMonoid`,
we can use the semantic bridge directly. For those that don't, we need another argument.

But actually: `Z` with the standard order satisfies ALL the required properties for
temporal completeness (LinearOrder, Nontrivial, NoMaxOrder, NoMinOrder). And `Z` also
has `AddCommGroup` and `IsOrderedAddMonoid`. So if we can show the result for Z, temporal
completeness gives us BX-derivability. BUT temporal completeness needs validity on ALL
such D, not just Z.

Wait -- actually the completeness theorem says "if phi is valid on ALL serial linear
orders then phi is derivable". The contrapositive is "if phi is not derivable then phi
is not valid on SOME serial linear order". So we need to show the HYPOTHESIS of
completeness, which is universal validity.

**Approach A6 (Model-theoretic transfer -- CORRECT approach)**:

For any `D` with `LinearOrder`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`, and any
temporal model `M_temp : TemporalModel D Atom`, and any `t : D`:

We need `Satisfies M_temp t phi`.

Since `phi` has no `box`, and `phi.toBimodal` is valid in TM (by soundness from the
derivation), we need a MODEL-THEORETIC transfer. This is the standard approach:

1. **Any temporal model can be viewed as a bimodal task model** by choosing a trivial
   task structure (single world state, trivial task relation). However, this requires
   `AddCommGroup D` which an arbitrary `D` may lack.

2. **Alternative: use the Lowenheim-Skolem-style argument.** For any temporal model on
   `D`, construct an elementarily equivalent temporal model on `Z` (or some `D'` with
   `AddCommGroup`). This is overkill and hard to formalize.

3. **Simplest correct approach: DIRECT SYNTACTIC TRANSLATION.**

### 8.6 Revised Recommendation: Syntactic Translation

After careful analysis of the semantic gap (bimodal soundness needs `AddCommGroup D` but
temporal completeness needs arbitrary `D`), the **syntactic approach** is actually the
cleanest path.

The key insight is that the problematic cases in the syntactic translation (Section 4.2)
CAN be handled if we carefully analyze what bimodal axioms and rules are compatible with
the temporal language:

**Temporal-compatible axioms** (axioms that, instantiated with temporal formulas, produce
temporal formulas):
- All 4 propositional axioms (imp_k, imp_s, efq, peirce) -- YES
- All 22 temporal axioms (serial_future/past, mono_until/since, etc.) -- YES
- 5 S5 modal axioms -- produce formulas with `box`, NOT temporal
- `modal_future` -- produces formulas with `box`, NOT temporal
- 5 uniformity axioms -- produce TEMPORAL formulas (they use `untl bot top`, etc.)

**Temporal-compatible rules**:
- `modus_ponens` -- preserves temporal formulas if both premises are temporal
- `temporal_necessitation` -- output `allFuture phi` is temporal if `phi` is temporal
- `temporal_duality` -- output `swapTemporal phi` is temporal if `phi` is temporal
- `weakening` -- preserves temporality
- `necessitation` -- output `box phi` is NOT temporal

The fundamental obstacle remains: the derivation may use `box` internally even though
the conclusion is box-free.

**However**: We can use a SEMANTIC argument that works despite the AddCommGroup gap:

### 8.7 Correct Semantic Approach (Final)

Key realization: We do NOT need to match ARBITRARY D. We can use the specific structure
of the temporal completeness proof contrapositive-style:

```
phi is TM-derivable
=> phi.toBimodal is TM-derivable (by construction)
=> phi.toBimodal is valid in all task models on Z (by TM soundness on Z)
=> phi is valid in all temporal models on Z (by semantic bridge on Z)
=> phi is BX-derivable (if phi were not derivable, completeness would give
   a countermodel on some D, but we can embed that countermodel into a
   task model... WAIT, the countermodel D may not have AddCommGroup)
```

Actually, let me look at this differently. Temporal completeness is proved contrapositively:
if phi is not derivable, a countermodel is built on `ChronicleSubtype` which is a subtype
of Q. Both Q and subtypes of Q CAN have `AddCommGroup` structure (Q certainly does).

So the question becomes: does `ChronicleSubtype` (the specific countermodel domain) support
`AddCommGroup`? If so, we can embed the temporal countermodel into a task model and get a
contradiction.

**Simplest correct approach**: Rather than tracing through the completeness proof, use the
following clean argument:

1. `phi.toBimodal` is TM-derivable, hence valid in all task models.
2. In particular, for any temporal model on Z, construct the trivial task model on Z
   (single world state, valuation = M.valuation, universal domain).
3. `truthAt` of `phi.toBimodal` in this model equals `Satisfies M t phi`.
4. Hence `phi` is valid on Z.
5. Now argue: if phi is BX-valid on ALL serial linear orders (not just Z), it is
   BX-derivable. We have it on Z. Is Z-validity enough?

**Z-validity is NOT enough for completeness** in general. However, we can strengthen:

For EVERY D with `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, `Nontrivial`,
`NoMaxOrder`, `NoMinOrder`, and every temporal model on D, construct the trivial task
model and get phi valid. This covers Z, Q, R (as additive groups).

The temporal completeness proof constructs its countermodel on `ChronicleSubtype M hM_mcs`
which is a subtype of Q. Q has `AddCommGroup`, but the SUBTYPE inherits only `LinearOrder`.
We would need to check whether this subtype also inherits `AddCommGroup`.

**Ultimate recommendation**: Given the complexity of matching domain requirements, the
cleanest implementable approach is:

**Approach B (Syntactic + Normal Form)**: Define a `box_free` predicate on bimodal
formulas. Prove that if the conclusion of a TM derivation is box-free, then the derivation
can be transformed into one that uses only temporal axioms and rules (no `necessitation`,
no S5 axioms). Then translate.

**Approach C (Simplest: use PropositionalConservativity pattern on Z + additional lemma)**:
1. For Z specifically, build the semantic bridge
2. Use the fact that temporal BX has the same theorems regardless of the domain (by
   soundness + completeness: a formula is BX-derivable iff it is valid on all serial
   linear orders, and validity on Z alone suffices because BX is complete w.r.t. countable
   linear orders)

Actually approach C may work if we can show that BX-validity on Z implies BX-validity on
all serial linear orders. This is essentially the "standard model property" for BX.

**After further reflection**: The approach that most closely follows the existing codebase
pattern (PropositionalConservativity.lean) is:

1. Fix D = Z, construct trivial task model from temporal valuation
2. Prove semantic bridge for box-free formulas on this specific model
3. Use TM soundness to get truth of phi.toBimodal
4. Use semantic bridge to get Satisfies M t phi for arbitrary M on Z
5. Use temporal soundness+completeness infrastructure

The gap at step 5 is that temporal completeness needs validity on ALL D, not just Z.
However, if phi is TM-derivable then phi.toBimodal is valid on ALL task models (including
those on D' for any D' with the right structure). So we get:

For ALL D' with AddCommGroup + LinearOrder + IsOrderedAddMonoid + Nontrivial:
  phi is valid on D'

This includes Z, Q, R, and many other domains. The question is whether this is
sufficient for temporal completeness.

Looking at the completeness proof: it constructs a countermodel on `ChronicleSubtype`,
a subtype of Q. If we can ensure `ChronicleSubtype` has `AddCommGroup`, we're done.
Alternatively, if we can prove `ChronicleSubtype` embeds order-preservingly into Q
(which it does, being a subtype), and Q has AddCommGroup, then we might be able to
extend the temporal model on `ChronicleSubtype` to one on Q.

## 9. Implementation Recommendation

Given the analysis, the recommended implementation approach is:

### Primary: Semantic Bridge on Z (with explicit domain handling)

1. **Construct trivial task model from temporal model on Z**:
   ```lean
   def trivialTaskModelOfTemporal (M : TemporalModel Z Atom) :
       TaskModel Atom TaskFrame.trivialFrame :=
     { valuation := fun _ p => M.valuation 0 p }  -- or parameterize
   ```
   Actually this is insufficient because the valuation needs to depend on time.
   The correct construction is to use `WorldHistory.trivial` (domain = everything,
   single world state = Unit) and set `valuation () p := M.valuation t p` -- but
   the valuation is fixed, not time-dependent.

   **The right construction**: Use a world history with `domain = fun _ => True` and
   `states t _ = t` (world state = time point), so `WorldState = D`. Then
   `valuation w p = M.valuation w p`. This makes `truthAt` of an atom equal to
   `exists (ht : True), M.valuation t p`, which simplifies to `M.valuation t p`.

2. **Prove semantic bridge**: For box-free bimodal formulas that are images of
   `toBimodal`, show `truthAt = Satisfies` by structural induction.

3. **Apply TM soundness** on Z to get truth of `phi.toBimodal`.

4. **Extract** `Satisfies M t phi`.

5. **Handle the completeness gap**: Since temporal completeness needs validity on ALL
   D, and we can only establish it for D with `AddCommGroup`, we need one of:
   (a) Show BX-validity on Z implies BX-validity on all serial linear orders (standard
       model property)
   (b) Show the chronicle countermodel domain has `AddCommGroup`
   (c) Use a different completeness theorem that only needs Z-validity

### Alternative: Syntactic Translation (if semantic approach blocked)

Define an inductive translation of bimodal derivation trees (for box-free conclusions)
into temporal derivation trees. This avoids the domain mismatch but requires proving
that TM derivations of temporal formulas can be "de-modalized."

### Blocking Question

The main blocking question for the semantic approach: **Does temporal BX have the
"standard model property" -- is BX-validity on Z alone sufficient for BX-derivability?**

If yes (which is expected for temporal logics on linear orders), the semantic approach
works cleanly. If not, the syntactic approach is needed.

**Research needed**: Check whether there is a result in the codebase or literature
confirming that BX-validity on Z (or any single countable linear order) implies
BX-validity on all serial linear orders. For standard temporal logics, this follows from
the fact that the completeness proof constructs a countable countermodel, and Z embeds
all countable linear orders (Cantor's theorem for countable dense linear orders, or
direct embedding for discrete ones).

## 10. Suggested File Location

```
Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean
```

This follows the naming convention of the existing `PropositionalConservativity.lean`.

## 11. Summary of Key Findings

- The `toBimodal` embedding exists and is structurally trivial (identity on shared constructors)
- The existing `lift_derivation_qfree` infrastructure is NOT applicable (operates within bimodal, not across logics)
- The existing conservative extension proofs (over CPL) use semantic approaches
- The main technical challenge is the domain mismatch: bimodal soundness requires `AddCommGroup D` but temporal completeness needs arbitrary `D` with `LinearOrder`
- Two viable approaches exist: semantic bridge (simpler if standard model property holds) or syntactic derivation translation (more complex but avoids domain issues)
- No `IsTemporal` or `boxFree` predicate exists in CSLib; temporal formulas are identified by being in the image of `toBimodal`
