# Round 2 Research: Reviewer-Directed Generic Metalogic Refactoring

**Task**: 207 -- Research refactoring Temporal/Modal metalogic based on PR #649 reviewer feedback
**Date**: 2026-06-15
**Session**: sess_1781543325_21d257
**Mode**: Deep focused investigation (Round 2 with actual reviewer comment)

## 1. Reviewer Comment Analysis

The reviewer wrote:

> "Looking at your MCS and Deduction Theorem proofs for temporal logic, I think we can abstract
> away from proving this stuff repeatedly by using classes.
>
> For instance, all you need is `|- phi -> psi -> phi`, `|- (phi -> psi -> chi) -> (phi -> psi) -> phi -> chi`,
> and `|- phi -> psi ==> |- phi ==> |- psi` and you can prove the deduction theorem
> (here's my formalization in Isabelle).
>
> Similarly, we could show, given those same axioms, that if `Gamma not-derives phi` then `Gamma`
> can be extended to an MCS `Omega` where `Omega not-derives phi`, and prove common results like
> `phi in Omega <=> Omega |- phi` and so on."

The reviewer linked: https://isa-afp.org/thys/Propositional_Logic_Class/Implication_Logic.html

### What the reviewer is asking for, precisely:

1. A **typeclass** (not a structure, not a locale) with three fields: K axiom, S axiom, MP rule
2. The **deduction theorem** proved generically for any type satisfying this class
3. The **MCS construction** (Lindenbaum extension) proved generically
4. The **MCS reflection property** (`phi in Omega <=> Omega |- phi`) proved generically
5. Concrete logics (Temporal, Modal, Propositional, Bimodal) should **instantiate** the class

### What CSLib already has that partially addresses this:

- `HasHilbertTree` typeclass in `DeductionHelpers.lean` -- has exactly the right fields (K, S, MP, assumption, weakening) but only proves 4 helper lemmas, not the full deduction theorem
- `DerivationSystem` structure in `Consistency.lean` -- has the MCS framework but requires a separate `HasDeductionTheorem` proof
- The gap: the deduction theorem and MCS properties are proved per-logic, not generically

## 2. Line-by-Line Comparison of DeductionTheorem Proofs

### 2.1 Structure Comparison

All four logics follow an identical proof structure for `deductionTheorem`:

```
match d with
| .axiom/ax ...      => deductionAxiom ...        -- K axiom case
| .assumption ...    => by_cases (= A / != A)     -- identity or K case
| .modus_ponens ...  => ih1, ih2, deductionMpUnderImp  -- S axiom case
| .weakening ...     => by_cases (= ctx / A in / A not in)
| <modal/temporal rules> => simp at hA            -- vacuous: empty context
```

### 2.2 What differs between the four proofs

| Aspect | PL | Modal | Temporal | Bimodal |
|--------|-----|-------|----------|---------|
| Formula type | `PL.Proposition Atom` | `Proposition Atom` | `Formula Atom` | `Formula Atom` |
| DerivationTree | 4 constructors | 5 constructors | 6 constructors | 7 constructors |
| Extra constructors | none | `necessitation` | `temporal_necessitation`, `temporal_duality` | `necessitation`, `temporal_necessitation`, `temporal_duality` |
| Axiom param | `Axioms : Prop -> Prop` | `Axioms : Prop -> Prop` | fixed `FrameClass.Base` | fixed `fc : FrameClass` |
| K axiom name | `.implyK` | `.implyK` | `.imp_s` (swapped!) | `.imp_s` (swapped!) |
| S axiom name | `.implyS` | `.implyS` | `.imp_k` (swapped!) | `.imp_k` (swapped!) |
| Height termination | same pattern | same pattern | same pattern | same pattern |
| `removeAll` helpers | same | same | same | same (inlined) |

**Critical observation**: The extra constructors (necessitation, temporal_necessitation, temporal_duality) are ALL handled identically -- `simp at hA` -- because they require empty context and the deduction theorem premise has `A :: Gamma` (non-empty). The proof is structurally identical regardless of how many extra empty-context rules exist.

### 2.3 What is literally identical

The following are character-for-character identical (modulo type names):

1. The `axiom/ax` case: `exact deductionAxiom ... (.axiom/ax [] ...)`
2. The `assumption` case: `by_cases h_eq : phi = A` with identity vs other subcases
3. The `modus_ponens` case: two recursive calls + `deductionMpUnderImp`
4. The `weakening` case: three subcases (Gamma' = A :: Gamma, A in Gamma', A not in Gamma')
5. All extra constructors: `simp at hA`

### 2.4 What the reviewer's insight enables

The reviewer's key insight is that the `HasHilbertTree` typeclass already captures everything needed. The proof does NOT need to pattern-match on concrete `DerivationTree` constructors. It only needs:

- `Tree` (the derivation tree type)
- `implyK` (produces `[] |- phi -> (psi -> phi)`)
- `implyS` (produces `[] |- (phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))`)
- `assumption` (from `phi in Gamma`)
- `mp` (modus ponens)
- `weakening`
- A `height` function with the right properties

The extra constructors (necessitation, duality) are irrelevant to the deduction theorem proof because they all require empty context.

## 3. Line-by-Line Comparison of MCS Proofs

### 3.1 Generic MCS Infrastructure (already exists)

`Consistency.lean` already provides:
- `DerivationSystem` structure with `Deriv`, `weakening`, `assumption`, `mp`
- `SetConsistent`, `SetMaximalConsistent`
- `set_lindenbaum` (Lindenbaum's lemma via Zorn)
- `HasDeductionTheorem` predicate
- `closed_under_derivation` (conditional on HasDeductionTheorem)
- `implication_property` (conditional on HasDeductionTheorem)
- `negation_complete` (conditional on HasDeductionTheorem)

### 3.2 What each logic duplicates in its MCS file

Each logic (PL, Modal, Temporal, Bimodal) has its own MCS file that:

1. **Defines abbreviations** for `SetConsistent` and `SetMaximalConsistent` instantiated at the logic's `DerivationSystem` -- trivial wrappers
2. **Wraps Lindenbaum** -- calls `Metalogic.set_lindenbaum` with the logic's system
3. **Wraps closed_under_derivation** -- calls generic version with the logic's `HasDeductionTheorem` proof
4. **Wraps implication_property** -- same
5. **Wraps negation_complete** -- same
6. **Proves `mcs_bot_not_mem`** -- identical proof across all 4 logics
7. **Proves `mcs_neg_of_not_mem`** -- identical
8. **Proves `mcs_not_mem_of_neg`** -- identical
9. **Proves `mcs_mem_iff_neg_not_mem`** -- identical

The Modal and Temporal files additionally prove logic-specific MCS properties:
- Modal: `mcs_box_closure`, `mcs_box_mp`, `mcs_box_witness` (using axiom K, T)
- Temporal: `mcs_g_mp`, `mcs_g_witness`, `mcs_h_mp`, `mcs_h_witness` (using temporal axioms)

### 3.3 What is duplicated vs. what is logic-specific

**Duplicated across all 4 logics** (~100 LOC per logic, ~300 LOC total savings):
- The wrapper abbreviations and lemmas (items 1-9 above)
- `mcs_bot_not_mem` proof (identical)
- `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem` (identical)

**Logic-specific (NOT duplicated)**:
- Modal's box witness construction (uses K, T axioms and necessitation)
- Temporal's G/H distribution and witness constructions (use temporal axioms)
- Bimodal's bundle/FMCS infrastructure (massive, specific to bimodal)

## 4. The Isabelle Pattern (Doty 2022)

The Isabelle formalization defines:

```isabelle
class implication_logic =
  fixes deduction :: "'a => bool"
  fixes implication :: "'a => 'a => 'a"
  assumes axiom_k: "|- phi -> psi -> phi"
  assumes axiom_s: "|- (phi -> psi -> chi) -> (phi -> psi) -> phi -> chi"
  assumes modus_ponens: "|- phi -> psi ==> |- phi ==> |- psi"
```

Key features:
- `list_implication` (`listImp`): `[] :-> phi = phi`, `(psi # Psi) :-> phi = psi -> Psi :-> phi`
- `list_deduction`: `Gamma :|- phi = |- Gamma :-> phi`
- The deduction theorem becomes **definitionally trivial**: `(phi # Gamma) :|- psi = Gamma :|- phi -> psi` unfolds to `|- phi -> Gamma :-> psi = |- phi -> Gamma :-> psi`
- MCS construction via Zorn's lemma, MCS reflection: `phi in Omega <=> Omega |- phi`
- `classical_logic` extends with `falsum` and double negation

### What translates vs. what does not

**Translates directly**:
- The class definition maps to a Lean 4 typeclass
- The MCS construction and properties
- The `phi in Omega <=> Omega |- phi` reflection

**Does NOT translate directly**:
- The `listImp`/definitional trick: CSLib uses `Type`-valued `DerivationTree` (not `Prop`-valued `deduction`), so the deduction theorem cannot be definitional. CSLib needs the explicit proof by induction on tree height. However, the proof is still generic over the typeclass.
- Isabelle's `interpretation` for instantiation: Lean 4 uses `instance` declarations instead.

## 5. Existing Foundations Infrastructure Analysis

### 5.1 HasHilbertTree (DeductionHelpers.lean)

This is the KEY existing abstraction. It already has exactly the right fields:

```lean
class HasHilbertTree (F : Type*) [HasImp F] where
  Tree : List F -> F -> Type*
  implyK : (phi psi : F) -> Tree [] (HasImp.imp phi (HasImp.imp psi phi))
  implyS : (phi psi chi : F) -> Tree []
    (HasImp.imp (HasImp.imp phi (HasImp.imp psi chi))
      (HasImp.imp (HasImp.imp phi psi) (HasImp.imp phi chi)))
  assumption : {Gamma : List F} -> {phi : F} -> phi in Gamma -> Tree Gamma phi
  mp : {Gamma : List F} -> {phi psi : F} -> Tree Gamma (HasImp.imp phi psi) -> Tree Gamma phi -> Tree Gamma psi
  weakening : {Gamma Delta : List F} -> {phi : F} -> Tree Gamma phi -> (forall x in Gamma, x in Delta) -> Tree Delta phi
```

It provides 4 generic helpers: `deductionAxiom`, `deductionImpSelf`, `deductionAssumptionOther`, `deductionMpUnderImp`.

**What it is missing** to complete the reviewer's request:
1. A `height` function on `Tree` (needed for well-founded recursion)
2. The `deductionWithMem` proof (generic)
3. The `deductionTheorem` proof (generic)
4. Connection to `DerivationSystem` / `HasDeductionTheorem`

### 5.2 DerivationSystem (Consistency.lean)

Already provides the full MCS framework. The gap is that each logic manually:
1. Defines a `DerivationSystem` instance
2. Proves `HasDeductionTheorem` by extracting from concrete `DerivationTree`
3. Wraps all the generic MCS lemmas

### 5.3 ProofSystem.lean hierarchy

The bundled classes (`MinimalHilbert`, `ClassicalHilbert`, etc.) work at the `Prop` level via `InferenceSystem`/`DerivableIn`. These are NOT directly useful for the `Type`-level `DerivationTree` proofs. They represent a parallel interface that is not yet connected.

## 6. Concrete Refactoring Design

### 6.1 The Key Insight: Extend HasHilbertTree with Height

The cleanest approach is to extend `HasHilbertTree` with a height function and prove the deduction theorem once generically. This requires:

```lean
class HasHilbertTree (F : Type*) [HasImp F] where
  Tree : List F -> F -> Type*
  implyK : (phi psi : F) -> Tree [] (HasImp.imp phi (HasImp.imp psi phi))
  implyS : (phi psi chi : F) -> Tree []
    (HasImp.imp (HasImp.imp phi (HasImp.imp psi chi))
      (HasImp.imp (HasImp.imp phi psi) (HasImp.imp phi chi)))
  assumption : {Gamma : List F} -> {phi : F} -> phi in Gamma -> Tree Gamma phi
  mp : {Gamma : List F} -> {phi psi : F} -> Tree Gamma (HasImp.imp phi psi) -> Tree Gamma phi -> Tree Gamma psi
  weakening : {Gamma Delta : List F} -> {phi : F} -> Tree Gamma phi -> (forall x in Gamma, x in Delta) -> Tree Delta phi
  -- NEW: height for well-founded recursion
  height : {Gamma : List F} -> {phi : F} -> Tree Gamma phi -> Nat
  height_mp_left : ... -- standard height lemmas
  height_mp_right : ...
  height_weakening : ...
```

**Problem**: The height function needs to satisfy specific ordering properties for ALL constructors, including logic-specific ones (necessitation, duality). But the generic class does not know about these constructors.

**Solution**: The height properties only need to hold for the constructors the generic proof uses: `mp` and `weakening`. Logic-specific constructors (necessitation, duality) are handled by the vacuous `simp at hA` case, which does not recurse and does not need height ordering.

However, there is a deeper issue: the generic `deductionTheorem` proof needs to **pattern match** on the tree to determine which constructor was used. The generic `HasHilbertTree` class does not expose constructors -- it only provides operations. This is why each logic currently has its own proof.

### 6.2 Alternative Design: Generic DerivationTree

Instead of extending `HasHilbertTree`, define a generic `DerivationTree` that captures the common constructors and allows extension:

```lean
/-- Generic derivation tree for any Hilbert-style system.
    Parameterized by:
    - F: formula type
    - ExtraRules: additional logic-specific rules (necessitation, duality, etc.)
    ExtraRules takes a formula from empty context and produces a formula from empty context. -/
inductive GenericDerivationTree (F : Type*) [HasImp F]
    (Axioms : F -> Prop) (ExtraRules : List F -> F -> Type*) :
    List F -> F -> Type _ where
  | ax (Gamma : List F) (phi : F) (h : Axioms phi) :
      GenericDerivationTree F Axioms ExtraRules Gamma phi
  | assumption (Gamma : List F) (phi : F) (h : phi in Gamma) :
      GenericDerivationTree F Axioms ExtraRules Gamma phi
  | modus_ponens (Gamma : List F) (phi psi : F)
      (d1 : GenericDerivationTree F Axioms ExtraRules Gamma (HasImp.imp phi psi))
      (d2 : GenericDerivationTree F Axioms ExtraRules Gamma phi) :
      GenericDerivationTree F Axioms ExtraRules Gamma psi
  | weakening (Gamma Delta : List F) (phi : F)
      (d : GenericDerivationTree F Axioms ExtraRules Gamma phi)
      (h : forall x in Gamma, x in Delta) :
      GenericDerivationTree F Axioms ExtraRules Delta phi
  | extraRule (Gamma : List F) (phi : F)
      (d : ExtraRules Gamma phi) :
      GenericDerivationTree F Axioms ExtraRules Gamma phi
```

**Problem with this approach**: The `ExtraRules` parameter makes it hard to define height uniformly, and `termination_by` needs to work with the specific type. Also, Lean 4's positivity checker may reject this if `ExtraRules` is not strictly positive.

### 6.3 Recommended Design: The Reviewer's Approach Adapted

The reviewer's approach, adapted for Lean 4's `Type`-valued trees, is:

**Step 1: Keep `HasHilbertTree` as is** (the 6-field typeclass).

**Step 2: Add a `HasDerivationTreeHeight` class** that captures height-based properties:

```lean
class HasDerivationTreeHeight (F : Type*) [HasImp F] extends HasHilbertTree F where
  /-- Height measure for well-founded recursion -/
  height : {Gamma : List F} -> {phi : F} -> Tree Gamma phi -> Nat
  /-- MP left subtree has strictly smaller height -/
  height_mp_left : {Gamma : List F} -> {phi psi : F} ->
    (d1 : Tree Gamma (HasImp.imp phi psi)) -> (d2 : Tree Gamma phi) ->
    d1.height < (mp d1 d2).height   -- PROBLEM: can't refer to mp's output tree
```

**This also does not work** because the typeclass operations (`mp`, `weakening`) return opaque `Tree` values -- we cannot state height properties about them without knowing the internal structure.

### 6.4 Actually Recommended Design: Prop-Level Generic Deduction Theorem

The cleanest approach that works within Lean 4's typeclass system, and directly follows the reviewer's suggestion:

**The key realization**: The deduction theorem can be proved at the `Prop` level (using `Deriv`, not `DerivationTree`) by using the `HasHilbertTree` operations without pattern matching.

Wait -- this does not work either. The deduction theorem proof fundamentally needs to case-split on HOW a formula was derived (was it an axiom? an assumption? MP? weakening? a necessitation rule?).

### 6.5 ACTUAL Recommended Design: Factor out the Pattern Match

The proof of the deduction theorem has this structure for ALL logics:

```
deductionTheorem d = match d with
  | common_constructor_1 => generic_proof_1    -- same across all logics
  | common_constructor_2 => generic_proof_2    -- same across all logics  
  | common_constructor_3 => generic_proof_3    -- same across all logics
  | common_constructor_4 => generic_proof_4    -- same across all logics
  | extra_rule_1 => simp at hA                 -- vacuous, same pattern
  | extra_rule_2 => simp at hA                 -- vacuous, same pattern
  | extra_rule_3 => simp at hA                 -- vacuous, same pattern
```

The generic part (constructors 1-4) is identical. The logic-specific part (extra rules) always follows the same pattern: `simp at hA` because non-empty context is impossible.

**Design**: Add a single new field to `HasHilbertTree` that bundles the "eliminate all extra rules" case:

```lean
class HasHilbertTree (F : Type*) [HasImp F] where
  -- existing fields (Tree, implyK, implyS, assumption, mp, weakening)
  ...
  /-- For the deduction theorem: given a derivation d from non-empty context
      A :: Gamma, either d is from one of the 4 common constructors, or d is
      vacuously impossible (the extra rules require empty context). -/
  cases_deduction :
    {Gamma : List F} -> {A phi : F} ->
    (d : Tree (A :: Gamma) phi) ->
    -- axiom case
    (Sum (Sigma (fun psi => Sigma (fun (d_ax : Tree [] psi) => phi = psi)))
    -- assumption case
    (Sum (phi in (A :: Gamma))
    -- modus_ponens case
    (Sum (Sigma (fun psi => (Tree (A :: Gamma) (HasImp.imp psi phi)) x (Tree (A :: Gamma) psi)))
    -- weakening case
    (Sigma (fun Gamma' => (Tree Gamma' phi) x (forall x in Gamma', x in (A :: Gamma)))))))
```

This is getting unwieldy. Let me step back and identify the simplest approach that achieves the reviewer's goal.

### 6.6 SIMPLEST VIABLE APPROACH

After analyzing all the code carefully, the simplest approach that achieves maximum duplication elimination with minimum disruption is:

**The deduction theorem proof in each logic already instantiates `HasHilbertTree` and delegates to the 4 generic helpers.** The ONLY thing that varies is:
1. The match on concrete constructors (but the logic is identical)
2. The handling of extra constructors (always `simp at hA`)
3. The `termination_by d.height` and `decreasing_by` blocks (same pattern)

The Modal deduction theorem is ALREADY parameterized over `Axioms : Proposition Atom -> Prop`. The PL deduction theorem copied this parameterization. The Temporal and Bimodal versions are NOT parameterized (they are fixed to specific frame classes).

**The minimal change the reviewer is asking for**:

1. **Factor the common MCS wrappers into a generic layer** -- eliminate the ~100 LOC per logic of trivial delegation wrappers
2. **Make the Temporal deduction theorem parameterized** like Modal's (it currently hardcodes `FrameClass.Base`)
3. **Provide a generic "given HasDeductionTheorem, here are all the MCS properties" bundle**

Here is the concrete design:

#### New File: `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean`

```lean
/-! # Generic MCS Properties for Any DerivationSystem with Deduction Theorem

Given a `DerivationSystem D` and a proof `HasDeductionTheorem D`, this module
provides all the common MCS properties that are currently duplicated across
PL, Modal, Temporal, and Bimodal MCS files. -/

namespace Cslib.Logic.Metalogic

variable {F : Type*} [HasBot F] [HasImp F]
variable (D : DerivationSystem F)
variable (hdt : HasDeductionTheorem D)

/-- If S is MCS, then bot not in S. -/
theorem mcs_bot_not_mem {S : Set F} (h_mcs : SetMaximalConsistent D S) :
    HasBot.bot ∉ S := by
  intro h_bot
  exact h_mcs.1 [HasBot.bot]
    (fun x hx => by simp [List.mem_cons] at hx; exact hx ▸ h_bot)
    (D.assumption (List.mem_cons.mpr (Or.inl rfl)))

/-- If phi not in MCS S, then (phi -> bot) in S. -/
theorem mcs_neg_of_not_mem {S : Set F} (h_mcs : SetMaximalConsistent D S)
    {phi : F} (h_not : phi ∉ S) : HasImp.imp phi HasBot.bot ∈ S := by
  rcases SetMaximalConsistent.negation_complete D hdt h_mcs phi with h | h
  · exact absurd h h_not
  · exact h

/-- If (phi -> bot) in MCS S, then phi not in S. -/
theorem mcs_not_mem_of_neg {S : Set F} (h_mcs : SetMaximalConsistent D S)
    {phi : F} (h_neg : HasImp.imp phi HasBot.bot ∈ S) : phi ∉ S := by
  intro h_phi
  exact mcs_bot_not_mem D h_mcs
    (SetMaximalConsistent.implication_property D hdt h_mcs h_neg h_phi)

/-- phi in S iff (phi -> bot) not in S, for MCS S. -/
theorem mcs_mem_iff_neg_not_mem {S : Set F} (h_mcs : SetMaximalConsistent D S)
    {phi : F} : phi ∈ S ↔ HasImp.imp phi HasBot.bot ∉ S := by
  constructor
  · intro h hn
    exact mcs_bot_not_mem D h_mcs
      (SetMaximalConsistent.implication_property D hdt h_mcs hn h)
  · intro h
    rcases SetMaximalConsistent.negation_complete D hdt h_mcs phi with h' | h'
    · exact h'
    · exact absurd h' h

/-- Helper: derive a formula from MCS membership using an axiom. -/
theorem mcs_mp_axiom {S : Set F} (h_mcs : SetMaximalConsistent D S)
    {phi psi : F} (h_mem : phi ∈ S) (h_ax : D.Deriv [] (HasImp.imp phi psi)) :
    psi ∈ S :=
  SetMaximalConsistent.closed_under_derivation D hdt h_mcs
    (L := [phi]) (fun x hx => by
      simp [List.mem_cons] at hx; exact hx ▸ h_mem)
    (D.mp (D.weakening h_ax (fun _ h => nomatch h))
      (D.assumption (List.mem_cons.mpr (Or.inl rfl))))

end Cslib.Logic.Metalogic
```

This single file eliminates ~400 LOC of duplication (100 LOC x 4 logics of identical wrapper lemmas).

#### Changes to Each Logic's MCS File

Each logic's MCS file would be simplified to:
1. An abbreviation for its `DerivationSystem`
2. The `HasDeductionTheorem` instance (already exists)
3. Logic-specific MCS properties only (box witness, G witness, etc.)
4. Reexports of the generic properties via `alias` or `abbrev`

For example, Modal's MCS file would become:

```lean
-- Keep: abbreviations, hasDeductionTheorem
-- Remove: modal_lindenbaum, modal_closed_under_derivation, modal_implication_property,
--   modal_negation_complete, mcs_bot_not_mem, mcs_neg_of_not_mem, mcs_not_mem_of_neg,
--   mcs_mem_iff_neg_not_mem, mcs_mp_axiom (all replaced by generic versions)
-- Keep: mcs_box_closure, mcs_box_box, mcs_box_diamond, mcs_box_mp, mcs_box_witness
--   (these are Modal-specific)
```

#### The Deduction Theorem: Keep per-logic but reduce boilerplate

The deduction theorem proof cannot be fully generalized because it requires pattern matching on concrete `DerivationTree` constructors. However, the current approach where Modal and PL are already parameterized over `Axioms` is sound. The remaining work is:

1. **Parameterize the Temporal deduction theorem** over axioms (matching Modal's design)
2. **Note the axiom name swap** (Temporal/Bimodal use `.imp_s` for K and `.imp_k` for S -- this should be fixed for consistency but is a separate task)

The per-logic deduction theorem proofs (~200 LOC each) must remain because they case-split on concrete constructors. But the `HasHilbertTree` instance + 4 generic helpers already factor out the common logic, so each proof is primarily structural recursion boilerplate. This is acceptable -- the Isabelle approach avoids this only because it uses `Prop`-level deduction (no tree structure to recurse on).

## 7. Assessment of Changes

### Files to Create

| File | Content | LOC (est.) |
|------|---------|------------|
| `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` | Generic MCS lemmas | ~80 |

### Files to Modify

| File | Change | LOC saved |
|------|--------|-----------|
| `Cslib/Logics/Propositional/Metalogic/MCS.lean` | Remove duplicated wrappers, use generic | ~80 |
| `Cslib/Logics/Modal/Metalogic/MCS.lean` | Remove duplicated wrappers, use generic | ~100 |
| `Cslib/Logics/Temporal/Metalogic/MCS.lean` | Remove duplicated wrappers, use generic | ~80 |
| `Cslib/Logics/Bimodal/Metalogic/Core/MaximalConsistent.lean` | Remove duplicated wrappers, use generic | ~60 |

### Files that can be simplified but NOT deleted

The per-logic DeductionTheorem files must remain (they do the concrete pattern match), but the `HasHilbertTree` instance + generic helpers already factor out the reusable parts.

### Files NOT touched

- All DerivationTree files (no structural change)
- All completeness files (they import MCS, so API must be preserved)
- Bimodal's massive metalogic infrastructure (51K LOC -- API preserved via aliases)

### Net impact

- **New code**: ~80 LOC (generic MCS properties)
- **Deleted code**: ~320 LOC (duplicated wrappers across 4 logics)
- **Net**: ~240 LOC reduction
- **API compatibility**: Preserved via `alias`/`abbrev` reexports

### Migration path

1. Create `MCSProperties.lean` with generic lemmas
2. For each logic (start with PL as simplest):
   a. Import `MCSProperties.lean`
   b. Replace duplicated lemma bodies with calls to generic versions
   c. Keep API names via `alias` for downstream compatibility
   d. Run `lake build` to verify
3. Each logic is a separate, safe PR

### Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| Breaking downstream imports | Low | Use `alias` to preserve names |
| Typeclass resolution slowdown | Low | No new typeclasses, just parametric lemmas |
| Bimodal cascading breakage | Medium | Touch Bimodal last, use aliases only |
| Temporal axiom name swap confusion | Low | Document in comments, fix in separate task |

## 8. Relationship to Existing Infrastructure

### How this relates to HasHilbertTree

`HasHilbertTree` already captures the K/S/MP structure the reviewer identified. The new `MCSProperties.lean` file complements it by providing the MCS-level consequences. Together:

- `HasHilbertTree` + `DeductionHelpers.lean` = generic deduction theorem HELPERS
- Per-logic `DeductionTheorem.lean` = concrete deduction theorem PROOF (unavoidable pattern match)
- Per-logic `DerivationTree.lean` = `DerivationSystem` instance + `HasDeductionTheorem` proof
- **NEW** `MCSProperties.lean` = generic MCS properties given `DerivationSystem` + `HasDeductionTheorem`

### How this relates to ProofSystem.lean / InferenceSystem.lean

The `ProofSystem.lean` hierarchy (`MinimalHilbert`, `ClassicalHilbert`, etc.) works at the `Prop`/`DerivableIn` level and is orthogonal to the `Type`-level `DerivationTree` metalogic. The two layers are not yet connected. Connecting them (proving that `MinimalHilbert` implies `HasDeductionTheorem`) is future work and out of scope for this task.

### How this relates to the Isabelle formalization

The Isabelle approach proves the deduction theorem definitionally via `listImp`. CSLib cannot do this because it uses `Type`-valued `DerivationTree` for structural recursion in other proofs. However, CSLib achieves the same goal (prove common MCS properties once) through the `DerivationSystem` + `HasDeductionTheorem` abstraction, which is the `Prop`-level equivalent. The new `MCSProperties.lean` completes this layer.

## 9. Summary and Recommendations

### What to implement (Phase 1 -- addresses reviewer's comment directly)

1. Create `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` with generic versions of:
   - `mcs_bot_not_mem`
   - `mcs_neg_of_not_mem`
   - `mcs_not_mem_of_neg`
   - `mcs_mem_iff_neg_not_mem`
   - `mcs_mp_axiom`
   - Convenience aliases for `set_lindenbaum`, `closed_under_derivation`, `implication_property`, `negation_complete`

2. Simplify each logic's MCS file to use the generic versions, preserving API via aliases.

### What to defer (Phase 2 -- further cleanup)

1. Parameterize Temporal's deduction theorem over axioms (matching Modal's design)
2. Fix the axiom name swap (`.imp_s` vs `.imp_k`) in Temporal/Bimodal
3. Investigate whether the `ProofSystem.lean` hierarchy can be connected to `HasDeductionTheorem`

### What NOT to do

1. Do not try to fully genericize the deduction theorem proof -- the concrete pattern match is unavoidable with `Type`-valued trees
2. Do not touch Bimodal's internal metalogic (51K LOC) beyond the MCS wrapper layer
3. Do not introduce a generic `DerivationTree` type -- the positivity/height issues make this impractical
4. Do not try to unify formula types -- keep concrete `Proposition`, `Formula`, etc.

### Responding to the reviewer

The PR response should explain:
- "We have created generic MCS properties in `Foundations/Logic/Metalogic/MCSProperties.lean` that factor out the common MCS lemmas (bot not in MCS, negation completeness, membership iff, etc.) using the existing `DerivationSystem` + `HasDeductionTheorem` abstraction."
- "The deduction theorem proof itself requires pattern matching on concrete `DerivationTree` constructors and cannot be fully genericized in Lean 4's type system. However, the 4 generic helper lemmas in `DeductionHelpers.lean` (via `HasHilbertTree`) already factor out the common logic."
- "This reduces ~320 LOC of duplication across 4 logics while preserving all APIs."
