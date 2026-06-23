# Teammate B Findings: CSLib Typeclass Hierarchy and Term-Mode Search Design

**Task 269**: Build generic bounded proof-search tactic for InferenceSystem
**Role**: CSLib typeclass hierarchy and term-mode search design (Round 2)
**Date**: 2026-06-23

---

## 1. Complete InferenceSystem Typeclass Hierarchy

### Core Abstraction Layer (`Cslib/Foundations/Logic/InferenceSystem.lean`)

The root abstraction is:

```lean
class InferenceSystem (S : Type*) (α : Type*) where
  derivation (a : α) : Sort v
```

Tag type `S` is opaque; `α` is the formula type. `derivation S φ` is the
derivation type (written `S⇓φ` in notation).

Key derived definitions:
- `DerivableIn S a = Nonempty (S⇓a)` -- Prop-valued wrapper
- `Derivable a = DerivableIn Default a` -- single-system shorthand
- `rwConclusion : Γ = Δ → S⇓Γ → S⇓Δ` -- rewrite rule for conclusions
- `DerivableIn.fromDerivation : S⇓a → DerivableIn S a` -- coercion up
- `DerivableIn.toDerivation : DerivableIn S a → S⇓a` -- noncomputable coercion down

### Connective Typeclasses (`Cslib/Foundations/Logic/Connectives.lean`)

Each connective is an independent typeclass:

| Typeclass | Method | Arity |
|-----------|--------|-------|
| `HasBot F` | `bot : F` | 0-ary |
| `HasImp F` | `imp : F → F → F` | binary |
| `HasBox F` | `box : F → F` | unary |
| `HasDia F` | `dia : F → F` | unary (primitive diamond for non-classical) |
| `HasUntil F` | `untl : F → F → F` | binary |
| `HasSince F` | `snce : F → F → F` | binary |
| `HasNext F` | `next : F → F` | unary |
| `HasAnd F` | `and : F → F → F` | binary (available for PL) |
| `HasOr F` | `or : F → F → F` | binary (available for PL) |

Bundled classes: `PropositionalConnectives`, `ModalConnectives`,
`TemporalConnectives`, `BimodalConnectives` compose via `extends`.

Critical note: `HasAnd` and `HasOr` are NOT part of `ModalConnectives`,
`TemporalConnectives`, or `BimodalConnectives`. Modal/temporal/bimodal formula
types use the Lukasiewicz encoding: `conj' φ ψ = (φ → (ψ → ⊥)) → ⊥`,
`disj' φ ψ = (φ → ⊥) → ψ`. Only `PL.Proposition` has native `and`/`or`
constructors with `HasAnd`/`HasOr` instances.

### Axiom Typeclasses (`Cslib/Foundations/Logic/ProofSystem.lean`)

Layer 1: Per-axiom typeclasses (all under `[HasBot F] [HasImp F] [InferenceSystem S F]`):

| Typeclass | Method | Statement |
|-----------|--------|-----------|
| `HasAxiomImplyK S` | `implyK : DerivableIn S (ImplyK φ ψ)` | `φ → (ψ → φ)` |
| `HasAxiomImplyS S` | `implyS : DerivableIn S (ImplyS φ ψ χ)` | `(φ→(ψ→χ))→((φ→ψ)→(φ→χ))` |
| `HasAxiomEFQ S` | `efq : DerivableIn S (EFQ φ)` | `⊥ → φ` |
| `HasAxiomPeirce S` | `peirce : DerivableIn S (Peirce φ ψ)` | `((φ→ψ)→φ)→φ` |
| `HasAxiomK S` | `K : DerivableIn S (AxiomK φ ψ)` | `□(φ→ψ)→(□φ→□ψ)` |
| `HasAxiomT S` | `T : DerivableIn S (AxiomT φ)` | `□φ→φ` |
| `HasAxiom4 S` | `four : DerivableIn S (Axiom4 φ)` | `□φ→□□φ` |
| `HasAxiomB S` | `B : DerivableIn S (AxiomB φ)` | `φ→□◇φ` |
| `HasAxiom5 S` | `five : DerivableIn S (Axiom5 φ)` | `◇φ→□◇φ` |
| `HasAxiomD S` | `D : DerivableIn S (AxiomD φ)` | `□φ→◇φ` |

Plus `ModusPonens S` (method `mp`) and `Necessitation S` (method `nec`).

Layer 2: Bundled proof systems (each via `extends`):

```
MinimalHilbert = ModusPonens + HasAxiomImplyK + HasAxiomImplyS
IntuitionisticHilbert = MinimalHilbert + HasAxiomEFQ
ClassicalHilbert = IntuitionisticHilbert + HasAxiomPeirce
ModalHilbert = ClassicalHilbert + Necessitation + HasAxiomK
ModalTHilbert = ModalHilbert + HasAxiomT
ModalDHilbert = ModalHilbert + HasAxiomD
ModalS4Hilbert = ModalTHilbert + HasAxiom4
ModalS5Hilbert = ModalS4Hilbert + HasAxiomB
TemporalBXHilbert = ClassicalHilbert + TemporalNecessitation + 22 temporal axioms
BimodalTMHilbert = ModalS5Hilbert + TemporalBXHilbert + HasAxiomMF
```

The full hierarchy for bimodal: `BimodalTMHilbert` inherits from 30+ typeclass
constraints total (counting atomic axiom classes).

Layer 3: Tag types (opaque `Type := Empty`):

```
Propositional.HilbertMin, HilbertInt, HilbertCl
Modal.HilbertK, HilbertT, HilbertD, HilbertS4, HilbertS5, HilbertB, HilbertK4, ...
Temporal.HilbertBX
Bimodal.HilbertTM
```

Each tag type gets concrete `InferenceSystem` + all axiom instances in an
`Instances.lean` file. For `Bimodal.HilbertTM`, the `InferenceSystem` instance
maps `HilbertTM⇓φ` to `DerivationTree .Base [] φ`.

---

## 2. Combinators Module Catalog

### Foundations Combinators (`Cslib/Foundations/Logic/Theorems/Combinators.lean`)

All are generic over `[MinimalHilbert S (F := F)]`:

| Theorem | Type | Note |
|---------|------|------|
| `imp_trans h1 h2` | `DerivableIn S (φ→ψ) → DerivableIn S (ψ→χ) → DerivableIn S (φ→χ)` | transitivity |
| `identity φ` | `DerivableIn S (φ→φ)` | SKK construction |
| `b_combinator` | `DerivableIn S ((ψ→χ)→((φ→ψ)→(φ→χ)))` | B combinator |
| `flip` | `DerivableIn S ((φ→ψ→χ)→(ψ→φ→χ))` | C combinator |
| `app1` | `DerivableIn S (φ→(φ→ψ)→ψ)` | single application |
| `app2` | `DerivableIn S (φ→ψ→(φ→ψ→χ)→χ)` | Vireo (double application) |
| `pairing φ ψ` | `DerivableIn S (φ→ψ→¬(φ→¬ψ))` | conjunction introduction |
| `dni φ` | `DerivableIn S (φ→¬¬φ)` | double negation introduction |
| `combine_imp_conj hA hB` | from `DerivableIn S (P→A)` + `DerivableIn S (P→B)` gives `DerivableIn S (P→¬(A→¬B))` | |
| `combine_imp_conj_3 hA hB hC` | three implications into nested conjunction | |
| `implication_absorption` | `DerivableIn S ((φ→φ→ψ)→(φ→ψ))` | W combinator |

### Propositional Core (`Cslib/Foundations/Logic/Theorems/Propositional/Core.lean`)

Over `[ClassicalHilbert S]`:
- `double_negation` : `DerivableIn S (¬¬φ→φ)` (DNE via Peirce)
- `lce_imp` : `DerivableIn S ((φ∧ψ)→φ)` (left conj. elim, Lukasiewicz)
- `rce_imp` : `DerivableIn S ((φ∧ψ)→ψ)` (right conj. elim, Lukasiewicz)
- `rcp` : `DerivableIn S ((¬φ→¬ψ)→(ψ→φ))` (reverse contraposition)

### Propositional Connectives (`Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean`)

Over `[MinimalHilbert S]`:
- `contrapose_imp` : `DerivableIn S ((φ→ψ)→(¬ψ→¬φ))`
- `contraposition h` : from `DerivableIn S (φ→ψ)` derives `DerivableIn S (¬ψ→¬φ)`
- `iff_intro h1 h2` : from `DerivableIn S (A→B)` + `DerivableIn S (B→A)` gives `DerivableIn S (A↔B)`

Over `[ClassicalHilbert S]`:
- `classical_merge` : `DerivableIn S ((P→Q)→((¬P→Q)→Q))`
- `demorgan_conj_neg_forward`, `demorgan_conj_neg_backward`, `demorgan_conj_neg`
- `demorgan_disj_neg_forward`, `demorgan_disj_neg_backward`, `demorgan_disj_neg`

### Modal Basic (`Cslib/Foundations/Logic/Theorems/Modal/Basic.lean`)

Over `[ModalHilbert S]`:
- `box_mono h` : from `DerivableIn S (φ→ψ)` derives `DerivableIn S (□φ→□ψ)` -- KEY META-RULE
- `diamond_mono h` : from `⊢ φ→ψ` derives `⊢ ◇φ→◇ψ`
- `box_contrapose` : `DerivableIn S (□(φ→ψ)→□(¬ψ→¬φ))`
- `k_dist_diamond` : `DerivableIn S (□(φ→ψ)→(◇φ→◇ψ))`
- `modal_duality_neg`, `modal_duality_neg_rev`
- `box_iff_intro h` : from `⊢ φ↔ψ` derives `⊢ □φ↔□ψ`

### S5 Theorems (`Cslib/Foundations/Logic/Theorems/Modal/S5.lean`)

Over `[ModalS5Hilbert S]`:
- `diamond_4` : `DerivableIn S (◇◇φ→◇φ)` (Axiom 5 derivation)
- `axiom5_derived` : `DerivableIn S (◇φ→□◇φ)`
- `t_box_to_diamond` : `DerivableIn S (□φ→◇φ)` (seriality from T)
- `box_conj_iff`, `diamond_disj_iff`, `s5_diamond_box`

### Temporal (`Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`)

Over `[TemporalBXHilbert S]`:
- `until_mono_guard`, `since_mono_guard` (BX2G/BX2H)
- `until_mono_event`, `since_mono_event` (BX3/BX3')
- `serial_future_derived`, `serial_past_derived`
- `connect_future_derived`, `connect_past_derived`
- Plus wrappers for all 22 BX axioms as `DerivableIn S (...)` theorems

### Bimodal-Specific (`Cslib/Logics/Bimodal/Theorems/Combinators.lean`)

These are `def`-level (not `theorem`-level) combinators, operating on
`DerivationTree fc []` directly (Type-valued, not Prop-valued):
- `impTrans`, `mp`, `identity`, `bCombinator`, `flip`, `app1`, `app2`
- `pairing`, `dni`, `combineImpConj`, `combineImpConj3`
- `tempFutureDerived` : `□φ → G(□φ)` (bimodal-specific)

---

## 3. Formula Decomposition: What Exists and What Doesn't

### What EXISTS for formula inspection

All concrete CSLib formula types derive `DecidableEq` and `BEq`:

```lean
-- PL.Proposition: DecidableEq via deriving
inductive Proposition (Atom : Type u) : Type u where
  | atom, | bot, | imp, | and, | or
  deriving DecidableEq, BEq

-- Modal.Proposition: DecidableEq via deriving
inductive Proposition (Atom : Type u) : Type u where
  | atom, | bot, | imp, | box
  deriving DecidableEq, BEq

-- Bimodal.Formula: DecidableEq via deriving
inductive Formula (Atom : Type u) : Type u where
  | atom, | bot, | imp, | box, | untl, | snce
  deriving DecidableEq, BEq
```

Pattern-matching on concrete formula types works directly in term-mode:

```lean
match φ with
| .imp a b => ...  -- works for Modal.Proposition, Bimodal.Formula, PL.Proposition
| .box inner => ...
| .bot => ...
| .atom p => ...
```

The `AxiomMatcher.lean` module (lines 91+) demonstrates extensive pattern matching
on `Formula Atom` using `match φ with | .imp lhs rhs => ...` etc.

### What does NOT exist: `HasImpView` / `HasBoxView`

There are no view/projection typeclasses in CSLib:
- No `HasImpView` that would allow `match hasImpView φ with | some (a, b) => ...`
- No `HasBoxView`, `HasUntilView`, `HasSinceView`
- No `matchImp`, `matchBox` helpers in the generic (`Foundations`) layer

The existing pattern-matching happens ONLY at the concrete formula type level
(in `AxiomMatcher.lean`, `ProofExtraction.lean`, etc.), not generically.

### Implications for `hilbertSearch`

A generic term-mode `hilbertSearch` operating over `[MinimalHilbert S (F := F)]`
CANNOT pattern-match on `φ : F` to detect if `φ = HasImp.imp a b`, because
`F` is abstract and `HasImp.imp` is a function, not a constructor.

This is the fundamental tension identified in the existing plan. There are two
resolution paths:

**Path A (Pure generic, limited scope)**: The term-mode search only handles cases
that do NOT require formula decomposition:
- Axiom dispatch: `HasAxiomImplyK.implyK`, `HasAxiomK.K`, etc. (direct)
- Inference rule applications: `ModusPonens.mp`, `Necessitation.nec`
- Combinator chaining: `imp_trans`, `identity`, `box_mono`
- Hypothesis matching via `DecidableEq F` for equality comparison

**Path B (Concrete formula search)**: A separate, concrete search function for
each formula type using pattern-matching directly on constructors:
- `bimodalSearch : Bimodal.Formula Atom → Nat → Option (DerivationTree .Base [] φ)`
- This is exactly what `buildCompositionalProof` in `ProofExtraction.lean` does

The `buildCompositionalProof` function is the canonical existing implementation
of Path B. It operates on `Bimodal.Formula` directly:

```lean
match phi with
| .box inner => ...  -- pattern match on concrete constructor
| .imp a b => if h : a = b then ... else ...
| _ => none
```

### `whnf` + MetaM approach for generic formula decomposition

In MetaM, the Lean elaborator's `whnf` (weak head normal form) reduction can
reduce `HasImp.imp a b` to a form where the head is `HasImp.imp`. This enables
generic formula inspection in TacticM:

```lean
-- In MetaM/TacticM:
let reduced ← whnf formula_expr
if reduced.isAppOfArity ``HasImp.imp 4 then
  let a := reduced.getArg! 2
  let b := reduced.getArg! 3
  ...
```

This is the approach that belongs in the Tier 2 TacticM wrapper, NOT in the
term-mode Tier 1 search.

---

## 4. Concrete `hilbertSearch` Type Signature and Design

### Design Principles from CSLib API Surface

1. All derivability facts live in `InferenceSystem.DerivableIn S φ` (Prop-valued)
2. All combinators take and return `DerivableIn S (...)` values
3. The generic typeclass hierarchy allows `[MinimalHilbert S]` to use K, S, MP
4. Formula decomposition is only possible at concrete type level

### Recommended Term-Mode Search Function

**For generic axiom dispatch (works across all logic levels)**:

```lean
/-- Try to derive φ using available axioms at the current typeclass level.
    Returns `some (DerivableIn S φ)` on success, `none` on failure. -/
def tryAxiom {F : Type*} [HasBot F] [HasImp F]
    {S : Type*} [MinimalHilbert S (F := F)]
    (φ : F) : Option (InferenceSystem.DerivableIn S φ) :=
  -- Check implyK: φ must match `α → (β → α)` form -- REQUIRES formula view
  -- Check implyS: φ must match `(α→(β→χ))→((α→β)→(α→χ))` -- REQUIRES formula view
  none  -- cannot be implemented generically without HasImpView
```

This reveals the core issue: axiom matching requires knowing if `φ = imp α (imp β α)`,
which requires `HasImpView`. Without it, the generic layer cannot do axiom dispatch.

**For modus ponens chaining with known antecedent**:

```lean
/-- Given a collection of derivable hypotheses `hyps : List (Σ φ, DerivableIn S φ)`,
    try to derive `ψ` by modus ponens. -/
def mpChain {F : Type*} [HasBot F] [HasImp F] [DecidableEq F]
    {S : Type*} [MinimalHilbert S (F := F)]
    (hyps : List (Σ φ : F, InferenceSystem.DerivableIn S φ))
    (ψ : F) : Option (InferenceSystem.DerivableIn S ψ) :=
  -- Look for a hyp of the form (imp α ψ) and a hyp (α)
  hyps.findSome? fun ⟨φ, hφ⟩ =>
    -- Check if φ = imp α ψ -- REQUIRES formula view to extract α
    none
```

Again, the antecedent extraction requires formula decomposition.

**For concrete formula type (the viable path)**: Working at `Bimodal.Formula`
or `Modal.Proposition` level using `buildCompositionalProof` style:

```lean
/-- Bounded proof search for Bimodal formulas. Matches the pattern in ProofExtraction.lean.
    Generic enough to be the template for other formula types. -/
partial def hilbertSearch (fuel : Nat) (φ : Bimodal.Formula Atom)
    [DecidableEq Atom] :
    Option (InferenceSystem.DerivableIn Bimodal.HilbertTM φ) :=
  if fuel = 0 then none else
  -- Fast path: direct axiom match
  match tryAxiomProof φ with  -- from AxiomMatcher.lean
  | some d => some ⟨d⟩
  | none =>
  -- Structural decomposition
  match φ with
  | .imp a b =>
    if h : a = b then some (h ▸ Theorems.Combinators.identity a)
    else
      -- Try: if b is provable, so is a→b (weakening)
      match hilbertSearch (fuel - 1) b with
      | some hb => some (ModusPonens.mp HasAxiomImplyK.implyK hb)
      | none => none
  | .box inner =>
    match hilbertSearch (fuel - 1) inner with
    | some h => some (Necessitation.nec h)
    | none => none
  | _ => none
```

**The key API call pattern** for each reasoning step:
- `HasAxiomImplyK.implyK` -- `DerivableIn S (ImplyK φ ψ)` (weakening)
- `HasAxiomImplyS.implyS` -- `DerivableIn S (ImplyS φ ψ χ)` (distribution)
- `ModusPonens.mp h1 h2` -- from `h1 : DerivableIn S (imp φ ψ)` + `h2 : DerivableIn S φ`
- `Necessitation.nec h` -- from `h : DerivableIn S φ` gives `DerivableIn S (box φ)`
- `imp_trans h1 h2` -- transitivity combinator
- `identity φ` -- `DerivableIn S (φ→φ)`
- `box_mono h` -- from `DerivableIn S (φ→ψ)` gives `DerivableIn S (□φ→□ψ)`

### Full Proposed Signature for a Generic Wrapper

For the TacticM-layer Tier 2 (where MetaM expression inspection is available):

```lean
-- The TacticM function would:
-- 1. Inspect the goal: `DerivableIn S φ` or `S⇓φ`
-- 2. Call whnf on φ to get a reducible form
-- 3. Pattern-match on the whnf head to identify the connective
-- 4. Dispatch to the appropriate axiom / combinator
-- 5. Recursively handle subgoals
syntax (name := hilbertSearch) "hilbert_search" (num)? : tactic
```

For the term-mode Tier 1 (concrete formula type, working today):

```lean
/-- Type: Nat → Formula Atom → Option (DerivableIn HilbertTM φ)
    Parameterized by fuel. Returns proof if found, none if search exhausted.
    Lives in a `noncomputable` section since DerivableIn.toDerivation is noncomputable.

    Recommended placement: Cslib/Foundations/Logic/ProofSearch.lean
    Requires: [DecidableEq Atom] on the formula type. -/
noncomputable def hilbertSearch (fuel : Nat) :
    ∀ (φ : F), Option (InferenceSystem.DerivableIn S φ)
```

But as shown above, the concrete implementation must be per-formula-type
unless `HasImpView` typeclasses are added.

---

## 5. Formula Decomposition: `HasImpView` Proposal

To make `hilbertSearch` genuinely generic (not per-formula-type), CSLib needs
a minimal decomposition typeclass:

```lean
/-- Typeclass for formula types that support implication inspection. -/
class HasImpView (F : Type*) [HasImp F] where
  /-- Decompose a formula into an implication pair, if it is one. -/
  viewImp (φ : F) : Option (F × F)
  /-- If `viewImp φ = some (a, b)` then `φ = imp a b`. -/
  viewImp_eq {φ a b : F} : viewImp φ = some (a, b) → φ = HasImp.imp a b

/-- Typeclass for formula types that support box inspection. -/
class HasBoxView (F : Type*) [HasBox F] where
  viewBox (φ : F) : Option F
  viewBox_eq {φ inner : F} : viewBox φ = some inner → φ = HasBox.box inner
```

All four concrete formula types can trivially instantiate these:

```lean
instance : HasImpView (Modal.Proposition Atom) where
  viewImp | .imp a b => some (a, b) | _ => none
  viewImp_eq := by intro φ a b h; split at h <;> simp_all

instance : HasImpView (Bimodal.Formula Atom) where
  viewImp | .imp a b => some (a, b) | _ => none
  viewImp_eq := by intro φ a b h; split at h <;> simp_all
```

With `HasImpView`, a truly generic search function becomes:

```lean
/-- Generic bounded Hilbert proof search.
    Returns `some (DerivableIn S φ)` on success within fuel steps.

    Typeclass requirements:
    - [DecidableEq F] for equality tests
    - [HasImpView F] for implication decomposition
    - [HasBoxView F] for box decomposition (if ModalHilbert)
    - [MinimalHilbert S (F := F)] for axioms and MP
-/
noncomputable def hilbertSearch {F : Type*} [HasBot F] [HasImp F] [DecidableEq F]
    [HasImpView F] {S : Type*} [MinimalHilbert S (F := F)]
    (fuel : Nat) (φ : F) : Option (InferenceSystem.DerivableIn S φ) :=
  if fuel = 0 then none else
  match HasImpView.viewImp φ with
  | some (a, b) =>
    if h : a = b then
      some (HasImpView.viewImp_eq rfl ▸ h ▸ identity a)
    else
      match hilbertSearch (fuel - 1) b with
      | some hb =>
        some (HasImpView.viewImp_eq ... ▸ ModusPonens.mp HasAxiomImplyK.implyK hb)
      | none => none
  | none => none -- non-implication, non-axiom: search fails
```

The equality proofs from `viewImp_eq` are needed to rewrite `HasImp.imp a b`
back to `φ` when constructing the proof witness. This is a non-trivial but
tractable engineering detail -- the `rwConclusion` helper in `InferenceSystem.lean`
already provides this pattern.

---

## 6. Fuel/Depth Parameter Strategy

### Current Pattern in CSLib (`buildCompositionalProof`)

```lean
def buildCompositionalProof (phi : Formula Atom) (fuel : Nat) :
    Option (DerivationTree .Base [] phi) :=
  if fuel = 0 then none
  else match phi with
  | .box inner => buildCompositionalProof inner (fuel - 1)  -- fuel decremented
  | .imp a b => buildCompositionalProof b (fuel - 1)        -- fuel decremented
  | _ => none
```

Fuel is decremented once per structural descent. This bounds the proof depth.

### Recommended Strategy for `hilbertSearch`

Use two fuel parameters (matches `itauto` level decomposition):

```lean
-- fastFuel: for pure axiom/combinator dispatch (no branching) -- default 5
-- searchFuel: for modus ponens backward search (branching) -- default 10
structure SearchConfig where
  fastFuel : Nat := 5
  searchFuel : Nat := 10

-- Tactic syntax:
syntax "hilbert_search" ("(" "depth" ":=" num ")")? : tactic
```

At the term-mode level, a single `fuel : Nat` parameter (decremented on structural
descent) is cleaner and adequate for Phase 1.

---

## 7. Key Design Decision: Where Formula Decomposition Lives

The fundamental architectural question is:

**Option A**: Add `HasImpView`/`HasBoxView` to `Foundations/Logic/Connectives.lean`
and build a generic `hilbertSearch` there.

**Option B**: Build per-formula-type search functions (like `buildCompositionalProof`)
and expose them through a common interface.

**Option C**: Keep Tier 1 generic but limited (axiom dispatch + MP with known
antecedent); put structural formula decomposition entirely in Tier 2's MetaM layer.

Assessment:
- Option A is the cleanest but requires adding new typeclasses (violates reuse-first
  unless confirmed no existing view abstraction exists -- confirmed: none exists).
  The new typeclasses are small, well-motivated, and follow CSLib style.
- Option B is the safest for Phase 1 (mirrors existing code in ProofExtraction.lean).
  Less generic but works immediately.
- Option C creates a gap: the tactic works but no term-mode search library exists.

**Recommendation**: Option B for Phase 1 (instantiate `hilbertSearch` for
`Bimodal.HilbertTM` following `buildCompositionalProof` pattern), with Option A
as the Phase 2 upgrade that adds `HasImpView`/`HasBoxView` to `Foundations/`.
The plan's current scope (Phase 1 = propositional + minimal modal) can proceed
without view typeclasses by working at the concrete `Modal.Proposition` level.

---

## 8. Critical Constraint: `noncomputable` and `Nonempty`

The term-mode search returns `Option (InferenceSystem.DerivableIn S φ)`.
`DerivableIn` is `Nonempty (S⇓φ)`.

- `DerivableIn.fromDerivation : S⇓a → DerivableIn S a` is computable
- `DerivableIn.toDerivation : DerivableIn S a → S⇓a` is `noncomputable`

The search function itself, when it constructs a `DerivableIn` from axiom
calls (e.g., `HasAxiomImplyK.implyK`), is computable in principle. However:

1. If the search function needs to inspect `DerivableIn` witnesses from
   hypotheses, it must use `toDerivation` (noncomputable).
2. The bimodal-specific search wraps `DerivationTree` (computable) in `Nonempty`
   (also computable via `Nonempty.intro`).

For the Phase 1 propositional/modal term-mode search, all operations are
computable IF the function only constructs new proofs from axioms + combinators
(never needs to extract a derivation from a `Nonempty` witness).

The `noncomputable` annotation should be added if the search needs to call
`DerivableIn.toDerivation` anywhere -- a conservative default.

---

## 9. Connections to Existing `AxiomMatcher.lean` Infrastructure

The `matchAxiom` function in `AxiomMatcher.lean` is a pure `Bimodal.Formula`
pattern-matcher returning `Option (AxiomWitness Atom)`. This is:

1. **Concrete-type-specific** (only for `Bimodal.Formula`)
2. **Computable** (returns `Option (Sigma Axiom)`)
3. **Called by** `tryAxiomProof` in `ProofExtraction.lean`
4. **The correct model** for Phase 1's axiom matching

The generic `hilbertSearch` for bimodal should wrap `matchAxiom` and then call
`buildCompositionalProof` for formulas not matched as axioms. This avoids
reimplementing the 42-axiom matching logic.

For modal (`Modal.Proposition`), a separate, smaller axiom matcher needs to be
written (only ~10 axioms for K-level). This is ~80-120 lines of straightforward
pattern matching code.

---

## Summary: API Surface for the Term-Mode Search Core

The core term-mode search for Phase 1 should call the following CSLib API:

**For axiom dispatch** (bimodal):
- `matchAxiom : Formula Atom → Option (AxiomWitness Atom)` (existing)
- `tryAxiomProof : Formula Atom → Option (DerivationTree .Base [] φ)` (existing)

**For inference rules** (generic via typeclasses):
- `ModusPonens.mp : DerivableIn S (imp φ ψ) → DerivableIn S φ → DerivableIn S ψ`
- `Necessitation.nec : DerivableIn S φ → DerivableIn S (box φ)`
- `Theorems.Combinators.identity : DerivableIn S (imp φ φ)`
- `Theorems.Combinators.imp_trans : DerivableIn S (φ→ψ) → DerivableIn S (ψ→χ) → DerivableIn S (φ→χ)`
- `Theorems.Modal.Basic.box_mono : DerivableIn S (φ→ψ) → DerivableIn S (□φ→□ψ)`

**For formula equality** (required, available on all concrete types):
- `[DecidableEq F]` / `DecidableEq.decEq : (a b : F) → Decidable (a = b)`

**What is missing** (needed for generic search, not yet in CSLib):
- `HasImpView F` with `viewImp : F → Option (F × F)`
- `HasBoxView F` with `viewBox : F → Option F`
- A generic `matchAxiom` at the `[MinimalHilbert S]` / `[ModalHilbert S]` level
