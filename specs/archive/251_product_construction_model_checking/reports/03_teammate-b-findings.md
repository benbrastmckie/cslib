# Task 251: Product Construction and Model Checking — Alternative Approaches (Teammate B)

## Summary

After studying the CSLib infrastructure, the literature, and existing product constructions,
this report concludes that: (1) the LTS × NBA product cannot be expressed as a simple
instantiation of existing constructions; (2) there is a plausible "direct path" that avoids
an explicit product file but would be fragile and harder to extend; (3) the right approach
is a standalone `LTSProduct.lean`, and it should live in the LTL semantics layer rather than
the NA automata layer; (4) on-the-fly formalization is not worth doing now; and (5) the
`SatisfiesExec` bridge is the natural entry point for the model checking theorem but cannot
replace the product construction itself.

---

## Key Findings

### Finding 1: The FLTS Product Cannot Generalize to LTS × NBA

`Cslib/Foundations/Semantics/FLTS/Prod.lean` defines a **synchronous product of two
deterministic (functional) LTSs** sharing the same label type:

```lean
def prod (flts1 : FLTS State1 Label) (flts2 : FLTS State2 Label) :
    FLTS (State1 × State2) Label where
  tr := fun (s1, s2) μ ↦ (flts1.tr s1 μ, flts2.tr s2 μ)
```

The LTS × NBA product is **categorically different**:
- The LTS has transition relation `Tr : State → Label → State → Prop` (nondeterministic).
- The NBA has `Tr : NAState → Symbol → NAState → Prop` with `Symbol = Set Atom`.
- The label "consumed" by the NBA is the **labeling** of the *target* LTS state (`L(s')`),
  not a shared label.
- The product is not deterministic; it cannot be expressed as an FLTS.

No generalization of `FLTS.prod` covers the LTS × NBA case. The FLTS product requires
determinism and a shared label type; the LTS × NBA product involves a cross-type projection.

### Finding 2: The NA.iProd Cannot Express the LTS × NBA Product

`Cslib/Computability/Automata/NA/Prod.lean` defines an indexed product of NAs sharing the
same symbol type:

```lean
def iProd (na : (i : I) → NA (State i) Symbol) : NA (Π i, State i) Symbol where
  Tr s x t := ∀ i, (na i).Tr (s i) x (t i)
```

The NBA intersection construction (`BuchiInter.lean`) builds on this: it takes two NBAs
over the same symbol type and synchronizes them step-by-step on the same input letter.

The LTS × NBA product is **not** an instance of two NAs being intersected because:
- The LTS is not an NA (it lacks a start state and accepting set).
- The "symbol" for the NBA comes from the **labeling function applied to the LTS state**,
  not from an external input tape.
- The `iProd` requires both components to read the same external symbol; the LTS × NBA
  product has the LTS driving the label via `L(s')`.

Concretely: the NBA reads `L(s')` at each step, where `s'` is the next LTS state. This
"internally generated" alphabet cannot be modeled as a second NA in `iProd`, because
the second NA would need to read its own transition label as input — a circular dependency.

**Conclusion**: The LTS × NBA product needs its own dedicated definition. It is not a
special case of any existing CSLib product construction.

### Finding 3: The SatisfiesExec Bridge Does NOT Eliminate the Need for an Explicit Product

`OmegaExecutionSatisfies.lean` defines:

```lean
def SatisfiesExec (labeling : State → (Atom → Prop))
    (ss : ωSequence State) (φ : Formula Atom) : Prop :=
  Satisfies (fun p s => labeling s p) ss φ
```

This bridge connects `OmegaExecution`-typed LTS runs to LTL satisfaction. It is the correct
abstraction for the "system side" of the model checking theorem.

However, the model checking theorem requires connecting the **NBA side** as well:
- A path `ss` in the LTS satisfies `¬φ` if and only if `ss` is the state projection of an
  accepting run of `A_{¬φ}`.
- The NBA correctness theorem (from task 242 / `OmegaRegular.lean`) states that LTL formulas
  define ω-regular languages recognized by an NBA.
- To get an accepting run of `A_{¬φ}` **synchronized** with the LTS path, we need the
  product automaton — an explicit data structure pairing `(LTS state, NBA state)` with a
  transition relation encoding both the LTS transition and the NBA acceptance of the label.

The `SatisfiesExec` bridge participates in the proof but cannot replace the product.
Specifically:

- The **soundness direction** (accepting run of product → LTS path satisfies `¬φ`): the
  projection of the product run gives an LTS `OmegaExecution`; then `SatisfiesExec` connects
  this to `¬φ` satisfaction.
- The **completeness direction** (LTS path satisfying `¬φ` → accepting run of product): the
  `SatisfiesExec` hypothesis and the NBA correctness theorem together provide an NBA run; the
  NBA run and the LTS execution must be **co-induced** to form a product run.

Without defining the product explicitly, stating the model checking theorem requires
quantifying over "synchronized pairs" informally — which is exactly what the product formalizes.

### Finding 4: The Model Checking Theorem Has a Direct Formulation Without Explicit Product

There is a viable "product-free" statement of the model checking theorem that works by:
1. Defining an NBA for `¬φ` (from `OmegaRegular.lean`: `gnbaNBA (neg φ)`).
2. Defining an inline NBA for the model checking check: given LTS `lts`, labeling `L`, start
   state `s₀`, and NBA `A`:

   ```lean
   def modelCheckingNBA (lts : LTS State Label)
       (L : State → Set Atom) (s₀ : State)
       (A : NA.Buchi QState (Set Atom)) : NA.Buchi (State × QState) (List Label)
   ```

   This is exactly the product definition, but placed inline in the theorem rather than as a
   separate named construction.

The downside: the model checking theorem becomes opaque (the product structure is hidden),
and extending to other acceptance conditions or adding algorithmic results (SCC-based
algorithms) would require re-introducing the product anyway.

**Verdict**: The "direct path" without an explicit product file exists but sacrifices clarity
and reusability. Not recommended.

### Finding 5: The On-the-Fly Formulation is Out of Scope for Task 251

Gerth 1995 proposes an **on-the-fly** approach where the NBA for `¬φ` is constructed
simultaneously with the product, node by node during DFS. The key feature: the product can
be explored without fully materializing either the formula automaton or the LTS graph.

Formalizing on-the-fly verification would require:
- An imperative or coinductive DFS algorithm formalization
- A proof that partial product exploration is sound for emptiness detection
- Interface with the Gerth 1995 GNBA construction (which constructs nodes lazily)

This is a separate algorithmic formalization task. The on-the-fly property is about
*implementation efficiency*, not about the *correctness* of the product construction.
Courcoubetis 1992 confirms that the correctness argument reduces to checking emptiness of
the (fully defined) product automaton regardless of how it is explored.

**Verdict**: On-the-fly formalization is not in scope for task 251. The task asks for the
product construction and the model checking reduction theorem; both are about the
**mathematical object**, not the exploration algorithm.

### Finding 6: No Categorical/Pullback Generalization is Warranted

The LTS × NBA product could in principle be described as a pullback in a suitable category of
labeled transition systems (e.g., presheaves over the transition monoid, or fibrations over
the alphabet). However:
- CSLib does not have a category-theoretic framework for LTSs or automata.
- The Kripke-structure/LTS product is not used anywhere else in CSLib at this level of
  abstraction.
- The categorical description would add significant proof overhead without simplifying the
  core arguments.
- The Baier-Katoen and Vardi treatments are entirely "set-theoretic" and the CSLib proof
  should follow this style.

**Verdict**: No categorical abstraction is warranted. The product is a standalone definition.

---

## Alternative Approaches Considered

### Alternative A: Standalone LTSProduct.lean in the LTL Semantics Layer

**Location**: `Cslib/Logics/LTL/Semantics/LTSProduct.lean`

**Rationale**: The product construction is specific to the LTL model checking setting (the
symbol type is `Set Atom`, the labeling connects to the LTL atom set). It is not a general
automata construction. Placing it in `Cslib/Logics/LTL/Semantics/` keeps it co-located with
`OmegaExecutionSatisfies.lean` and `OmegaRegular.lean`, which it depends on.

**Structure**:
```lean
-- Given: lts : LTS SysState Label, L : SysState → Set Atom, A : NA.Buchi QState (Set Atom)
-- with s₀ : SysState, q₀ : QState initial states.
-- Product state: SysState × QState
-- Product LTS: standard product transition relation
-- Product NBA: inherit A's accepting set lifted to the product

structure LTSProduct ... where  -- or just `def`
  ...

theorem modelChecking ... :
    (∃ ss, lts.OmegaExecution ss ... ∧ SatisfiesExec L ss (neg φ)) ↔
    language (ltsMBA ...) ≠ ⊥
```

**Tradeoffs**:
- Pros: co-located with semantics, correct abstraction level, natural import chain.
- Cons: `Cslib/Logics/LTL/Semantics/` is mostly about logic, not about combining LTS + NBA.

### Alternative B: Standalone LTSProduct.lean in the Computability/Automata Layer

**Location**: `Cslib/Computability/Automata/NA/LTSProduct.lean`

**Rationale**: The product is technically a construction on an NBA (the LTS serves as a
"system" that generates the input alphabet). Could be expressed as: given any LTS `lts` and
any NBA `A` over `Set Atom`, define the synchronized product as an NBA.

**Tradeoffs**:
- Pros: more general; the product could be reused for CTL* or other temporal logics.
- Cons: the LTL-specific labeling (`L : State → Set Atom`) would have to be passed as a
  parameter; the connection to `SatisfiesExec` would require importing from `Logics/LTL/`.
  This creates a layering issue: `Computability/` importing `Logics/`.

**Verdict**: The layering violation rules this out. The product definition should stay in
`Cslib/Logics/LTL/Semantics/` or in a new `Cslib/Logics/LTL/ModelChecking/` module.

### Alternative C: Inline Product in a Model Checking Theorem File

**Location**: No separate file; everything in `Cslib/Logics/LTL/ModelChecking.lean`

**Rationale**: Define the product construction and the model checking theorem in a single
file. The product does not need to be a reusable abstraction.

**Tradeoffs**:
- Pros: minimal file count, no layering questions.
- Cons: the product state type and transition relation become anonymous; future algorithmic
  results (SCC-based emptiness on the product) would require re-introducing them or importing
  the opaque definitions.

**Verdict**: Acceptable if the only goal is the model checking reduction theorem. Not ideal
for long-term extensibility.

### Recommendation: Alternative A (Standalone in LTL Semantics Layer)

Place the product in `Cslib/Logics/LTL/Semantics/LTSProduct.lean`, with the model checking
theorem in the same file or a companion `Cslib/Logics/LTL/ModelChecking.lean`. This keeps
the semantics layer complete while maintaining a clear abstraction boundary.

---

## Evidence and Examples

### Evidence 1: FLTS.prod vs. LTS × NBA — Signature Incompatibility

```lean
-- FLTS product (existing)
def prod (flts1 : FLTS State1 Label) (flts2 : FLTS State2 Label) :
    FLTS (State1 × State2) Label where
  tr := fun (s1, s2) μ ↦ (flts1.tr s1 μ, flts2.tr s2 μ)
-- Both sides consume the same label μ

-- LTS × NBA product (needed) — schematic
def ltsNBAProd (lts : LTS SysState SysLabel)
    (L : SysState → Set Atom) (A : NA.Buchi QState (Set Atom)) :
    NA.Buchi (SysState × QState) SysLabel where
  Tr := fun (s, q) μ (s', q') => lts.Tr s μ s' ∧ A.Tr q (L s') q'
  -- NBA consumes L(s'), not the LTS label μ
  start := ...
  accept := ...
```

The mismatch: the FLTS product passes `μ` to both components; the LTS × NBA product passes
`μ` to the LTS and `L(s')` to the NBA. These are structurally different operations.

### Evidence 2: NA.iProd vs. LTS × NBA — Circular Dependency

```lean
-- iProd (existing): both components read the same symbol x
def iProd (na : (i : I) → NA (State i) Symbol) : NA (Π i, State i) Symbol where
  Tr s x t := ∀ i, (na i).Tr (s i) x (t i)

-- If we tried to model the LTS as an NA, the "symbol" for the NBA
-- would have to be L(s'), but s' is the OUTPUT of the LTS transition.
-- This is a forward dependency on the result of the LTS step.
```

To use `iProd`, the NBA would need to read `L(s')` as its external symbol, but `s'` is
determined by the LTS transition, not by an external tape. There is no way to express this
without the cross-type projection.

### Evidence 3: BuchiInter Acceptance Pattern is Reusable for the Model Checking Theorem

The `BuchiInter` construction (for NBA intersection) uses a **history bit** to track which
acceptance condition has been seen. This pattern is NOT needed for the LTS × NBA product
because:
- The LTS has no acceptance condition (it runs forever without accepting).
- The product NBA simply inherits the NBA's accepting set, lifted to the product state:
  `accept := lts.AllStates × A.accept`.

This is simpler than the intersection case. No history bit is needed.

### Evidence 4: SatisfiesExec is the Right System-Side Abstraction

```lean
-- From OmegaExecutionSatisfies.lean
def SatisfiesExec (labeling : State → (Atom → Prop))
    (ss : ωSequence State) (φ : Formula Atom) : Prop :=
  Satisfies (fun p s => labeling s p) ss φ
```

The model checking theorem would read:

```lean
theorem modelChecking_iff
    (lts : LTS SysState Label) (L : SysState → Set Atom)
    (initSet : Set SysState) (φ : Formula Atom)
    [Finite SysState] [Inhabited Label] :
    (∀ ss, ss 0 ∈ initSet → lts.OmegaExecution ss μs → SatisfiesExec (fun s p => p ∈ L s) ss φ)
    ↔
    language (ltsNBAProd lts L (gnbaNBA (neg φ))) = ⊥ := ...
```

The `SatisfiesExec` is the natural way to express "the LTS path satisfies φ" and it connects
directly to the `OmegaExecution` infrastructure.

---

## Confidence Level

| Claim | Confidence |
|-------|------------|
| FLTS.prod cannot generalize to LTS × NBA | High — signature mismatch is definitive |
| NA.iProd cannot express LTS × NBA | High — circular dependency argument is clear |
| SatisfiesExec does not eliminate need for product | High — soundness and completeness both require it |
| On-the-fly formalization is out of scope | High — confirmed by Courcoubetis 1992 |
| Categorical abstraction is unwarranted | Medium — categorical approach is possible but adds no value here |
| Standalone file in LTL Semantics layer is the right choice | Medium-High — defensible, but the exact module location is flexible |
| No history bit needed for LTS × NBA acceptance | High — the LTS has no acceptance, so the standard Büchi product suffices |

---

## Implications for Task 251 Implementation

1. **New file needed**: `Cslib/Logics/LTL/Semantics/LTSProduct.lean` (or similar name chosen
   by Teammate A or the planner).

2. **No enrichment of NA/Prod.lean**: The existing `NA.iProd` and `NA.BuchiInter` should not
   be modified. The LTS × NBA product is a standalone construction.

3. **Symbol type for the product NBA**: The product NBA has symbol type `Label` (the LTS
   transition label), NOT `Set Atom`. The NBA's input (the labeling `L(s')`) is generated
   internally from the LTS state, not from the product's input label.

4. **Accepting set lifting**: The product NBA's accepting set is `{(s, q) | q ∈ A.accept}`,
   i.e., `Set.preimage Prod.snd A.accept`. This is a simple set-theoretic lifting.

5. **Proof strategy for the model checking theorem**: The two directions are:
   - Soundness: given a product accepting run `(ss, qs)`, the LTS path `ss` is an
     `OmegaExecution`; apply `SatisfiesExec` + NBA correctness to conclude `ss ⊨ ¬φ`.
   - Completeness: given `ss` with `SatisfiesExec L ss (neg φ)`, use `OmegaRegular.lean`'s
     NBA correctness to get a NBA run `qs` synchronized with `ss` via `L`; pair them to
     form a product accepting run.

6. **Dependency chain**:
   ```
   LTSProduct.lean
     imports: OmegaExecutionSatisfies.lean  (SatisfiesExec)
              OmegaRegular.lean             (gnbaNBA, gnba_language_eq)
              Emptiness.lean                (language_eq_bot_iff)
   ```

7. **Lean 4 encoding note**: The product NBA transition
   `Tr (s, q) μ (s', q') = lts.Tr s μ s' ∧ A.Tr q (L s') q'`
   uses **anonymous constructor** pattern matching with the pair `(s, q)` and `(s', q')`.
   This requires `fun ⟨s, q⟩ μ ⟨s', q'⟩ => ...` or using `.1/.2` projections. The CSLib
   `BuchiInter.lean` uses the same pattern with `Bool → Type*` indexing; the pair type is
   simpler for the two-component case.
