# Teammate B Findings: Alternative Approaches for Hilbert/ND Equivalence Refactor

Task 186: `hilbert_nd_equivalence_refactor`
Agent: Teammate B (Alternative Approaches)

---

## Key Findings

### 1. h_EFQ Is Genuinely Unused in `ndToHilbert`

**Verdict: CONFIRMED. h_EFQ can be removed from `ndToHilbert` and `nd_to_hilbert_deriv`.**

`ndToHilbert` pattern-matches on `Theory.Derivation` constructors (lines 173-215 of
`Equivalence.lean`). The 10 constructors are:
`ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE`.

Looking at every case in `ndToHilbert`:

- `ax`: uses no axiom witnesses
- `ass`: uses no axiom witnesses
- `andI`: uses `h_andI` (via `hilbertAndI`)
- `andE1`: uses `h_andE1` (via `hilbertAndE1`)
- `andE2`: uses `h_andE2` (via `hilbertAndE2`)
- `orI1`: uses `h_orI1` (via `hilbertOrI1`)
- `orI2`: uses `h_orI2` (via `hilbertOrI2`)
- `orE`: uses `h_K`, `h_S`, `h_orE` (via `hilbertOrE`)
- `impI`: uses `h_K`, `h_S` (via `deductionTheorem`)
- `impE`: uses no axiom witnesses (just `modus_ponens`)

`h_EFQ` is passed through recursively in every case (lines 178-215) but **never consumed**.
There is no `botE` constructor on the ND side because `Theory.Derivation.botE` is a
**derived rule** in `DerivedRules.lean`, not a primitive constructor. It is defined using
`impE` applied to an axiom of the theory. Since the primitive ND system has no `botE`
constructor, `ndToHilbert`'s match is exhaustive without it.

**Implication**: `ndToHilbert` with `h_EFQ` removed still typechecks. The simplified
signature has 8 parameters instead of 9:

```lean
noncomputable def ndToHilbert
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ))))
    (h_andE1 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ))
    (h_andE2 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ))
    (h_orI1 : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (φ.or ψ)))
    (h_orI2 : ∀ (φ ψ : PL.Proposition Atom), Axioms (ψ.imp (φ.or ψ)))
    (h_orE : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))))
    ...
```

This is the **minimal axiom requirement**: exactly the connective axioms of `MinPropAxiom`
plus K and S.

### 2. The Existing Typeclass Infrastructure Already Bundles These Axioms

The CSLib `ProofSystem.lean` already defines individual axiom typeclasses
(`HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomAndI`, ..., `HasAxiomOrE`) and bundled
classes:

```
MinimalHilbert  = ModusPonens + HasAxiomImplyK + HasAxiomImplyS
IntuitionisticHilbert = MinimalHilbert + HasAxiomEFQ
ClassicalHilbert = IntuitionisticHilbert + HasAxiomPeirce
```

Notably, `MinimalHilbert` does NOT include the and/or axioms. The 8 witness parameters
in the refactored `ndToHilbert` correspond to K + S + 6 connective axioms, which is
`MinimalHilbert` + `HasAxiomAndI` + `HasAxiomAndE1` + `HasAxiomAndE2` +
`HasAxiomOrI1` + `HasAxiomOrI2` + `HasAxiomOrE`.

### 3. Three Viable Architectural Approaches

#### Approach A: Structure Bundling (Recommended)

Define a structure that bundles the 8 required witnesses:

```lean
structure HasMinimalConnectiveAxioms {Atom : Type*}
    (Axioms : PL.Proposition Atom → Prop) : Prop where
  h_K    : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ))
  h_S    : ∀ (φ ψ χ : PL.Proposition Atom),
    Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ)))
  h_andE1: ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ)
  h_andE2: ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ)
  h_orI1 : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (φ.or ψ))
  h_orI2 : ∀ (φ ψ : PL.Proposition Atom), Axioms (ψ.imp (φ.or ψ))
  h_orE  : ∀ (φ ψ χ : PL.Proposition Atom),
    Axioms ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))
```

`ndToHilbert` then takes `(h : HasMinimalConnectiveAxioms Axioms)` as a single
parameter. The three corollaries prove the structure for `MinPropAxiom`, `IntPropAxiom`,
and `PropositionalAxiom` as trivial term-mode proofs.

**Advantages**:
- Single parameter instead of 8
- Directly reflects what `MinPropAxiom` already contains
- `hilbert_iff_nd` becomes `hilbert_iff_nd_ctx` with one `h` parameter
- Unlocks `hilbert_iff_nd_min` (currently missing!) at zero proof cost
- The corollaries for int and cl become one-liners

**Disadvantage**: Introduces a new type that needs to be named carefully. Check that
`Cslib.Foundations.Logic` does not already have a suitable bundled structure.

#### Approach B: Typeclass-Based (Mathlib Style)

Instead of a structure, use the existing `HasAxiom*` typeclasses with a constraint:

```lean
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom → Prop}
    [h_K   : ∀ φ ψ, Axioms (φ.imp (ψ.imp φ))]    -- awkward
    ...
```

However, the existing `HasAxiom*` typeclasses in `ProofSystem.lean` are indexed by a
tag type `S`, not by a predicate `Axioms`. They take the form:
```lean
class HasAxiomImplyK (S : Type*) [HasImp F] [InferenceSystem S F] where
  implyK {φ ψ : F} : InferenceSystem.DerivableIn S (Axioms.ImplyK φ ψ)
```

This is a different abstraction level (closed-world derivability from the tag) vs. the
open-world `Axioms` predicate used in `ndToHilbert`. Connecting these requires the
`AxiomTheory` wrapper, which is already present.

The key insight: the `AxiomTheory Axioms` theory (used on the ND side) can be given
`IsIntuitionistic` and `IsClassical` instances:

```lean
instance [h : ∀ φ, Axioms (Proposition.bot.imp φ)] :
    IsIntuitionistic (AxiomTheory Axioms) where
  efq A := mem_axiomTheory.mpr (h A)
```

But for `ndToHilbert` itself, since it works with raw `Axioms` predicates, the
structure approach (Approach A) is cleaner. The typeclass approach is more useful for
the ND side's derived rules.

#### Approach C: Context-Based Generic Theorem (Strongest Result)

The strongest possible refactor extends the equivalence from the empty context to
all contexts:

```lean
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom → Prop}
    (h : HasMinimalConnectiveAxioms Axioms)
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv Axioms Γ.toList φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom) (Γ ⊢ φ) := by
  constructor
  · intro ⟨d⟩
    exact ⟨hilbertToND d⟩
  · intro ⟨d⟩
    exact ⟨ndToHilbert h.h_K h.h_S h.h_andI ... d⟩
```

This is the "stronger result" mentioned in the task description: Gamma ND-proves phi
iff Gamma Hilbert-proves phi, for arbitrary `Γ`. Currently `hilbert_iff_nd` only
handles the empty context.

**This is achievable**: `hilbert_to_nd_deriv` already works for any `Γ` (it produces
`DerivableIn ... ((Γ.toFinset : Ctx Atom) ⊢ φ)`, not just the empty context). The
`nd_to_hilbert_deriv` similarly produces `Deriv Axioms Γ.toList φ`. The empty-context
`hilbert_iff_nd` is then a corollary by setting `Γ = ∅`.

The context conversion (`Γ.toList` vs `Γ.toFinset`) is the only bookkeeping issue,
and helper lemmas `finset_insert_toList_mem_cons` and `list_cons_mem_finset_insert_toList`
already exist.

### 4. The `hilbert_iff_nd_min` Gap (Currently Missing)

The current `Equivalence.lean` has `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` but
**no `hilbert_iff_nd_min`**. With `h_EFQ` removed, `MinPropAxiom` satisfies all
required axiom witnesses (it has K, S, andI, andE1, andE2, orI1, orI2, orE). So
adding:

```lean
theorem hilbert_iff_nd_min {φ : PL.Proposition Atom} :
    Derivable MinPropAxiom φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ) :=
  hilbert_iff_nd
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ)
    (fun φ ψ => .andE1 φ ψ)
    (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ)
    (fun φ ψ => .orI2 φ ψ)
    (fun φ ψ χ => .orE φ ψ χ)
```

This is currently blocked by `h_EFQ` being required, but after the refactor it becomes
a trivial addition.

### 5. Naming Conventions and API Alignment

Following the task description's mention of "Mathlib-compatible naming":

- `hilbert_iff_nd_ctx` for the context-parametric theorem (stronger)
- `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` for the three logics
- Keep `hilbert_iff_nd` as the generic form (currently empty-context only)
- The structure `HasMinimalConnectiveAxioms` should live in `Equivalence.lean` or
  in a new `NaturalDeduction/Axioms.lean` if it is reused elsewhere

**Reuse check**: No existing structure in `Cslib.Foundations.Logic` bundles K + S + 6
connective axioms. `MinimalHilbert` bundles K + S + MP only, without connective axioms.
The and/or axioms appear as individual `HasAxiom*` typeclasses. The bundled structure
is new but local to the equivalence proof.

### 6. Relationship to `FromHilbert.lean` and `HilbertDerivedRules.lean`

- `FromHilbert.lean` provides Hilbert wrappers for `impI`, `impE`, `botE`, cut,
  weakening, substitution. Its `botE` takes an explicit `h_EFQ` -- this is correct
  and should not change (the Hilbert `botE` genuinely needs EFQ).

- `HilbertDerivedRules.lean` provides the and/or derived rules at the Hilbert level.
  Its rules are already parameterized with explicit witnesses and do not need changes.
  The `hilbertTopI` and `hilbertBotE` rules take `h_EFQ` -- correct, since `TopI` in
  the Hilbert system uses EFQ.

- `Equivalence.lean` is the only file where `h_EFQ` appears superfluously (in
  `ndToHilbert` and its wrappers).

### 7. `hilbert_to_nd_deriv` Needs No Changes

The Hilbert-to-ND direction (`hilbertToND`, `hilbert_to_nd_deriv`) requires zero
axiom witnesses. It works by structural induction on `DerivationTree` constructors
(ax, assumption, modus_ponens, weakening) and maps each to its ND counterpart. This
direction is already maximally generic and requires no changes.

---

## Recommended Approach

**Two-step refactor** (both in `Equivalence.lean`):

**Step 1: Remove h_EFQ from ndToHilbert** (mechanical change).
- Remove `h_EFQ` parameter from `ndToHilbert`, `nd_to_hilbert_deriv`, `hilbert_iff_nd`,
  `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`.
- Remove the 9 occurrences of `h_EFQ` in the recursive calls within `ndToHilbert`
  (lines 178-215 of current `Equivalence.lean`).
- This is a pure deletion -- no proof changes needed for any case.

**Step 2: Add `hilbert_iff_nd_ctx` (stronger, context-parametric theorem)** (new theorem).
- Rename current `hilbert_iff_nd` to `hilbert_iff_nd_empty` or keep it as the
  empty-context corollary.
- Add `hilbert_iff_nd_ctx` using `Deriv Axioms Γ.toList φ ↔ DerivableIn ... (Γ ⊢ φ)`.
- Add `hilbert_iff_nd_min` as a corollary.

**Optional Step 3: Introduce `HasMinimalConnectiveAxioms` structure** (ergonomic).
- Bundle the 8 witnesses into a structure.
- This improves readability but is not required for correctness.
- The structure is a `Prop`-valued structure (all fields are propositions), so no
  universe issues arise.

The key decision for the plan author: whether Step 3 is worth adding. Given that
CSLib already has `HasAxiom*` individual typeclasses and the 3 bundled classes in
`ProofSystem.lean`, a new `HasMinimalConnectiveAxioms` structure in `Equivalence.lean`
should be kept local (not exposed to the whole library) since it bundles the predicate
form `Axioms : Prop → Prop` rather than the tag form `S : Type*`.

---

## Evidence: Case Analysis of ndToHilbert

Looking at the body of `ndToHilbert` (Equivalence.lean lines 173-215):

```
| .ax h_mem =>          -- uses: no witnesses
| .ass h_mem =>         -- uses: no witnesses
| .andI ... d₁ d₂ =>   -- uses: h_andI (via hilbertAndI)
                        -- recursive calls pass h_EFQ but DON'T use it
| .andE1 ... d =>       -- uses: h_andE1 (via hilbertAndE1)
| .andE2 ... d =>       -- uses: h_andE2 (via hilbertAndE2)
| .orI1 ... d =>        -- uses: h_orI1 (via hilbertOrI1)
| .orI2 ... d =>        -- uses: h_orI2 (via hilbertOrI2)
| .orE ... d dA dB =>   -- uses: h_K, h_S, h_orE (via hilbertOrE)
| .impE d₁ d₂ =>        -- uses: no witnesses
| .impI ... d =>        -- uses: h_K, h_S (via deductionTheorem)
```

h_EFQ appears in recursive calls (passed to IH) but is **never applied** to produce
any Hilbert derivation. Lean's compiler treats unused function arguments as dead code,
but in a proof context the parameter must still be provided at call sites. After
removing h_EFQ, all internal recursive calls simply drop it.

Supporting evidence: `hilbertOrE` (HilbertDerivedRules.lean lines 229-252) takes only
`h_K`, `h_S`, `h_orE` -- no EFQ. `hilbertAndI`, `hilbertAndE1`, `hilbertAndE2`,
`hilbertOrI1`, `hilbertOrI2` take only their respective axiom witness -- no EFQ.
The `deductionTheorem` (DeductionTheorem.lean) takes only K and S -- no EFQ.

---

## Confidence Level

- **h_EFQ is unused in ndToHilbert**: HIGH (complete case analysis above)
- **Removing h_EFQ enables hilbert_iff_nd_min**: HIGH (MinPropAxiom has all 8 required axioms)
- **hilbert_iff_nd_ctx (context-parametric theorem) is achievable**: HIGH (hilbert_to_nd_deriv and nd_to_hilbert_deriv already work for any Γ)
- **Structure bundling approach works**: HIGH (Prop-valued structure, no universe issues)
- **Typeclass-based approach alternative**: MEDIUM (requires connecting the Axioms-predicate world to the S-tag typeclass world, which adds complexity without benefit for this specific equivalence)
- **Step 1 alone is zero-risk**: HIGH (pure deletion, no proof strategy changes)
