# Teammate B Findings: Alternative Patterns and Prior Art
## Task 172 — Hybrid Five-Primitive Signature for PL

---

## Key Findings

### 1. No HasAnd / HasOr Classes Exist Yet — And May Not Be Needed

The CSLib reuse-first check is unambiguous: `lean_local_search` for `HasAnd` returns nothing in
CSLib; `HasOr` returns only Mathlib matrix entries. The `Cslib.Foundations.Logic.Connectives`
module currently has:

- `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` — atomic classes
- `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` — bundles
- `ImpBotDerived` — derives `neg/top/or/and` from `bot/imp`, currently intentionally uninstantiated

The design note in `Connectives.lean` is explicit: `ImpBotDerived` is "retained as a specification
artifact and for potential future use in polymorphic proof-system abstractions." This suggests adding
`HasAnd` and `HasOr` as new atomic classes in `Connectives.lean`, bundling them into a new
`FullPropositionalConnectives` class (or extending `PropositionalConnectives`), and ensuring
`PL.Proposition` is updated to register these as constructors and instances.

**Recommendation**: Task 172 should add `HasAnd (F : Type*) where and : F → F → F` and
`HasOr (F : Type*) where or : F → F → F` alongside existing classes. The bundled extension could
be `FullPropConnectives` extending `PropositionalConnectives`, `HasAnd`, and `HasOr`.

### 2. Hilbert Axiom Extension Pattern — Six New Axioms at MinPropAxiom Level

The standard Hilbert axioms for primitive and/or are all valid in minimal logic:

**Conjunction** (three axioms):
- `andI (φ ψ : Prop) : MinPropAxiom (φ → ψ → φ ∧ ψ)` — introduction
- `andE1 (φ ψ : Prop) : MinPropAxiom (φ ∧ ψ → φ)` — left elimination
- `andE2 (φ ψ : Prop) : MinPropAxiom (φ ∧ ψ → ψ)` — right elimination

**Disjunction** (three axioms):
- `orI1 (φ ψ : Prop) : MinPropAxiom (φ → φ ∨ ψ)` — left introduction
- `orI2 (φ ψ : Prop) : MinPropAxiom (ψ → φ ∨ ψ)` — right introduction
- `orE (φ ψ χ : Prop) : MinPropAxiom ((φ → χ) → (ψ → χ) → φ ∨ ψ → χ)` — elimination

These 6 axioms are all derivable in minimal logic with the Lukasiewicz encoding and {K, S}
alone (conjunction) or with {K, S, EFQ, Peirce} (disjunction elimination in its current form).
With primitive `and`/`or`, all 6 are valid even in minimal logic, so they should all be added to
`MinPropAxiom`. `IntPropAxiom` and `PropositionalAxiom` inherit them via their subsumption
theorems.

**Pattern for Axioms.lean**:
```lean
inductive MinPropAxiom : FivePrimProposition Atom → Prop where
  | implyK  (φ ψ : ...)   : MinPropAxiom (φ.imp (ψ.imp φ))
  | implyS  (φ ψ χ : ...) : MinPropAxiom ((φ.imp (ψ.imp χ)).imp ...)
  | andI    (φ ψ : ...)   : MinPropAxiom (φ.imp (ψ.imp (φ.and ψ)))
  | andE1   (φ ψ : ...)   : MinPropAxiom ((φ.and ψ).imp φ)
  | andE2   (φ ψ : ...)   : MinPropAxiom ((φ.and ψ).imp ψ)
  | orI1    (φ ψ : ...)   : MinPropAxiom (φ.imp (φ.or ψ))
  | orI2    (φ ψ : ...)   : MinPropAxiom (ψ.imp (φ.or ψ))
  | orE     (φ ψ χ : ...) : MinPropAxiom ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ)))
```
`IntPropAxiom` adds `efq`; `PropositionalAxiom` adds `peirce`. The subsumption theorems
(`MinPropAxiom.toIntProp`, `IntPropAxiom.toProp`) gain 6 new cases each, all trivial.

### 3. The DerivedRules and HilbertDerivedRules Files Are Already Complete — No Changes Needed

A key insight: `DerivedRules.lean` and `HilbertDerivedRules.lean` provide `andI/andE1/andE2/
orI1/orI2/orE` as *derived rules from K/S/EFQ/Peirce using the Lukasiewicz encoding*. These
currently require `[IsClassical T]` for elimination rules because the Lukasiewicz encoding of
`and`/`or` is only classically equivalent to the standard definitions.

With the five-primitive extension, the situation changes:
- These derived rules in `DerivedRules.lean` operate on `PL.Proposition` (the three-primitive
  type `{atom, bot, imp}`). They still work correctly on the existing type.
- The **new Hilbert system** for `FivePrimProposition` will have `andI/andE1/andE2/orI1/orI2/orE`
  as **axioms** rather than derived rules. The analogous "derived rules" file for the new type
  will be trivial wrappers around those axioms — no complex derivations needed.

This means the `IsClassical T` restriction on elimination rules disappears in the new system:
`andE1`, `andE2`, `orE` become available in minimal logic once `and`/`or` are primitive.

### 4. The ND System (Theory.Derivation) Must Be Preserved Exactly

`NaturalDeduction/Basic.lean` contains `Theory.Derivation` with exactly 5 constructors:
`ax`, `ass`, `impI`, `impE`, `botE`. The user's requirement to keep this "exactly as-is upstream"
means:

- The `PL.Proposition` type (`{atom, bot, imp}`) does NOT change.
- `Theory.Derivation` does NOT change.
- `DerivedRules.lean` does NOT change (still works for the existing 3-primitive type).

The five-primitive extension creates a **parallel** formula type (e.g., `FivePrimProposition` or
`PL5.Proposition`) with its own Hilbert system. The `Equivalence.lean` `hilbert_iff_nd` theorem
is a bridge between the Hilbert system and the ND system for the same formula type. Since both
the Hilbert system and the ND system will now change formula type, the equivalence theorem must
be re-examined.

**Critical decision**: Does task 172 create a new formula type, or extend the existing
`PL.Proposition`? The current `Connectives.lean` comment says "Falsum and implication are taken
as the only propositional primitives because `{imp, bot}` is functionally complete." If we
extend `PL.Proposition` to add `and`/`or` constructors, the ND derivation must also be extended
(adding `andI`/`andE1`/`andE2`/`orI1`/`orI2`/`orE` constructors). But the user wants the ND
system preserved exactly. Therefore:

**The five-primitive extension requires a new formula type alongside the existing one.**

### 5. Equivalence Between Derived and Primitive: What Needs Proving

The key equivalence theorems required:

**Lukasiewicz embedding**: There is a map `embed : PL.Proposition Atom → FivePrimProposition Atom`
that is the identity on `atom`, `bot`, `imp`, and maps `and`/`or` to their Lukasiewicz encodings.

**Soundness of embedding for proofs**: Any Hilbert derivation using `PropositionalAxiom` over
`PL.Proposition` translates to a derivation using the new axioms over `FivePrimProposition`.

**The exact equivalence** (theorem `hilbert_iff_nd` update): Since `Theory.Derivation` operates
over `PL.Proposition` (the 3-primitive type), the equivalence for the new Hilbert system connects:
- `Derivable FivePrimAxiom φ` (Hilbert derivability for 5-primitive formulas)
- `DerivableIn (AxiomTheory FivePrimAxiom) (∅ ⊢ embed⁻¹(φ))` (ND derivability after translating
  back to the 3-primitive type, for classically equivalent formulas)

**The ND-to-Hilbert direction**: `ndToHilbert` currently requires explicit K, S, EFQ witnesses.
For the new axiom system, it additionally needs and/or axiom witnesses. The proof strategy
in `hilbert_iff_nd` — using the deduction theorem — still works because the new Hilbert system
still has K and S.

### 6. IForces Must Be Extended for Kripke Soundness/Completeness

The current `IForces` in `Kripke.lean` has exactly 3 cases: `atom`, `bot`, `imp`. With primitive
`and`/`or`, it must be extended:

```lean
def IForces [Preorder World] ... (w : World) : FivePrimProposition Atom → Prop
  | .atom p => v w p
  | .bot => bot_forces w
  | .imp φ ψ => ∀ w', w ≤ w' → IForces v bot_forces w' φ → IForces v bot_forces w' ψ
  | .and φ ψ => IForces v bot_forces w φ ∧ IForces v bot_forces w ψ
  | .or φ ψ => IForces v bot_forces w φ ∨ IForces v bot_forces w ψ
```

**Critical difference from current**: The current system defines `and A B := ¬(A → ¬B)` and
`or A B := ¬A → B`, so their forcing conditions unfold through `imp`/`bot`. The new system uses
the **standard Kripke semantics** for `and`/`or`:
- `w ⊩ A ∧ B iff w ⊩ A and w ⊩ B` — this is persistent because both conjuncts are persistent.
- `w ⊩ A ∨ B iff w ⊩ A or w ⊩ B` — this is persistent if either disjunct is persistent.

These are genuinely different from the current IForces behavior (where and/or unfold to imp/bot).
The persistence lemma `iforces_persistence` gains 2 new induction cases.

**Soundness for new axioms**: The 6 new axioms have immediate semantic proofs:
- `andI`: `w ⊩ A → ψ → A ∧ B` — trivially, if `w' ⊩ A` and `w'' ⊩ B`, then pair them.
- `andE1`: `w ⊩ A ∧ B → A` — project left.
- `andE2`: `w ⊩ A ∧ B → B` — project right.
- `orI1`: `w ⊩ A → A ∨ B` — left injection.
- `orI2`: `w ⊩ B → A ∨ B` — right injection.
- `orE`: `w ⊩ (A → C) → (B → C) → A ∨ B → C` — case analysis.

### 7. Completeness Strategy: Truth Lemma Update

The truth lemma in `MinCompleteness.lean` currently handles 3 cases (atom, bot, imp). With the
5-primitive formula type, it needs 5 cases. The `and`/`or` cases should be:
- `and`: `IForces val bf S (A ∧ B) ↔ A ∧ B ∈ S.val` — the forward direction uses `andE1`/`andE2`
  in the Hilbert system; the backward direction uses `andI`.
- `or`: `IForces val bf S (A ∨ B) ↔ A ∨ B ∈ S.val` — similar.

The MinTheory/IntDCCS canonicity conditions need to be checked for closure under `and`/`or`
introduction/elimination rules.

### 8. Substitution Lemma Updates

Three substitution lemmas in `FromHilbert.lean` need extending:
- `subst_preserves_axiom` — gains 6 new cases (andI, andE1, andE2, orI1, orI2, orE)
- `subst_preserves_intAxiom` — same 6 cases
- `subst_preserves_minAxiom` — same 6 cases

Pattern for each new case (e.g., `andI`):
```lean
| andI a b => exact .andI (a.subst f) (b.subst f)
```
These are all trivial `cases h with | ... => exact .constructor ...` patterns.

Also, `Proposition.subst` in `Defs.lean` needs cases for `and`/`or`:
```lean
| and A B => .and (A.subst f) (B.subst f)
| or A B => .or (A.subst f) (B.subst f)
```

And `DecidableEq`/`BEq` derivation must be re-checked (should work automatically via `deriving`
for the new constructors if they are added to the inductive).

---

## Recommended Approach

The recommended strategy for task 172 is a **parallel formula type with Hilbert extension**, not
modification of `PL.Proposition` or `Theory.Derivation`:

**Phase 1: Connectives.lean** — Add `HasAnd`, `HasOr` atomic typeclasses; optionally add
`FullPropConnectives` bundle extending `PropositionalConnectives`, `HasAnd`, `HasOr`.

**Phase 2: New formula type** — Create `FivePrimProposition` (or extend `PL.Proposition` by
renaming the old type) as an inductive with 5 constructors: `atom`, `bot`, `imp`, `and`, `or`.
Register `HasAnd`/`HasOr` instances. Extend `Proposition.subst` and `DecidableEq/BEq`.

**Phase 3: New Hilbert axioms** — Extend `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`
with 6 new constructors (andI, andE1, andE2, orI1, orI2, orE) for the 5-primitive formula type.
Update subsumption theorems to handle 6 new cases.

**Phase 4: IForces extension** — Add `and`/`or` cases to `IForces`; update persistence lemma.
New cases require 2 new induction steps (both trivial).

**Phase 5: Axiom soundness** — Extend soundness lemmas with 6 new axiom cases. All proofs are
structurally simple (direct introduction/projection).

**Phase 6: Equivalence with ND** — State and prove the equivalence between the 5-primitive
Hilbert system and the existing `Theory.Derivation` ND system. This requires:
a. A translation `toThreePrim : FivePrimProposition → PL.Proposition` (Lukasiewicz encoding)
b. An ND derivation of `andI`/`andE1`/`andE2` (logic-neutral) and `orI1`/`orI2`/`orE`
   (classical) for the three-primitive encoding of the same formula.

**Key insight**: The `hilbert_iff_nd` equivalence still holds parametrically — the generic
theorem `hilbert_iff_nd` in `Equivalence.lean` requires only K, S, EFQ witnesses, and those
are all present in `MinPropAxiom`/`IntPropAxiom`/`PropositionalAxiom`. No changes to
`Equivalence.lean` are needed! The corollary instantiation for the new axiom systems just
requires adding instances for K, S, and EFQ.

---

## Evidence and Examples

### Evidence 1: ImpBotDerived Shows Exact Lukasiewicz Encoding

From `Connectives.lean` (lines 104-113), the `ImpBotDerived` class gives the exact definitions
that must be used for the equivalence:
- `and φ ψ := imp (imp φ (imp ψ bot)) bot` — i.e., `¬(A → ¬B)`
- `or φ ψ := imp (imp φ bot) ψ` — i.e., `¬A → B`

These are what the current `DerivedRules.lean` rules work with. The five-primitive extension
uses **primitive** `and`/`or` constructors instead, but the Lukasiewicz definition is still the
translation function `toThreePrim`.

### Evidence 2: andE1/andE2 Currently Require IsClassical

From `DerivedRules.lean` (lines 143-192), `andE1` and `andE2` both require `[IsClassical T]`
because they route through `dne` (double negation elimination). This is the Lukasiewicz
encoding's limitation. With primitive `and`, both eliminations are minimal-logic axioms —
no classical reasoning needed.

### Evidence 3: hilbert_iff_nd Is Already Generic

From `Equivalence.lean` (lines 189-205), `hilbert_iff_nd` is parameterized over any `Axioms`
predicate with explicit K, S, EFQ witnesses. The new axiom systems (with 8/9/10 constructors)
satisfy K (`implyK`), S (`implyS`), and EFQ (`efq`) for all three levels including minimal.
Therefore `hilbert_iff_nd` applies without modification for the new axiom system, producing the
correct equivalence corollaries once the formula type translation is handled.

### Evidence 4: Persistence Is Closed Under and/or

From `Kripke.lean` (lines 93-104), `iforces_persistence` proves by structural induction. The
`and`/`or` cases are:
- `and`: persistence of `A ∧ B` at `w'` follows from persistence of `A` (IH) and persistence
  of `B` (IH), then pairing.
- `or`: persistence of `A ∨ B` at `w'` follows from persistence of either disjunct (IH on the
  inhabited one).

Both cases are straightforward. The proof requires no new lemmas — just `And.intro` /
`Or.inl` / `Or.inr` on the IH results.

### Evidence 5: Soundness for New Axioms Is Trivial

For `min_axiom_sound`, the 6 new axiom cases have short proofs:
```lean
| andI φ ψ =>
  -- Goal: IForces w (φ → ψ → φ ∧ ψ)
  intro w' hw' hφ w'' hw'' hψ
  exact ⟨iforces_persistence ... (le_trans hw' hw'') hφ, hψ⟩
| andE1 φ ψ =>
  intro w' _ h; exact h.1
| andE2 φ ψ =>
  intro w' _ h; exact h.2
| orI1 φ ψ =>
  intro w' _ h; exact Or.inl h
| orI2 φ ψ =>
  intro w' _ h; exact Or.inr h
| orE φ ψ χ =>
  intro w₁ hw₁ hAC w₂ hw₂ hBC w₃ hw₃ hAB
  rcases iforces_persistence ... hw₃ hAB with hA | hB
  · exact hAC w₃ (le_trans hw₂ hw₃) hA w₃ le_refl hA -- impE style
  · exact hBC w₃ hw₃ hB w₃ le_refl hB
```
(Exact Lean syntax needs adjustment for the Kripke `IForces` convention with world quantifiers.)

---

## Confidence Level

**High confidence** on structural findings:
- Reuse check is complete: no existing `HasAnd`/`HasOr` in CSLib.
- The parallel formula type requirement (to preserve ND exactly) is forced by the user's constraint.
- The 6-axiom extension at `MinPropAxiom` level is standard and uncontroversial.
- `hilbert_iff_nd` is already generic and requires no changes to the proof.

**Medium confidence** on implementation specifics:
- Whether `FivePrimProposition` should be a new inductive in `Defs.lean` or a new namespace
  depends on how the task scopes the refactor. Task 172 may be intended only for
  `Connectives.lean` (typeclass layer), with downstream changes in tasks 173-178.
- The exact formulation of the equivalence (type translation vs. same formula type) depends on
  how the ND preservation constraint is interpreted.
- The `orE` soundness proof in the Kripke setting requires care: the or-forcing is `w ⊩ A ∨ B`
  meaning `IForces w A ∨ IForces w B`. The axiom `orE` states `(A → C) → (B → C) → A ∨ B → C`.
  Verifying this in Kripke semantics requires `IForces w (A → C)` means universal quantification
  over successors, so applying it at `w' = w` with `le_refl w` is sufficient.

**Low confidence** on:
- Whether the task intends to keep the current `Defs.lean` formula type unchanged with `and`/`or`
  continuing as abbreviations, vs. actually adding new constructors. If `and`/`or` remain
  abbreviations, the "five primitive" signature is notational only, not structural, and the
  Hilbert axioms for `and`/`or` become derivable lemmas rather than constructors of `MinPropAxiom`.
  This would be a much smaller change but would not achieve the stated goal of "primitives."

**Final recommendation**: Confirm with the user whether the intent is (a) strictly syntactic
extension (new constructors in the formula inductive), or (b) axiomatic extension (add axioms
for and/or to the Hilbert system while keeping them as abbreviations). Option (b) is sound and
requires less change; option (a) requires a new formula type and all downstream updates.
