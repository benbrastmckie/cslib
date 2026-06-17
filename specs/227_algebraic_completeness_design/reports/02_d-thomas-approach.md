# Teammate D Report: Thomas Waring's cslib_SKI Algebraic Semantics Design

## Session
- **Task**: 227 (Algebraic Completeness Design)
- **Session**: sess_1750130000_research227
- **Focus**: Thomas Waring's `cslib_SKI` Heyting.lean -- design choices, completeness theorem, tradeoffs vs our approach.

---

## 1. Thomas's Design: Core Architecture

### 1.1 Proposition Type (Defs.lean)

Thomas's `Proposition` has **four constructors** -- no primitive `bot`:

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
  | impl (a b : Proposition Atom)
```

Bottom is recovered via a `[Bot Atom]` typeclass instance:

```lean
instance instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩
```

So `(⊥ : Proposition Atom) = .atom ⊥` -- falsum is literally an atom. Negation is then `Proposition.neg [Bot Atom] := (Proposition.impl · ⊥)`, exactly as in our version, but the `⊥` here is `atom ⊥`, not a dedicated constructor.

Top is also derived: `Proposition.top [Inhabited Atom] := impl (.atom default) (.atom default)` -- the identity implication on the default atom.

### 1.2 Valuation and Evaluation (Heyting.lean)

Thomas defines:

```lean
abbrev Valuation (Atom : Type*) (H : Type*) := Atom → H

def Valuation.interp {H : Type _} [GeneralizedHeytingAlgebra H] (v : Valuation Atom H) :
    Proposition Atom → H
  | atom x => v x
  | Proposition.and A B => (v.interp A) ⊓ (v.interp B)
  | Proposition.or A B => (v.interp A) ⊔ (v.interp B)
  | impl A B => (v.interp A) ⇨ (v.interp B)
```

Key observation: **there is no `bot` case** in `Valuation.interp` because `⊥` is `atom ⊥`, so it falls through to `| atom x => v x`. The value of `⊥` under the valuation is simply `v ⊥`, which is whatever the valuation assigns to the bottom atom.

This is the crux of the design: the valuation `v : Atom → H` controls the interpretation of `⊥` as a side effect of interpreting atoms. There is no separate `bot_val` parameter.

### 1.3 Validity Predicates

Thomas defines validity via `v ⊨ A` (meaning `v⟦A⟧ = ⊤`) and `v ⊨ T` (meaning every axiom evaluates to `⊤`):

```lean
def Valuation.PValid (A : Proposition Atom) : Prop := v⟦A⟧ = ⊤
def Valuation.TValid (T : Theory Atom) : Prop := ∀ A ∈ T, v.PValid A
```

### 1.4 Theory-Parametric Completeness

The crown jewel:

```lean
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

This says: `A` is derivable from theory `T` if and only if every GHA valuation that models all axioms of `T` also models `A`. The `v ⊨ T` hypothesis does all the work of specialization.

### 1.5 Specialization to Logic Tiers

**MPL** (minimal logic, `T = MPL = ∅`):

```lean
theorem MPL.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn (MPL (Atom := Atom)) A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, v ⊨ A
```

Since `MPL = ∅`, the hypothesis `v ⊨ MPL` is trivially true for any `v`, so it drops out. The `v ⊨ MPL` direction is proved by `Valuation.MPL_valid` which is trivially `by grind`.

**IPL** (intuitionistic logic, `T = IPL = Set.range (⊥ → ·)`):

```lean
theorem IPL.complete [Bot Atom] {A : Proposition Atom} :
    DerivableIn (IPL (Atom := Atom)) A ↔
    ∀ {H : Type u} [HeytingAlgebra H] {v : Valuation Atom H}, v ⊥ = ⊥ → v ⊨ A
```

Here the constraint upgrades from GHA to HA, and the `v ⊨ IPL` condition simplifies to `v ⊥ = ⊥`. This is because `IPL = Set.range (⊥ → ·)`, so `v ⊨ IPL` means `∀ A, v⟦⊥ → A⟧ = ⊤`, i.e., `∀ A, v(⊥) ⇨ v⟦A⟧ = ⊤`, i.e., `∀ A, v(⊥) ≤ v⟦A⟧`. In a HeytingAlgebra, the only element below everything is `⊥`, so `v ⊥ = ⊥`.

**CPL** (classical logic, `T = CPL = Set.range (¬¬· → ·)`):

```lean
theorem CPL.complete [Bot Atom] {A : Proposition Atom} :
    DerivableIn (CPL (Atom := Atom)) A ↔
    ∀ {B : Type u} [BooleanAlgebra B] {v : Valuation Atom B}, v ⊥ = ⊥ → v ⊨ A
```

Same pattern: BooleanAlgebra + `v ⊥ = ⊥`.

---

## 2. Thomas's Lindenbaum Algebra Construction

### 2.1 The Quotient Algebra

Thomas builds the Lindenbaum algebra as `Quotient T.propositionSetoid` where the setoid identifies provably equivalent propositions. He then constructs:

1. **`propPO`**: Partial order via `⟦A⟧ ≤ ⟦B⟧ ↔ DerivableIn T ({A} ⊢ B)`
2. **`propLattice`**: Lattice with `⟦A⟧ ⊔ ⟦B⟧ = ⟦A ∨ B⟧` and `⟦A⟧ ⊓ ⟦B⟧ = ⟦A ∧ B⟧`
3. **`propGeneralizedHeyting`**: GHA with `⊤ = ⟦⊤⟧` and `⟦A⟧ ⇨ ⟦B⟧ = ⟦A → B⟧`
4. **`propHeyting`** (requires `[Bot Atom]` + `[IsIntuitionistic T]`): HA with `⊥ = ⟦⊥⟧` and `bot_le` from EFQ
5. **`propBoolean`** (requires `[Bot Atom]` + `[IsClassical T]`): BA via `BooleanAlgebra.ofRegular` -- every element is Heyting-regular because DNE holds

### 2.2 Canonical Valuation and Completeness Proof

```lean
def Theory.canonicalV (T : Theory Atom) : Valuation Atom (Quotient T.propositionSetoid) :=
  fun x => ⟦atom x⟧

theorem Theory.canonicalV_spec [Inhabited Atom] (A : Proposition Atom) :
    T.canonicalV.interp A = ⟦A⟧
```

The canonical valuation maps each atom `x` to its equivalence class `⟦atom x⟧`. The spec lemma proves this extends to all propositions: evaluation under `canonicalV` produces the equivalence class. This is a clean structural induction.

The completeness proof then says: if `∀ v, (v ⊨ T) → v ⊨ A`, instantiate with `v = T.canonicalV` in the Lindenbaum algebra. Since `T.canonicalV ⊨ T` (every axiom maps to `⊤` in the quotient), we get `T.canonicalV ⊨ A`, meaning `⟦A⟧ = ⊤`, meaning `A` is derivable.

### 2.3 The `propBooleanOfLE` Trick

For classical logic, Thomas uses Mathlib's `BooleanAlgebra.ofRegular` which shows that a HeytingAlgebra where every element satisfies `¬¬a = a` (Heyting-regular) is a BooleanAlgebra. He proves regularity of the Lindenbaum quotient from the DNE axiom of CPL. This avoids building the Boolean algebra structure from scratch.

---

## 3. Head-to-Head Comparison

### 3.1 Proposition Type

| Aspect | Our approach (primitive ⊥) | Thomas (⊥ as atom via `[Bot Atom]`) |
|--------|---------------------------|--------------------------------------|
| Constructors | 5: `atom`, `bot`, `imp`, `and`, `or` | 4: `atom`, `and`, `or`, `impl` |
| Bot instance | `Bot (Proposition Atom) := ⟨.bot⟩` | `Bot (Proposition Atom) := ⟨.atom ⊥⟩` (requires `[Bot Atom]`) |
| Top | `⊤ := .imp .bot .bot` | `⊤ := impl (.atom default) (.atom default)` (requires `[Inhabited Atom]`) |
| Pattern matching | 5 arms everywhere | 4 arms, but `⊥` is hidden inside `atom` |
| MPL expressibility | MPL has `⊥` intrinsically | MPL can exist without `⊥` (no `[Bot Atom]` needed) |

### 3.2 Evaluation Function

| Aspect | Our `AlgEvaluate` | Thomas's `Valuation.interp` |
|--------|-------------------|----------------------------|
| Parameters | `v : Atom → H`, `bot_val : H` | `v : Atom → H` (just the valuation) |
| Bot handling | Explicit: `| .bot => bot_val` | Implicit: `| atom x => v x` (and `⊥ = atom ⊥`) |
| No-⊥ logic | Works (bot_val is free) | Natural (no `[Bot Atom]` needed) |
| Code complexity | Slightly more (extra parameter) | Cleaner (one fewer parameter) |

### 3.3 Completeness Statement

| Aspect | Our approach (planned) | Thomas's `Theory.complete` |
|--------|----------------------|---------------------------|
| General form | Not yet formalized | `DerivableIn T A ↔ ∀ [GHA H] v, (v ⊨ T) → v ⊨ A` |
| MPL specialization | `GHAValid φ` (∀ H v bot_val, evaluate = ⊤) | `∀ [GHA H] v, v ⊨ A` (v ⊨ MPL drops out) |
| IPL specialization | `HAValid φ` (∀ H v, evaluate v ⊥ = ⊤) | `∀ [HA H] v, v ⊥ = ⊥ → v ⊨ A` |
| CPL specialization | `BAValid φ` (∀ H v, evaluate v ⊥ = ⊤) | `∀ [BA B] v, v ⊥ = ⊥ → v ⊨ A` |
| Elegance | Three separate predicates | One theorem, parametric in T |

### 3.4 Lindenbaum Construction

| Aspect | Our approach | Thomas's approach |
|--------|-------------|-------------------|
| Current status | `MinLindenbaum.lean`: prime exclusion via Zorn, but Hilbert-style | Full Lindenbaum algebra as GHA/HA/BA quotient |
| Proof style | DeductionTree-based, hand-rolled DT | Natural deduction (Derivation inductive), algebraic |
| GHA structure | Not yet built | `propGeneralizedHeyting` instance |
| HA/BA upgrade | Not yet built | `propHeyting`, `propBoolean` via `BooleanAlgebra.ofRegular` |
| Completeness | Strong completeness via Kripke canonical model | Direct via Lindenbaum algebra canonical valuation |

---

## 4. The Key Design Question: Formal Equivalence

### 4.1 Are the Two Approaches Formally Equivalent?

**Yes, for any logic with `⊥`.** Given our `(v : Atom → H, bot_val : H)` pair, define Thomas's valuation as:

```
v' : (Atom ⊕ {⊥}) → H := fun | .inl a => v a | .inr ⊥ => bot_val
```

(or more precisely, if `Atom` has a `Bot` instance, `v' : Atom → H` where `v' a = v a` for non-⊥ atoms and `v' ⊥ = bot_val`).

Conversely, given Thomas's `v : Atom → H` (with `[Bot Atom]`), extract:
- Our atom valuation: `fun a => v a` restricted to non-⊥ atoms
- Our `bot_val`: `v ⊥`

Under these correspondences, `AlgEvaluate v bot_val φ = Valuation.interp v' (embed φ)` where `embed` maps our `Proposition` to Thomas's by replacing `.bot` with `.atom ⊥`.

**For MPL without `⊥`**: Thomas's approach is strictly more general. His `Proposition Atom` does not require `[Bot Atom]`, so MPL exists over any atom type. Our `Proposition` always has `.bot`, so we always have `⊥` in the language even for MPL. The `bot_val` parameter in `AlgEvaluate` effectively quantifies over all possible interpretations of this `⊥`, which is equivalent to Thomas's "no constraint on `v ⊥`" in the `[Bot Atom]` setting, but is conceptually less clean because it forces `⊥` into the language.

### 4.2 Which Framing is Better for Completeness?

Thomas's `v ⊨ T` framing is superior for the following reasons:

1. **Uniformity**: One theorem parametric in `T`, not three separate predicates.
2. **Extensibility**: Adding a new theory `T'` (say, intuitionistic logic + Peirce's law for classical) requires only proving `v ⊨ T'` -- no new validity predicate needed.
3. **Natural specialization**: The hypothesis `v ⊨ T` automatically constrains the valuation to the right algebra class. For MPL, it imposes no constraint. For IPL, it forces `v ⊥ = ⊥`. For CPL, it forces regularity.
4. **Clean proof**: The Lindenbaum completeness proof is direct -- instantiate with the canonical valuation and observe `canonicalV ⊨ T`.

Our `bot_val` framing requires three separate predicates (`GHAValid`, `HAValid`, `BAValid`) with different shapes, and the MPL case quantifies over a free variable (`bot_val`) that has no natural algebraic interpretation -- it is neither `⊥` (GHA lacks one) nor constrained to any value.

---

## 5. The `v ⊨ T` Approach vs `bot_val` Approach: Detailed Formal Comparison

### 5.1 MPL: The Key Divergence

**Thomas**: `∀ [GHA H] v, v ⊨ A` -- valid in all GHA valuations, period. No mention of `⊥`.

**Ours**: `∀ [GHA H] v (bot_val : H), AlgEvaluate v bot_val φ = ⊤` -- quantifies over `bot_val`.

These are equivalent when `[Bot Atom]` exists: any `bot_val` corresponds to choosing `v' ⊥ = bot_val`. But Thomas's statement is cleaner because:
- When `Atom` has no `Bot`, Thomas's MPL just does not mention `⊥` at all
- When `Atom` has `Bot`, Thomas's `v ⊥` is free (no `v ⊨ MPL` constraint limits it), which is the same as our free `bot_val`

### 5.2 IPL: Essentially Identical

**Thomas**: `∀ [HA H] v, v ⊥ = ⊥ → v ⊨ A`

**Ours**: `∀ [HA H] v, AlgEvaluate v ⊥ φ = ⊤` (i.e., `HAValid`)

These are definitionally the same once you note `AlgEvaluate v ⊥ φ = Valuation.interp v' φ` when `v' ⊥ = ⊥`.

### 5.3 CPL: Essentially Identical

Same equivalence as IPL, with BooleanAlgebra replacing HeytingAlgebra.

---

## 6. Could We Have BOTH? Hybrid Design Analysis

### 6.1 Option: Keep Primitive ⊥, Use Thomas's Completeness Style

This is viable. The evaluation function would be:

```lean
def AlgEvaluate {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : PL.Proposition Atom → H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => AlgEvaluate v bot_val a ⇨ AlgEvaluate v bot_val b
  | .and a b => AlgEvaluate v bot_val a ⊓ AlgEvaluate v bot_val b
  | .or a b => AlgEvaluate v bot_val a ⊔ AlgEvaluate v bot_val b
```

And completeness could be stated as:

```lean
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Atom → H} {bot_val : H},
      (∀ B ∈ T, AlgEvaluate v bot_val B = ⊤) → AlgEvaluate v bot_val A = ⊤
```

This keeps our 5-constructor `Proposition` (preserving all 257 downstream pattern matches), uses the `v ⊨ T` style for the completeness statement, and passes `bot_val` explicitly.

**Tradeoff**: Less elegant than Thomas's version because `bot_val` is a visible parameter. But it works and does not require refactoring the `Proposition` type.

### 6.2 Option: Adopt Thomas's Proposition Type (Massive Refactor)

Replacing `.bot` with `[Bot Atom]` across the codebase would affect:
- 257 pattern match sites across Bimodal, LTL, Temporal logics
- Every file that defines formulas with `⊥`
- Modal logics would need `[Bot Atom]` threaded everywhere

This is prohibitively expensive and would break CSLib's downstream modules.

### 6.3 Option: Bridge Layer

Keep both `Proposition` types. Define an embedding:

```lean
def embedProposition [Bot Atom] : (our) Proposition Atom → (Thomas) Proposition Atom
  | .atom x => .atom x
  | .bot => .atom ⊥
  | .imp a b => .impl (embedProposition a) (embedProposition b)
  | .and a b => .and (embedProposition a) (embedProposition b)
  | .or a b => .or (embedProposition a) (embedProposition b)
```

Then prove `AlgEvaluate v bot_val φ = Valuation.interp v' (embedProposition φ)` where `v' = fun a => if a = ⊥ then bot_val else v a` (with appropriate Bot instance).

This preserves all existing code and allows importing Thomas's completeness results. But it adds a translation layer that complicates the API.

### 6.4 Recommended Option

**Option 6.1 (keep primitive ⊥, adopt `v ⊨ T` style)** is the pragmatic choice. It:
- Preserves all 257 downstream pattern match sites
- Gains the parametric completeness statement
- Requires only changing the completeness statement, not the `Proposition` type
- The `bot_val` parameter is visible but natural -- it is the designated interpretation of `⊥` in a given algebra

---

## 7. Thomas's Quote Explained

Thomas writes:
> "with that definition of evaluate completeness is no longer true for minimal logic -- this (i think) is why Benjamin's Kripke definitions need separate fields for the valuation of atoms and of bottom, which is avoided by just making ⊥ an atom itself."

**Translation**: With primitive `⊥` in `Proposition`, the evaluation function has a `bot_val` parameter. For MPL completeness, you must quantify over all possible `bot_val` values (since `⊥` can evaluate to anything in a GHA). This creates the asymmetry between atoms (valued by `v`) and `⊥` (valued by `bot_val`).

In the Kripke setting, this manifests as `KripkeModel` having both `v : World → Atom → Prop` and `botForces : World → Prop` as separate fields. In Thomas's setting, `botForces` would just be `v w ⊥` -- no separate field needed.

Thomas is correct that this is a direct consequence of the `Proposition` type design. The question is whether the cost (extra parameter, dual fields) is worth the benefit (no `[Bot Atom]` threading, 5th constructor for pattern matching clarity).

> "for reference... the general completeness theorem is:
> `DerivableIn T A ↔ ∀ {H} [GeneralizedHeytingAlgebra H] {v}, (v ⊨ T) → v ⊨ A`"

This is indeed very neat. The `v ⊨ T` hypothesis subsumes all logic-specific constraints.

> "you can remove the v ⊨ T hypothesis for T = IPL (resp CPL) by requiring that H is a HeytingAlgebra (resp BooleanAlgebra) and that v ⊥ = ⊥."

This shows how specialization works: the `v ⊨ T` hypothesis for `IPL` is equivalent to upgrading GHA to HA and requiring `v ⊥ = ⊥`. The algebra class absorbs part of the constraint.

> "Note that in Benjamin's development a similar thing happens, where ISemanticConsequence specialises IForces by requiring that ⊥ is never forced."

Yes: our `IValid` sets `botForces = fun _ => False`, which in Thomas's framework corresponds to `v ⊥ = ⊥` in the HA (since `⊥` being never forced is the Kripke analogue of `v ⊥ = ⊥` in the algebraic setting).

---

## 8. Lindenbaum Algebra: What Thomas Has That We Need

### 8.1 Structures We Lack

Thomas has the full Lindenbaum algebra hierarchy:
- `propPO`: Partial order on `Quotient T.propositionSetoid`
- `propLattice`: Lattice structure
- `propGeneralizedHeyting`: GHA structure (for any theory `T`)
- `propHeyting`: HA structure (when `T` is intuitionistic)
- `propBoolean`: BA structure (when `T` is classical)

We have none of this. Our `MinLindenbaum.lean` works at the set-theoretic level (prime theories, Zorn's lemma) for Kripke completeness, but does not build algebraic structure on the quotient.

### 8.2 Thomas's `BooleanAlgebra.ofRegular` Usage

For classical completeness, Thomas uses Mathlib's `BooleanAlgebra.ofRegular` which requires showing every element of the Lindenbaum algebra is Heyting-regular (`¬¬a = a`). He proves this from the DNE axiom. This is a clean approach that avoids constructing the Boolean complement directly.

### 8.3 Thomas's Hom Section

Thomas also defines:

```lean
theorem GeneralizedHeytingHom.map_interpret (f : GeneralizedHeytingHom H H')
    (A : Proposition Atom) (v : Valuation Atom H) : f (v⟦A⟧) = (f ∘ v)⟦A⟧
```

And a theory extension to GHA homomorphism:

```lean
def Theory.Extension.toGeneralizedHeytingHom (e : T.Extension T') :
    GeneralizedHeytingHom (Quotient T.propositionSetoid) (Quotient T'.propositionSetoid)
```

This shows the Lindenbaum algebra construction is functorial -- theory extensions induce GHA homomorphisms between Lindenbaum algebras. This is algebraically powerful for relating different logics.

---

## 9. Implications for Task 227

### 9.1 For the Algebraic Completeness Implementation

Thomas's code provides a working blueprint. The key decision is:

1. **Adopt Thomas's code directly** (requires switching to his `Proposition` type -- not viable without massive refactor)
2. **Port the proof strategy to our `Proposition` type** (build Lindenbaum quotient on our 5-constructor type with `bot_val` parameter)
3. **Merge Thomas's branch** and maintain both `Proposition` types with a bridge

Option 2 is the pragmatic path. The Lindenbaum construction works the same way with primitive `⊥` -- the quotient `Quotient T.propositionSetoid` is isomorphic regardless of whether `⊥` is a constructor or an atom. The canonical valuation maps each atom to its class, and `.bot` maps to `⟦⊥⟧`. The proofs are structurally identical with one extra case (`.bot`) in each induction.

### 9.2 JohanssonAlgebra

Mathlib has no `JohanssonAlgebra` class. The closest is `GeneralizedHeytingAlgebra` (GHA), which has `⊤` and `⇨` but no `⊥`. Thomas's approach shows GHA is sufficient for MPL completeness, and upgrading to HA/BA handles IPL/CPL. There is no need for a separate `JohanssonAlgebra` -- the three-tier Mathlib hierarchy (GHA < HA < BA) exactly matches the three logic tiers (MPL < IPL < CPL).

### 9.3 The `v ⊨ T` Pattern for Our Codebase

Even with primitive `⊥`, we can define:

```lean
def AlgTValid (T : Theory Atom) {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (bot_val : H) : Prop :=
  ∀ A ∈ T, AlgEvaluate v bot_val A = ⊤
```

And state the parametric completeness as:

```lean
theorem Theory.alg_complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```

This gets almost all of Thomas's elegance while keeping our `Proposition` type. The specialization works:
- MPL: `AlgTValid ∅ v bot_val` is trivially true, so it drops out
- IPL: `AlgTValid IPL v ⊥` in HA simplifies to `⊥ ⇨ v⟦A⟧ = ⊤` for all `A`, which is `bot_le`
- CPL: Similar with BA

---

## 10. Summary of Findings

1. **Thomas's design is algebraically cleaner** for the completeness theorem: one parametric statement vs three separate predicates. The `v ⊨ T` pattern elegantly absorbs logic-specific constraints.

2. **Thomas's `Proposition` type (4 constructors, `⊥` as atom)** is not viable for adoption in CSLib main due to 257 downstream pattern match sites. The refactoring cost is prohibitive.

3. **The two approaches are formally equivalent** for any logic with `⊥`. The correspondence is `bot_val ↔ v ⊥`.

4. **Recommended path**: Keep our 5-constructor `Proposition`, but adopt Thomas's `v ⊨ T` style for the completeness statement. Port the Lindenbaum algebra construction (propPO, propLattice, propGeneralizedHeyting, propHeyting, propBoolean) to our type with an extra `.bot` case in each induction.

5. **No JohanssonAlgebra needed**: Mathlib's GHA/HA/BA hierarchy exactly matches MPL/IPL/CPL.

6. **Thomas's Lindenbaum construction** is the missing piece for algebraic completeness. The canonical valuation + `canonicalV_spec` + `lindenbaum_complete` + `tValid_canonicalV` chain provides a complete proof strategy that can be ported to our framework.

7. **The `BooleanAlgebra.ofRegular` trick** for CPL completeness is elegant and should be adopted.
