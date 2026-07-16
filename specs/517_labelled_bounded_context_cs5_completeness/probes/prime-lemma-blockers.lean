import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

/-! # Task 517 Phase 21 — Simpson's Prime Lemma 5.3.1 at `𝒯 = ∅`: THREE STATEMENT-LEVEL BLOCKERS

**Phase 21's deliverable is not constructible as specified, and the reason is not the
mathematics.** Every claim in this file is sorry-free, axioms ⊆ `[propext, Classical.choice,
Quot.sound]`.

Lemma 5.3.1's job is to **produce a `𝒯`-prime context**. This file shows:

1. **`TPrime 𝒯 Atom` is uninhabited for EVERY `𝒯` — including `𝒯 = ∅`** (`tPrime_false`).
   Phase 20 established this at `𝒯 = TS5` (`tPrime_TS5_false`) and diagnosed the cause as
   `χ_T`'s quantifier range, concluding the defect "lands on Phase 23, not Phase 21". **That
   diagnosis is incomplete.** There is a second, independent, *`𝒯`-agnostic* emptiness driver
   that fires at `𝒯 = ∅`, so the `𝒯 = ∅`-first sequencing does **not** dodge it.

2. **`NIK.efq` is label-local; Simpson's `(⊥E)` is cross-label** (Figure 4-1, p. 69, read from
   the page raster — the text layer for this figure is destroyed). Simpson's rule is
   `x:⊥ / y:A`; CSLib's is `x:⊥ / x:A`. Lemma 5.3.1's *"Consistency is immediate, because
   `Δ ⊬_H x:A`"* (p. 93) is exactly an appeal to the cross-label form.

3. **`NIK.orE` is label-local; Simpson's `(∨E)` is cross-label** (same figure). Simpson's rule
   has major premise `x:A∨B` and conclusion `y:C`; CSLib's fixes both at `x`. Lemma 5.3.1's
   disjunction-property step (*"for otherwise we would have that `Δ ⊢_H x:A` by an application
   of `(∨E)`"*, p. 93) is exactly an appeal to the cross-label form: the disjunction sits at `y`
   and the excluded formula at `x`.

All three share **one root cause**: the CSLib transcription drops the *domain-relativity /
cross-label* structure that Simpson's Chapter 5 relies on. Phase 20 found the first instance of
this class (`clModel` quantifying type-wide instead of over `H`'s domain) and proposed
`ClassicalModelOn`. Blockers 1-3 are three further instances of the same class.

`Cslib/` is **out of Phase 21's territory**, so no repair is applied here; each repair is
*stated* and its adequacy checked.

## Provenance

[Simpson1994], `references.bib:86`. Page images read directly:
- p. 69 (PDF p. 78) — Figure 4-1, `N_□◇`'s rules. **Raster only**: `pdftotext -layout` renders
  this figure as noise (`%(M) %(/\El) %(Am)`), so the rule shapes are unrecoverable from the
  text layer. This is the same text-layer failure mode Phase 20 documented for `H_i` on p. 92.
- pp. 92-93 (PDF pp. 101-102) — Lemma 5.3.1 and its proof.
- pp. 94-95 (PDF pp. 103-104) — Lemma 5.3.2, the canonical model.
-/

namespace Cslib.Logic.Modal.Labelled

universe u
variable {Atom : Type u} {𝒯 : Set GeomAxiom}

/-! ## Blocker 1: `TPrime 𝒯 Atom` is empty for every `𝒯`

`impI` + `assumption` derive `x : A ⊃ A` at an **arbitrary** label, over an arbitrary graph,
from an arbitrary context — no premises, no side conditions, and (as Phase 20 established)
`NIK` never consults `G.X` at all. Chain that with `TPrime`'s **type-wide** `deductiveClosure`
and `Context.ctxSubset`:

```
deductiveClosure ⟹ (x : A ⊃ A) ∈ Γ   for every label x
ctxSubset        ⟹ x ∈ G.X            for every label x, i.e. G.X = univ
coinfinite       ⟹ ⊥                  (some Label.var n has n ∉ V')
```

This is structurally the same chain as Phase 20's `tPrime_TS5_false`, but the driver is a
**premise-free derivation** rather than `clModel .T`, so it is completely independent of `𝒯`.
Phase 20's `IsEmpty (TPrime TS5 Atom)` is a special case of `tPrime_false` below.
-/

/-- `x : A ⊃ A` is derivable at **every** label, over **every** graph, from **every** context.
No premises, no side conditions, no relational obligation, and no reference to `G.X`. -/
theorem NIK.imp_self (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x : Label Atom)
    (A : Proposition Atom) : NIK 𝒯 G Γ (x ∶ .imp A A) :=
  .impI G Γ x A A (.assumption _ _ _ (by simp))

/-- The `Deriv` (set-lifted) form of `NIK.imp_self`, witnessed by the **empty** finite sublist,
so it holds against every `Γ` whatsoever. -/
theorem Deriv.imp_self {G : Graph Atom} {Γ : Set (LabelledFormula Atom)} (x : Label Atom)
    (A : Proposition Atom) : Deriv 𝒯 G Γ (x ∶ .imp A A) :=
  ⟨[], by simp, NIK.imp_self G [] x A⟩

/-- **`TPrime 𝒯 Atom` is uninhabited for EVERY `𝒯`, including `𝒯 = ∅`.**

Lemma 5.3.1's entire purpose is to construct an inhabitant of this type. **Phase 21 as specified
therefore cannot succeed at any `𝒯`** — not because the mathematics fails, but because
`deductiveClosure` is transcribed with a type-wide quantifier where Simpson's clause 1 ranges
only over labels of `H`.

This **supersedes** Phase 20's scope finding. Phase 20 concluded the `TPrime`-emptiness defect
"lands on Phase 23, not Phase 21" because at `𝒯 = ∅` clause 0 is vacuous. Clause 0 is indeed
vacuous at `∅`; but clause 1 is not, and it empties the type on its own. -/
theorem tPrime_false (P : TPrime 𝒯 Atom) : False := by
  obtain ⟨V', hV', hX⟩ := P.coinfinite
  obtain ⟨n, hn⟩ := hV'.nonempty
  have hmem := P.deductiveClosure (Label.var n) (.imp .bot .bot) (Deriv.imp_self _ _)
  exact hn (hX _ (P.ctxSubset _ hmem))

/-- Restated as `IsEmpty`, at **every** `𝒯`, so downstream code cannot quantify over it
vacuously and mistake that for progress. Subsumes Phase 20's `IsEmpty (TPrime TS5 Atom)`. -/
instance instIsEmptyTPrime : IsEmpty (TPrime 𝒯 Atom) := ⟨tPrime_false⟩

/-! ### The repair for blocker 1

Simpson's clause 1 (p. 92, verbatim) is *"If `Γ ⊢^𝒯_G x:A` then `x:A ∈ Γ`"*, where `⊢_G` is the
consequence relation of §5.1 — a judgement about labels **of `G`**. Lemma 5.3.2 makes the same
domain-relativity explicit in its own statement: *"for all `y` **in `H`**, `(H,Δ),y ⊩ B` iff
`y:B ∈ Δ`"* (p. 94). Relativizing clause 1 to `G.X` is therefore a **transcription fix**, not a
weakening chosen for convenience:

```lean
deductiveClosure : ∀ x ∈ G.X, ∀ A, Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ
```

The relativized clause is exactly what Lemma 5.3.1's own deductive-closure step needs. Simpson
argues: *"suppose `Δ ⊢_H y:B`. Then `Δ, y:B ⊬_H x:A` ... Therefore `(H, Δ ∪ {y:B})` is in `C`"*.
For `(H, Δ ∪ {y:B})` to **be a context** at all, `Context.ctxSubset` demands `y ∈ H.X` — which
the relativized clause supplies as a hypothesis and the type-wide clause does not. So the
type-wide reading is not merely too strong; it is unusable at precisely the step that consumes
it. -/
theorem deductiveClosure_relativized_kills_the_chain
    {G : Graph Atom} {Γ : Set (LabelledFormula Atom)}
    (hdc : ∀ x ∈ G.X, ∀ A : Proposition Atom, Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ)
    (x : Label Atom) (A : Proposition Atom) :
    x ∈ G.X → (x ∶ .imp A A) ∈ Γ :=
  fun hx => hdc x hx _ (Deriv.imp_self x A)

/-- And the relativized clause is **consistent with `coinfinite`**: it only ever concludes
membership for labels already in `G.X`, so it cannot force `G.X = univ`. Witness: the trivial
graph's node set is a strict subset of `univ`, which is all the emptiness chain needed to fail. -/
example : ∃ x : Label Atom, x ∉ (Graph.trivial Atom).X := by
  refine ⟨Label.var 1, ?_⟩
  simp [Graph.trivial]

/-! ## Blocker 2: `(⊥E)` is transcribed label-local

**Simpson, Figure 4-1, p. 69 (PDF p. 78), read from the page raster:**

```
x:⊥
──── (⊥E)
y:A
```

The premise is labelled `x` and the conclusion `y`. **CSLib's `NIK.efq` fixes both at `x`**
(`Deduction.lean:206-208`, docstring: *"Ex falso quodlibet, label-local"*). The label-local rule
is sound but **strictly weaker**, and Lemma 5.3.1 consumes the cross-label form.
-/

/-- Simpson's cross-label `(⊥E)`, stated as a property of `𝒯` at the `Deriv` level. **This is
not a CSLib rule**; it is the rule Figure 4-1 prints. -/
def EfqCrossLabel (𝒯 : Set GeomAxiom) (Atom : Type u) : Prop :=
  ∀ (G : Graph Atom) (Γ : Set (LabelledFormula Atom)) (x y : Label Atom) (A : Proposition Atom),
    Deriv 𝒯 G Γ (x ∶ .bot) → Deriv 𝒯 G Γ (y ∶ A)

/-- **Simpson's one-line consistency argument, mechanized — and it needs the cross-label rule.**

p. 93, verbatim: *"Consistency is immediate, because `Δ ⊬^𝒯_H x:A`."* The excluded formula sits
at label `x`; the consistency clause must hold at **every** `y ∈ H.X`. Bridging `y:⊥` to `x:A`
across the label boundary is precisely what `(⊥E)` does in Figure 4-1 — and nothing else in the
system does it. Note this step needs **no maximality**: it is a property of any context avoiding
`x:A`, exactly as Simpson says. -/
theorem consistency_of_efqCrossLabel (h : EfqCrossLabel 𝒯 Atom) {H : Graph Atom}
    {Δ : Set (LabelledFormula Atom)} {x : Label Atom} {A : Proposition Atom}
    (hxA : ¬ Deriv 𝒯 H Δ (x ∶ A)) (y : Label Atom) : ¬ Deriv 𝒯 H Δ (y ∶ .bot) :=
  fun hy => hxA (h H Δ y x A hy)

/-- **What CSLib's label-local `efq` actually delivers: consistency at the excluded label ONLY.**

This is the sharp form of the gap. `TPrime.consistency` demands `∀ y ∈ H.X, Δ ⊬_H y:⊥`; the
label-local rule yields it **only at `y = x`**, because `efq` cannot move `⊥`'s label. For every
other `y ∈ H.X` the clause is left undischarged, and Simpson's proof offers no second argument —
it does not need one, because his `(⊥E)` is cross-label. -/
theorem consistency_at_excluded_label_only {H : Graph Atom} {Δ : Set (LabelledFormula Atom)}
    {x : Label Atom} {A : Proposition Atom} (hxA : ¬ Deriv 𝒯 H Δ (x ∶ A)) :
    ¬ Deriv 𝒯 H Δ (x ∶ .bot) := by
  rintro ⟨Γ₀, hΓ₀, hNIK⟩
  exact hxA ⟨Γ₀, hΓ₀, .efq _ _ x A hNIK⟩

/-! ## Blocker 3: `(∨E)` is transcribed label-local

**Simpson, Figure 4-1, p. 69 (PDF p. 78), read from the page raster:**

```
             [x:A]     [x:B]
               ⋮         ⋮
  x:A ∨ B     y:C       y:C
 ───────────────────────────── (∨E)
             y:C
```

The major premise is labelled `x`; the minor premises and the conclusion are labelled `y`.
**CSLib's `NIK.orE` fixes all of them at `x`** (`Deduction.lean:225-229`, docstring:
*"label-local case split"*).

Lemma 5.3.1's disjunction step (p. 93): *"suppose that `y:B ∨ C ∈ Δ`. Now either
`Δ,y:B ⊬^𝒯_H x:A` or `Δ,y:C ⊬^𝒯_H x:A`, for otherwise we would have that `Δ ⊢^𝒯_H x:A` by an
application of `(∨E)`."* The disjunction is at `y`; the derived formula is at `x`. Under the
label-local rule this application is **ill-formed**, so the disjunction property is dischargeable
only for disjunctions sitting at the excluded label `x`.
-/

/-- Simpson's cross-label `(∨E)`, stated at the `NIK` level. **Not a CSLib rule**; the rule
Figure 4-1 prints. Note `C`'s label `y` is independent of the disjunction's label `x`. -/
def OrECrossLabel (𝒯 : Set GeomAxiom) (Atom : Type u) : Prop :=
  ∀ (G : Graph Atom) (Γ : List (LabelledFormula Atom)) (x y : Label Atom)
    (A B C : Proposition Atom), NIK 𝒯 G Γ (x ∶ .or A B) → NIK 𝒯 G ((x ∶ A) :: Γ) (y ∶ C) →
    NIK 𝒯 G ((x ∶ B) :: Γ) (y ∶ C) → NIK 𝒯 G Γ (y ∶ C)

/-- CSLib's `orE` is the `x = y` diagonal of `OrECrossLabel`: the cross-label rule implies the
label-local one, confirming the transcription is a **restriction**, not a variant. -/
theorem orE_labelLocal_of_orECrossLabel (h : OrECrossLabel 𝒯 Atom) (G : Graph Atom)
    (Γ : List (LabelledFormula Atom)) (x : Label Atom) (A B C : Proposition Atom)
    (hor : NIK 𝒯 G Γ (x ∶ .or A B)) (hA : NIK 𝒯 G ((x ∶ A) :: Γ) (x ∶ C))
    (hB : NIK 𝒯 G ((x ∶ B) :: Γ) (x ∶ C)) : NIK 𝒯 G Γ (x ∶ C) :=
  h G Γ x x A B C hor hA hB

/-- Symmetrically, the cross-label `(⊥E)` implies the label-local `efq`. Both blockers 2 and 3
are therefore **strict weakenings** of Figure 4-1, not alternative encodings of it. -/
theorem efq_of_efqCrossLabel (h : EfqCrossLabel 𝒯 Atom) (G : Graph Atom)
    (Γ : Set (LabelledFormula Atom)) (x : Label Atom) (A : Proposition Atom)
    (hbot : Deriv 𝒯 G Γ (x ∶ .bot)) : Deriv 𝒯 G Γ (x ∶ A) :=
  h G Γ x x A hbot

end Cslib.Logic.Modal.Labelled

section Verification
open Cslib.Logic.Modal.Labelled
#print axioms Cslib.Logic.Modal.Labelled.NIK.imp_self
#print axioms Cslib.Logic.Modal.Labelled.Deriv.imp_self
#print axioms Cslib.Logic.Modal.Labelled.tPrime_false
#print axioms Cslib.Logic.Modal.Labelled.instIsEmptyTPrime
#print axioms Cslib.Logic.Modal.Labelled.deductiveClosure_relativized_kills_the_chain
#print axioms Cslib.Logic.Modal.Labelled.consistency_of_efqCrossLabel
#print axioms Cslib.Logic.Modal.Labelled.consistency_at_excluded_label_only
#print axioms Cslib.Logic.Modal.Labelled.orE_labelLocal_of_orECrossLabel
#print axioms Cslib.Logic.Modal.Labelled.efq_of_efqCrossLabel
end Verification
