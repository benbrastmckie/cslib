# Task 419 — DEEP RE-INVESTIGATION: The Virtuous Unification of Derivation Lifting

**Task type**: cslib (SPIKE round 2 — adversarial re-verification, read-only, no Lean edits)
**Status**: research / deep spike — supersedes the verdict (not the source facts) of `01_derivation-lifting-spike.md`
**Date**: 2026-06-29
**Mandate**: Adversarially challenge round 1's `BLOCKED` verdict. Find the principled unification, or prove rigorously none exists at reasonable cost. User has explicitly rejected the "keep three lifts" compromise.

---

## 1. VERDICT (no hedging)

**(A) FEASIBLE AND VIRTUOUS. The principled unification exists. Round 1's `BLOCKED` verdict is REFUTED.**

There **is** one mathematical object that subsumes all four lifts: a **morphism of proof systems**
`ProofSigHom σ₁ σ₂`, whose **functorial action `Deriv.map` on the free derivation algebra `Deriv σ`
is the lift**. Modal `liftDerivation`, PL `liftDerivationTree`, Bimodal `DerivationTree.lift`, and
Bimodal `liftDerivationWith` are four *instances* of `Deriv.map` applied to four different signature
morphisms. I verified the coherence conditions the abstraction requires already hold **in the
existing source** (definitionally for `imp`, propositionally for `swapTemporal`).

Round 1's three "obstacles" are **dissolvable artifacts of its own framing**, not real obstructions:

| Round-1 obstacle | Why it dissolves |
|---|---|
| (1) "axiom-predicate vs frame-class vs fresh-atom are different operations / axis mismatch" | All three are one **Type-valued axiom-family morphism** `∀ φ, Ax₁ φ → Ax₂ (g φ)` over a formula map `g`. Subsumption (`g=id`, predicate lift), frame monotonicity (`g=id`, `le_trans`), and unembedding (`g=liftFormula a`, `liftAxiom`) are instances. |
| (2) "Bimodal has no axiom **predicate**" | True but irrelevant. The abstraction needs an axiom **family** `Ax : F → Type`, not a `Prop` predicate. Bimodal's concrete `Axiom : Formula → Type u` (gated by `{h // h.minFrameClass ≤ fc}`) *already is* exactly that family. Fixating on "predicate" (Prop) was the round-1 error. |
| (3) "three formula types ⇒ no single recursion without unifying syntaxes (XL)" | The generic `Deriv.map` is **parametric in `F₁, F₂, g`**. Each logic instantiates at its own `F`. No syntax unification is required. Round 1 conflated "instantiate one parametric def three times" (cheap) with "one def over a sum-of-three syntax" (the XL straw man it then knocked down). |

The honest tension is **not mathematical but ergonomic**, and it governs *which realization* to pick
(§6): the maximally-unified realization (replace all three inductives) is XL and ergonomically
regressive across 190+ downstream files with no proof-side payoff; the **recommended** realization is
a **non-invasive Foundations overlay** that expresses the deep truth as a theorem while leaving
per-logic proofs untouched. This is what makes the result *virtuous-and-bounded* rather than
*virtuous-but-ruinous*.

---

## 2. Source-to-Implementation Mapping (reference grounding, Tier 3 + CT precedent)

| Source claim (verified) | File:line | Becomes an instance of | Translation note |
|---|---|---|---|
| Modal `liftDerivation` (5 ctors; `.ax` via `h_sub`) | `Modal/Metalogic/InterSystem/Lifting.lean:47` | `Deriv.map ⟨id, _, axMap=h_sub, closures={box}⟩` | `g=id`; one closure (necessitation/box) |
| PL `liftDerivationTree` (4 ctors; no closures) | `Propositional/Semantics/Algebra/ConjImpConservative.lean:59` | `Deriv.map ⟨id, _, axMap=h_sub, closures=∅⟩` | `g=id`; empty closure list |
| Bimodal `DerivationTree.lift` (frame monotone) | `Bimodal/ProofSystem/Derivation.lean:92` | `Deriv.map ⟨id, _, axMap=fun φ ⟨h,hfc⟩=>⟨h, le_trans hfc h_le⟩, closures={box,G,swap}⟩` | `g=id`; axiom-family morphism is `le_trans` on the `minFrameClass` gate |
| Bimodal `liftDerivationWith` (unembed) | `Bimodal/Metalogic/ConservativeExtension/Lifting.lean:636` | `Deriv.map ⟨liftFormula a, liftFormula_imp, axMap=liftAxiom a (+ minFrameClass preservation), closures coherent via liftFormula_swapTemporal⟩` | **cross-syntax** `g=liftFormula a : ExtFormula→Formula`; the only instance exercising full generality; freshness is orthogonal (§5) |

**Coherence conditions are already satisfied in source** (this is the decisive evidence the
abstraction is *the right one*, not a post-hoc fit):

- `liftFormula_imp` (`Lifting.lean:571`): `liftFormula a (x.imp y) = (liftFormula a x).imp (liftFormula a y)`.
  The mp arm of `liftDerivationWith` (`:652`) reconstructs `modus_ponens` with **no `▸` rewrite** — so this
  homomorphism holds *definitionally* (the elaborator accepts the recursive call's type directly). This is
  exactly the `g_imp` field the morphism needs for the `mp` rule.
- `liftFormula_swapTemporal` (`Lifting.lean:576`): the duality arm (`:666`) uses `liftFormula_swapTemporal a φ ▸ …`.
  This is exactly the **closure-coherence** condition `g (m φ) = m' (g φ)` for the `temporal_duality` closure
  operator `m = swapTemporal`, threaded as a propositional rewrite.

These two lemmas already in the Bimodal source *are* the naturality squares of a signature morphism.
The abstraction is not speculative; it is latent in the existing code.

**BibKey grounding** (`references.bib`, 74 entries): the proof-theoretic content (Burgess-Xu axioms)
is grounded in `[Burgess1982I]`, `[Burgess1982II]`, `[Xu1988]`; the algebraic PL lifts in `[Rasiowa1974]`.
The *abstraction* itself (functorial action of a signature morphism on free derivations) is category-theory
folklore (Lawvere functorial semantics / Lambek–Scott free-category proof theory); **no such BibKey exists
in `references.bib`** and none needs adding, because this task transcribes Mathlib/CT *patterns*, not a
specific paper. Reference grounding Tier 3 (implementation/Mathlib-backed), CT precedent supporting.

---

## 3. The exact target abstraction (Lean 4 signature)

Home: `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (new). Sketch (illustrative, not
yet typechecked — this is a research artifact, no Lean was edited):

```lean
variable {F : Type*} [HasImp F]

/-- A Hilbert-style proof-system signature over a formula algebra `F`:
    a Type-valued axiom family plus a list of unary empty-context closure operators. -/
structure ProofSig (F : Type*) [HasImp F] where
  Ax       : F → Type            -- axiom family (Type-valued ⇒ computational; Bimodal's `Axiom` fits as-is)
  closures : List (F → F)        -- box, G, swapTemporal, … (necessitation-style rules)

/-- The FREE derivation algebra over a signature: the initial object of the rule system.
    `assumption`, `modus_ponens`, `weakening` are the fixed structural rules. -/
inductive Deriv (σ : ProofSig F) : List F → F → Type _
  | ax    (Γ φ) (h : σ.Ax φ)                                   : Deriv σ Γ φ
  | assum (Γ φ) (h : φ ∈ Γ)                                    : Deriv σ Γ φ
  | mp    (Γ φ ψ) (d₁ : Deriv σ Γ (HasImp.imp φ ψ)) (d₂ : Deriv σ Γ φ) : Deriv σ Γ ψ
  | close (m) (hm : m ∈ σ.closures) (φ) (d : Deriv σ [] φ)     : Deriv σ [] (m φ)
  | weak  (Γ Δ φ) (d : Deriv σ Γ φ) (h : Γ ⊆ Δ)               : Deriv σ Δ φ

/-- A MORPHISM of proof systems: a formula map that respects implication, an axiom-family map
    living over it, and closure-operator coherence (the naturality squares). -/
structure ProofSigHom {F₁ F₂ : Type*} [HasImp F₁] [HasImp F₂]
    (σ₁ : ProofSig F₁) (σ₂ : ProofSig F₂) where
  g      : F₁ → F₂
  g_imp  : ∀ φ ψ, g (HasImp.imp φ ψ) = HasImp.imp (g φ) (g ψ)
  axMap  : ∀ φ, σ₁.Ax φ → σ₂.Ax (g φ)
  clMap  : ∀ m ∈ σ₁.closures, ∃ m', m' ∈ σ₂.closures ∧ ∀ φ, g (m φ) = m' (g φ)

/-- THE LIFT, once and for all: the functorial action of a proof-system morphism on free
    derivations. Modal/PL/Bimodal lifts are `Deriv.map H` for four choices of `H`. -/
def Deriv.map {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂} (H : ProofSigHom σ₁ σ₂) :
    {Γ : List F₁} → {φ : F₁} → Deriv σ₁ Γ φ → Deriv σ₂ (Γ.map H.g) (H.g φ)
  | _, _, .ax Γ φ h            => .ax _ _ (H.axMap φ h)
  | _, _, .assum Γ φ h         => .assum _ _ (List.mem_map_of_mem h)
  | _, _, .mp Γ φ ψ d₁ d₂      => H.g_imp φ ψ ▸ .mp _ _ _ (H.g_imp φ ψ ▸ Deriv.map H d₁) (Deriv.map H d₂)
  | _, _, .close m hm φ d      => let ⟨m', hm', hco⟩ := H.clMap m hm; hco φ ▸ .close m' hm' _ (Deriv.map H d)
  | _, _, .weak Γ Δ φ d h      => .weak _ _ _ (Deriv.map H d) (by intro x hx; ...)
```

This is **literally** the structure of `Cat.freeMap` (apply a prefunctor to each arrow of a free path),
generalised from unary paths to branching derivations. The generic functor laws
(`Deriv.map (id) = id`, `Deriv.map (H₂ ∘ H₁) = Deriv.map H₂ ∘ Deriv.map H₁`, height preservation) are
provable once and serve every logic.

---

## 4. Mathlib / proof-theory precedent (the user's named anchors, checked)

I searched `leansearch`, `loogle`, `leanfinder` for every precedent named in the mandate. Findings:

1. **`FirstOrder.Language.LHom`** (`Mathlib.ModelTheory.LanguageMap`) — a map of first-order languages
   `(onFunction, onRelation)` that transports terms/formulas/theories. Has `LHom.id`, `LHom.comp`-style
   structure, `sumInl`/`sumInr`, `lhomWithConstants` (**adding constants — the direct analogue of Bimodal's
   atom extension `Sum.inr ()`**), `IsExpansionOn`, `LEquiv`. **This validates the user's "logic
   homomorphism that transports syntax" intuition as a recognised, formalised concept.** *Caveat:* Mathlib's
   model theory is **semantic** (satisfaction/models); it has **no syntactic derivation calculus**, hence no
   "lift a derivation along an `LHom`" theorem. So `LHom` is precedent for the *signature-morphism half*, not
   the *derivation-transport half*. Mathlib provides the pattern, not the payload.

2. **`CategoryTheory.Cat.free` / `Cat.freeMap`** (`Mathlib.CategoryTheory.Category.Quiv`) — the free
   category on a quiver is its path category `Paths V`; a prefunctor `F : V ⥤q W` induces
   `freeMap F : Paths V ⥤ Paths W` "by applying F to vertices and paths," with naturality
   `pathsOf_freeMap_toPrefunctor`. **This is exactly "lift = functorial action of a signature morphism on
   free derivations" — for the UNARY case.** Derivations are **branching** (`mp` has two premises), so they
   are the free **multicategory / term algebra over a branching signature**, not a free category. `freeMap`
   is the right idea, wrong arity.

3. **No free multicategory / operad / indexed-container library in Mathlib.** Searches returned
   `FreeMonoidalCategory`, `FreeBicategory`, `FreeMagma` (free magma = binary trees over generators, single
   untyped op — closest, still wrong shape), and the initial-algebra machinery `QPF.Fix` / `MvQPF.Fix` /
   `PFunctor.W`. The `MvQPF`/`W` machinery is **un-indexed** (TypeVec-shaped) and cannot ergonomically carry
   a derivation's `(Γ, φ)` index with premise-dependent context constraints (`close` forces `Γ = []`, `weak`
   relates `Γ ⊆ Δ`). **Conclusion: the generic `Deriv`/`Deriv.map` must be hand-built; there is no Mathlib
   abstraction to instantiate.** But this is ~one Foundations file, not a research programme — the
   hand-built `Deriv` is a *standard* "inductive family generated by a rule set," and `Deriv.map` is a
   standard structural recursion (the four existing lift bodies are proof that Lean accepts exactly this
   recursion).

**Net precedent finding:** the *concept* is principled and has first-class Mathlib analogues
(`LHom`, `Cat.freeMap`); the *exact machinery* (branching, dependently-indexed free derivations +
functorial action) is genuinely absent and must be built. This is a "missing abstraction we should
add," not an "impossible abstraction." Reuse-first is satisfied: I confirmed nothing in Mathlib or
`Cslib.Foundations` already provides it.

---

## 5. The two genuinely subtle points (adversarial deep-dives)

### 5.1 Is the Bimodal axiom-predicate gap intrinsic? (round-1 obstacle 2) — NO.

Round 1 said Bimodal "has no axiom predicate to subsume." Correct literally, wrong in import. The lift
needs a **Type-valued axiom family**, and Bimodal already has the *strongest possible* form of one: the
concrete inductive `Axiom : Formula Atom → Type u` (`Axioms.lean:79`, 42 ctors) with the gate
`{h : Axiom φ // h.minFrameClass ≤ fc}`. The frame lift `DerivationTree.lift` (`:92`) is *precisely*
`Deriv.map` of the axiom-family morphism `fun φ ⟨h, hfc⟩ => ⟨h, le_trans hfc h_le⟩` with `g = id`.

Crucially, **do NOT predicate-ify Bimodal** (do not replace `Axiom` by `Formula → Prop`). That would be
actively *anti*-virtuous: `liftDerivationWith` depends on the *computational* `Axiom` data —
`liftAxiom a : ExtAxiom φ → Axiom (liftFormula a φ)` (`:581`) cases on all 42 constructors and
`liftAxiom_preserves_minFrameClass` (`:628`) needs the constructor correspondence. A `Prop` existential
would erase exactly the data these need (you cannot eliminate a `Prop` `∃` into the `Type`-valued
`Axiom (liftFormula a φ)`). So the Type-valued family is not merely *adequate* — it is *forced* by the
conservativity machinery, and the abstraction must (and does) use `Ax : F → Type`, not `F → Prop`.
This is a precise correction to the spike: the "axis mismatch" is an illusion created by demanding a
`Prop` predicate where the correct primitive is a `Type` family.

### 5.2 Does the freshness side-condition break functoriality? — NO; it is orthogonal.

`liftDerivationWith` carries `h_fresh : a ∉ collectDerivInl d` and splits it per node. One might fear this
is essential non-functoriality (a *conditional* map, not a total functor). It is not:

- In `liftDerivationWith`, `h_fresh` is **threaded but never consumed to build a node** — the `axiom`/
  `assumption` arms take `_` and ignore it; the recursive arms only derive sub-freshness to feed recursion.
  By induction the constructed `DerivationTree` does not depend on `h_fresh` for its *existence/typing*. It
  is the functorial action `Deriv.map (liftFormula-hom a)` on the nose.
- Freshness is a **correctness** condition used downstream in `liftDerivationQfree` (`:691`), guaranteeing
  the chosen `a` makes `liftFormula a` a faithful left-inverse of `embedFormula` on this derivation's atoms.
  In the abstraction it sits *outside* the functor, as a property of the specific morphism instance, not as
  a defect of `Deriv.map`.

So `liftDerivationWith` decomposes as **(total functorial action) + (orthogonal freshness lemma)**. The
generic `Deriv.map` hosts the first; the second stays Bimodal-local. No non-functoriality obstruction
exists. *(This is the closest thing to a route toward verdict (B), and it fails: the obstruction is not
essential.)*

---

## 6. Cost/benefit and the recommended realization

Because no mathematical obstruction survives, the decision is purely engineering ROI. Three realizations:

### A2 — Maximal unification (replace every `DerivationTree` by `Deriv σ`). NOT recommended.
- **Buys:** a single inductive, single recursor, single height function, shared soundness skeleton.
- **Costs (quantified):** `DerivationTree` is referenced in **193 Lean files** (Modal 55, Bimodal 69, PL 38,
  Temporal 28); **79 Bimodal constructor-match sites** and **23 Modal** would migrate from named
  constructors (`.necessitation`, `.temporal_duality`) to generic `.close m hm` with **list-membership
  rule dispatch**, losing exhaustiveness checking. Soundness/completeness/canonical-model inductions degrade
  permanently. **High blast radius, ergonomic regression with no proof-side payoff.** This is "more unified
  in one narrow sense, less virtuous overall."

### A1 — Non-invasive Foundations overlay. **RECOMMENDED.**
- Add `ProofSig`/`Deriv`/`ProofSigHom`/`Deriv.map` + functor laws to `Cslib/Foundations/Logic/Metalogic/`.
- For each logic, a **constructor-preserving definitional equivalence** `e : DerivationTree _ ≃ Deriv σ`
  (a structural iso; `@[match_pattern]` shims recover named ctors). Re-derive each existing lift as
  `e.symm ∘ Deriv.map H ∘ e`, **without touching any downstream proof**.
- **Buys:** the genuine cross-logic theorem ("lift = functorial action of a proof-system morphism"),
  including Bimodal's *both* lifts; generic functor laws proved once; a substrate future logics reuse.
- **Honest cost:** the equivalences are real work (each is a forward + backward recursion + two round-trip
  proofs ≈ 3–4× one lift body), so this **does not net-reduce LOC** — its payoff is conceptual unification +
  reusable generic metatheory, not line count. This is the correct *virtuous-and-bounded* trade.

### A3 — Incremental single-logic migration (validation step). Optional bridge.
- Migrate only **PL** (smallest, no closures) to `abbrev DerivationTree Ax := Deriv (plSig Ax)` definitionally,
  proving the abstraction earns its keep before committing Modal/Bimodal. PL's 38 files bound the risk.

**Recommendation:** Pursue **A1** (overlay) as the deliverable; gate full adoption behind an **A3** PL pilot.
Do **not** pursue A2. Reject the spike's "keep three lifts forever / BLOCKED" — but also reject naive "rip out
all three inductives." The virtuous middle is: *one Foundations definition of the morphism + functor, the
three (four) lifts exhibited as its instances, downstream proofs preserved.*

---

## 7. Phased implementation direction (if approved)

- **P1 (Foundations, ~120–160 lines):** `ProofSig`, `Deriv`, `ProofSigHom`, `Deriv.map`; functor laws
  (`map_id`, `map_comp`, `height` preservation). Self-contained; builds in isolation. *Acceptance: `Deriv.map`
  typechecks sorry-free; `map_id`/`map_comp` proved.*
- **P2 (PL instance + A3 pilot, ~60–100 lines):** `plSig`, `plHom`, equivalence `PL.DerivationTree ≃ Deriv plSig`;
  re-derive `liftDerivationTree` and `derivable_mono` as corollaries of `Deriv.map`. *Acceptance: `derivable_mono`
  re-proved via `Deriv.map`; `ConjImpConservative.lean` still builds.*
- **P3 (Modal instance):** `modalSig` (1 closure: box), `modalHom`; re-derive `liftDerivation`/`Derivable_mono`.
- **P4 (Bimodal — the real test):** `Ax := fun φ => {h : Axiom φ // h.minFrameClass ≤ fc}`, `closures = [box, allFuture, swapTemporal]`;
  (a) re-derive `DerivationTree.lift` as `Deriv.map` of the `le_trans` frame-inclusion morphism; (b) re-derive
  `liftDerivationWith` as `Deriv.map` of the `liftFormula a` cross-syntax morphism (reusing existing `liftFormula_imp`,
  `liftFormula_swapTemporal`, `liftAxiom`, `liftAxiom_preserves_minFrameClass`), with freshness retained as the
  orthogonal `liftDerivationQfree` lemma. *Acceptance: both Bimodal lifts factor through `Deriv.map`; full
  `lake build` green; no `sorry`, no `axiom`, no vacuous defs.*
- **P5 (docs + deprecation shims):** document the abstraction; optional `@[deprecated]` aliases.

**Zero-debt note:** every phase is independently buildable and sorry-free or it is `[BLOCKED]` and reported.
P4(b) is the highest-risk phase (cross-syntax morphism + freshness orthogonality); if the equivalence proves
costlier than re-deriving `liftDerivationWith` directly, P4(b) may be descoped to "frame lift only" and the
unembedding left as a *documented instance-by-hand* of the same `ProofSigHom` shape — still delivering the
unification claim without forcing the equivalence.

---

## 8. Adversarial Self-Verification

I challenged each load-bearing claim of *my own* (A) verdict before committing it:

1. **"All four lifts are `Deriv.map` instances."** Verified against source, not asserted: the coherence
   fields (`g_imp`, `clMap`) correspond to `liftFormula_imp` (definitional in the mp arm) and
   `liftFormula_swapTemporal` (the `▸` in the duality arm). Modal/PL use `g=id` trivially; Bimodal frame uses
   `le_trans`; Bimodal unembed uses `liftAxiom`. **Confidence: high.** The mp arm typechecking with no `▸`
   confirms the imp-homomorphism is definitional — the strongest possible evidence.
2. **"Round-1 obstacle (3) is wrong."** Re-checked: `Deriv.map` is parametric in `F₁,F₂,g`; instantiating three
   times needs no sum syntax. The spike's XL straw man (one inductive over a unified syntax) is a *different,
   unnecessary* construction. **Confidence: high.**
3. **Searched for an essential non-functoriality (the only route to verdict B).** The candidate was Bimodal's
   freshness side-condition. Dismantled in §5.2: freshness is threaded-but-unused in the construction
   (vestigial to the *function*, load-bearing only for the downstream *correctness* lemma), so the map is a
   total functor. **No essential obstruction found.** I therefore cannot honestly issue verdict (B). Confidence:
   high that the *function* is total-functorial; medium on the claim that freshness is fully removable from
   `liftDerivationWith` (that is a separate refactor I did not attempt) — but removability is not needed for the
   verdict, only orthogonality, which holds.
4. **"A1 overlay is not just round-1's rejected Option-A typeclass."** Challenged hard. Distinction confirmed:
   Option A re-implemented each lift body inside an instance (zero reuse, PL+Modal only, excludes Bimodal). A1
   provides a *single generic `Deriv.map` implementation* that all logics *reuse*, and *includes Bimodal's both
   lifts*. Different in kind. **But** I also concede honestly (§6) that A1 does **not** net-reduce LOC because of
   the equivalence plumbing — its payoff is conceptual unification + reusable generic metatheory, and a reader
   could rationally judge that payoff insufficient. I did not hide this. **Confidence: the abstraction is real;
   medium-high that A1 is worth its cost — this is a genuine judgment call, flagged for the user.**
5. **Reuse-check completeness (5 steps).** `lean_local_search`/grep over `Cslib.Foundations` (InferenceSystem,
   GenericMCS, ListDeduction, Consistency, ProofSystem) — no existing generic derivation functor. Mathlib via
   `leansearch`/`loogle`/`leanfinder` — `LHom`, `Cat.freeMap` (precedent, not payload); no free
   multicategory/indexed-container. Both locations of `Cslib.Logic` searched. **Reuse-first satisfied: the
   correct reuse is to ADD the missing Foundations abstraction, not to keep three lifts and not to instantiate a
   nonexistent Mathlib one.**
6. **Zero-debt compliance.** No recommendation involves `sorry`, `axiom`, or vacuous defs; every phase has an
   explicit green-or-BLOCKED acceptance gate; the riskiest sub-phase (P4b) has a documented descope path that is
   still sorry-free. **Compliant.**
7. **Line numbers re-verified post-417/418.** `Lifting.lean:47` (Modal), `ConjImpConservative.lean:59` (PL),
   `Derivation.lean:53/92` (Bimodal inductive/lift), `Axioms.lean:79`, `ConservativeExtension/Lifting.lean:562/571/576/581/628/636`,
   `InferenceSystem.lean:42`, `GenericMCS.lean:103-109/110` — all read directly this session, all current. No drift.

**Result of self-verification:** verdict **unchanged at (A)**. One claim down-graded to a flagged judgment call
(A1's cost-worth, item 4); one claim explicitly bounded (freshness orthogonality vs. removability, item 3).
No revision to the core finding that a principled, virtuous unification exists and the spike's `BLOCKED` was
premature.

---

## 9. One-paragraph escalation summary (for orchestrator)

The round-1 `BLOCKED` verdict is **refuted**. A single principled object — a **morphism of proof systems**
`ProofSigHom σ₁ σ₂` (formula map `g` respecting `imp`, a **Type-valued** axiom-family morphism
`∀ φ, Ax₁ φ → Ax₂ (g φ)`, and closure-operator coherence) — has a **functorial action `Deriv.map` on the
free derivation algebra `Deriv σ`** that **is** the lift. Modal `liftDerivation`, PL `liftDerivationTree`,
Bimodal `DerivationTree.lift`, and Bimodal `liftDerivationWith` are four instances; their required coherence
lemmas (`liftFormula_imp` definitional, `liftFormula_swapTemporal` propositional) already exist in source.
The spike's three obstacles are framing artifacts (predicate-vs-family, parametricity, and a `Prop`/`Type`
confusion), and the one candidate for an *essential* obstruction (Bimodal freshness) is merely orthogonal,
not non-functorial. Mathlib confirms the concept (`FirstOrder.Language.LHom`, `Cat.freeMap`) but lacks the
branching/indexed free-derivation machinery, which must be hand-built (~one Foundations file). **Recommended
realization: a non-invasive Foundations overlay (A1)** that adds the abstraction and exhibits all four lifts
as `Deriv.map` instances **without disturbing 190+ downstream proof files**, gated behind a **PL pilot (A3)**;
explicitly **not** the maximal inductive-replacement (A2), which is XL and ergonomically regressive. The
honest caveat: A1 unifies *concept and metatheory*, not *line count* — worth it if the project values a
reusable, documented "morphism of proof systems" layer, which is exactly what task 419 set out to build.
```
