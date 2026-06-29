# Research Report 01: Per-fragment algebraic completeness for the generic Derivable P-logic framework

- **Task**: 410 `fragment_generic_algebraic_completeness`
- **Started**: 2026-06-29
- **Completed**: 2026-06-29
- **Task type**: cslib
- **Session**: sess_1782760056_06c853_410
- **Depends on**: 407 (delivers `FragmentGeneric.lean`; status [PR READY])
- **Sources read (live, 2026-06-29)**:
  - `Cslib/Logics/Propositional/Semantics/Algebra/FragmentGeneric.lean` (the residual, lines 40-53)
  - `Semantics/Algebra.lean` (base: `AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid`)
  - `Semantics/Algebra/Conservative.lean`, `FragmentPredicates.lean`
  - `Semantics/Algebra/HilbertCompleteness.lean` (`hilbert_alg_complete_theory`, `MPL/IPL/CPL.hilbert_alg_complete`)
  - `Semantics/Algebra/MplConservativeChain.lean` (the per-fragment Derivable links + `LowerSet B` bridge)
  - `Semantics/Algebra/BrouwerianCompletenessGeneric.lean`, `BrouwerianCompleteness.lean` (`conjImp_brouwerian_complete`)
  - `ProofSystem/FragmentAxioms.lean` (`ConjImpAxiom`, `ImpAxiom`), `ProofSystem/Axioms.lean` (`ConjImpAxioms` class)
  - `references.bib` (Rasiowa1974 @771, Nemitz1965 @825, Kohler1981 @835)
  - task 407 report 03

---

## Executive Summary

- **The residual is, in substance, already discharged piecewise — what is missing is the *unifying abstraction*, not new mathematics.** `MplConservativeChain.lean` + `HilbertCompleteness.lean` + `BrouwerianCompleteness*.lean` together already prove, for each fragment, a `Derivable Ax_P φ ↔ GHAValid φ` link. Task 410 should deliver a thin `CanAlgComplete P` typeclass that *packages* these existing results behind one interface, with all instances provable by reuse. This is the reuse-first reading and it is strongly preferred over re-deriving canonical models.
- **The completeness property a fragment P needs is exactly: a target axiom system `Ax_P` together with (i) a "validity reaches the canonical model" step and (ii) a Lindenbaum/truth-lemma closing `GHAValid φ → Derivable Ax_P φ` for `P φ`.** Both (i) and (ii) already exist for every fragment named in the residual.
- **`CanAlgComplete P` should bundle `Ax_P` + `complete : P φ → GHAValid φ → Derivable Ax_P φ` + `sound : Derivable Ax_P φ → GHAValid φ`.** Then `(CanAlgComplete P) → (Derivable Ax_P φ ↔ GHAValid φ)` for `P φ`, and composing with `AlgEvalIndependent P` (from 407) + `generic_gha_implies_ha` yields the `HAValid` form for ⊥-free fragments. A Lean signature sketch is given in §3 and is grounded in verified existing signatures.
- **IsBotFree instance**: trivial. `MPL.hilbert_alg_complete : Derivable MinPropAxiom φ ↔ GHAValid φ` is **total** (holds for *all* φ). So `Ax = MinPropAxiom`, `complete`/`sound` are its two directions; the fragment-specific content is only the `HAValid ↔ GHAValid` collapse, already delivered by 407's `ghaValid_iff_haValid_of_botFree`.
- **IsOrBotFree instance**: already proved as `mplAxiom_iff_conjImpAxiom` (Mathlib API: `LowerSet B` as the free-join Heyting completion; `BrouwerianSemilattice`; `conjImp_brouwerian_complete`). `Ax = ConjImpAxiom`.
- **IsImpTopOnly is RECOVERABLE today and does NOT require the Rasiowa free algebra.** `mplAxiom_iff_impAxiom` already proves `Derivable MinPropAxiom φ ↔ Derivable ImpAxiom φ` for imp-top-only φ, routed through ConjImp via `IsImpTopOnly_implies_IsOrBotFree` (i.e. through `LowerSet B`, not a bespoke implicative free algebra). The residual's "routes through the Rasiowa free algebra" is an over-statement of the current architecture's requirements. `Ax = ImpAxiom`.
- **BibKey grounding (H3)**: `Rasiowa1974`, `Nemitz1965`, `Kohler1981` all present in `references.bib` and already cited in the relevant modules. No new key needed. Rasiowa1974 underpins the algebraic-completeness method generally; the implicational free algebra it describes is an *alternative* route, not the one CSLib uses.
- **Zero-debt outlook**: the proposed instances compose existing sorry-free theorems. No `sorry`, no new axiom, no vacuous definition is required. Task 410 is a definition+instantiation (abstraction) task, not open research.

---

## Context & Scope

`FragmentGeneric.lean` (task 407 phase 7 S3 spike) abstracted the ⊥-free fragment via
`AlgEvalIndependent P` and proved the easy validity directions:
`generic_gha_implies_ha` (`GHAValid → HAValid`, generic) and `ghaValid_of_botFree_of_haValid`
(`HAValid → GHAValid` for `IsBotFree`, via the `WithBot G` Heyting embedding), giving
`ghaValid_iff_haValid_of_botFree`. The documented residual (lines 40-53) is the *syntactic*
side: `HAValid φ → Derivable X-logic φ`, said to require per-fragment algebraic completeness
"not currently generic in P", with each fragment routed through a different canonical model.

The research goal is to (1) name the completeness property a fragment needs, (2) design
`CanAlgComplete P` so that `(CanAlgComplete P, AlgEvalIndependent P) ⟹ (Derivable P-logic φ ↔ GHAValid φ)`,
(3) instantiate for `IsBotFree` and `IsOrBotFree`, (4) decide the fate of `IsImpTopOnly`.

---

## Findings (grounded in `file:line`)

### F1 — The per-fragment completeness links already exist (the central reuse finding)

`MplConservativeChain.lean` already proves exactly the syntactic links the residual calls open,
all routed through `GHAValid` and the **canonical Heyting model `LowerSet B`**:

| Fragment | Existing theorem | Statement |
|---|---|---|
| `IsBotFree` | `MPL.hilbert_alg_complete` (`HilbertCompleteness.lean:93-94`) | `Derivable MinPropAxiom φ ↔ GHAValid φ` (**total**, all φ) |
| `IsOrBotFree` | `mplAxiom_iff_conjImpAxiom` (`MplConservativeChain.lean:197-199`) | `Derivable MinPropAxiom φ ↔ Derivable ConjImpAxiom φ` |
| `IsOrFree` | `mplAxiom_iff_conjImpBotMinAxiom` (`:231-233`) | `Derivable MinPropAxiom φ ↔ Derivable ConjImpBotMinAxiom φ` |
| `IsImpTopOnly` | `mplAxiom_iff_impAxiom` (`:263-265`) | `Derivable MinPropAxiom φ ↔ Derivable ImpAxiom φ` |

The completeness core `GHAValid φ → Derivable Ax_P φ` factors as:
1. `GHAValid_implies_BrouwerianValid_direct hOBF h` (`:143-145`): instantiates `GHAValid φ` **at
   `LowerSet B`** (a Heyting algebra, hence a GHA) via `LowerSet.Iic ∘ v` and `brouwerianEmbeddingLemma`,
   producing `BrouwerianValid φ` for or-bot-free φ.
2. `conjImp_brouwerian_complete hOBF` (`BrouwerianCompleteness.lean:151`): `BrouwerianValid φ → Derivable ConjImpAxiom φ`.

The soundness back-direction is `derivableMinOfDerivableConjImp` / `derivableMinOfDerivableImp`
(`MplConservativeChain.lean:278,290`) composed with `MPL.hilbert_alg_complete.mp`.

**Consequence**: nothing in the residual's syntactic step is unproven. The genuine gap is that
these results are stated per-axiom-system (`ConjImpAxiom`, `ImpAxiom`, …), not behind the
`AlgEvalIndependent`/`P`-parameterized interface that 407 introduced.

### F2 — What "algebraic completeness property for P" actually is (research goal 1)

A fragment predicate `P` "can be algebraically completed" iff there is a target axiom system
`Ax_P : Proposition Atom → Prop` such that:

- **(C) Completeness core**: `∀ φ, P φ = true → GHAValid φ → Derivable Ax_P φ`.
  This is the canonical-model/Lindenbaum/truth-lemma content. It is the *only* fragment-specific
  ingredient, and it is the composite `(2)∘(1)` of F1 (or, for `IsBotFree`, the total
  `MPL.hilbert_alg_complete.mpr`).
- **(S) Soundness**: `∀ φ, Derivable Ax_P φ → GHAValid φ`.
  Already available as `MPL.hilbert_alg_complete.mp ∘ derivableMinOfDerivable…`.

`AlgEvalIndependent P` (from 407) is the *orthogonal* ingredient that lets the `GHAValid` iff be
restated as an `HAValid` iff on the fragment (via `generic_gha_implies_ha` + the `WithBot`
converse `ghaValid_of_botFree_of_haValid`). It is not part of completeness; it bridges the two
validity notions. The task's pairing `(CanAlgComplete P, AlgEvalIndependent P)` is therefore the
right decomposition: completeness (syntax ↔ GHA-validity) × independence (GHA-validity ↔ HA-validity).

### F3 — `IsImpTopOnly` is recoverable now; the Rasiowa free algebra is not required (research goal 4)

`mplAxiom_iff_impAxiom` (`:263-265`) already closes the implicational fragment, and its proof
(`hilbertMplConservativeOverImp_direct`, `:249-253`) routes **through ConjImp** via
`IsImpTopOnly_implies_IsOrBotFree φ hITO` (`FragmentPredicates.lean:95`) and hence through the
`LowerSet B` Heyting model — **not** through a bespoke implicative-semilattice free algebra.
The residual's claim that `IsImpTopOnly` "routes through the Rasiowa free algebra" describes the
textbook construction in [Rasiowa1974], but the CSLib architecture obtains the same theorem more
cheaply by fragment subsumption. **Recommendation: instantiate `CanAlgComplete IsImpTopOnly`
with `Ax = ImpAxiom` by reuse; do NOT build a Rasiowa free algebra.** (A standalone implicative
free algebra would be a large net-new development with no payoff for this task and is explicitly
not needed for zero-debt closure.)

### F4 — `IsBotFree` is the cheapest instance, but its target logic is MPL, not a ⊥-fragment

Because `MPL.hilbert_alg_complete` is total, `Derivable MinPropAxiom φ ↔ GHAValid φ` already holds
for every φ, including ⊥-free ones. So `CanAlgComplete IsBotFree` takes `Ax = MinPropAxiom` and
both fields are projections of one existing iff. The *only* place ⊥-freeness is used is to upgrade
`GHAValid` to `HAValid` (407's `ghaValid_iff_haValid_of_botFree`, via `WithBot G` +
`instHeytingAlgebraWithBot`, `Conservative.lean:102`). This matches the residual's
"`WithBot G` + Heyting completeness" but shows the Heyting-completeness half is just MPL completeness.

### F5 — Mathlib / CSLib API inventory for the instantiations

- **`LowerSet B`** (Mathlib `Mathlib.Order.UpperLower`): the free-join completion used as the
  canonical Heyting algebra for the Brouwerian fragment; `LowerSet.Iic` is the principal-downset
  embedding (`MplConservativeChain.lean:144`). This is the "LowerSet B + Brouwerian completeness"
  route named in the residual — already wired.
- **`WithBot G`** + `instHeytingAlgebraWithBot` (`Conservative.lean:102`): adjoins a fresh bottom
  to any GHA to obtain a Heyting algebra; underpins the `IsBotFree` HAValid↔GHAValid collapse.
- **`BrouwerianSemilattice`** (CSLib-local, `BrouwerianBot.lean`): meet-semilattice with relative
  pseudocomplement; *not* a Mathlib class. `BrouwerianValid`/`BrouwerianBotValid` are the matching
  validity predicates (`Brouwerian.lean:106`, `BrouwerianBot.lean:117`).
- **`ConjImpAxioms`** typeclass (`Axioms.lean:191`): the 5-field conj-imp interface over which
  `brouwerianBot_complete` and `conjImp_brouwerian_complete` are already generic. **This is the
  precedent for the `CanAlgComplete` design**: CSLib already favors typeclass-parameterized
  completeness, so a `CanAlgComplete` typeclass is idiomatic.
- **Heyting algebra API**: `Mathlib.Order.Heyting.Basic`, `le_himp_iff`, `HeytingAlgebra.ofHImp`
  (used in `Conservative.lean:104`).

### F6 — Why a *single* `AlgEvaluate`-generic theorem cannot literally cover all three (honesty note)

The three fragments use three *different evaluators* over three *different* algebra classes:
`AlgEvaluate` over GHA, `BrouwerianEvaluate`/`BrouwerianBotEvaluate` over `BrouwerianSemilattice`.
There is no single Mathlib superclass with one evaluator subsuming all three, so a literally
"fully generic over P with one `AlgEvaluate`" completeness theorem is not achievable as one
inductive proof. The achievable — and idiomatic — genericity is the **typeclass-instance** form:
one `CanAlgComplete`-driven theorem, three reuse-built instances. This reframes the residual's
"open research" honestly: it is open *as a single uniform proof*, closed *as a bundled interface*.

---

## Research Goal 2 — `CanAlgComplete` design and Lean signature sketch

Idiomatic CSLib design (mirrors `ConjImpAxioms`): a `Prop`-valued structure/typeclass bundling
the target logic and the two completeness directions. Placement: a new additive file
`Semantics/Algebra/CanAlgComplete.lean` importing `FragmentGeneric`, `MplConservativeChain`,
`HilbertCompleteness`.

```lean
namespace Cslib.Logic.PL
universe u

/-- A formula predicate `P` is *algebraically completable* if it has a target axiom system
`Ax` whose derivability coincides with GHA-validity on the `P`-fragment. The two fields are the
soundness and completeness halves; both are discharged by reuse for every existing fragment. -/
structure CanAlgComplete {Atom : Type u} (P : PL.Proposition Atom → Bool) where
  /-- The sub-logic whose derivability characterizes the fragment. -/
  Ax      : PL.Proposition Atom → Prop
  /-- Completeness core: GHA-validity of a `P`-formula yields derivability in `Ax`. -/
  complete : ∀ {φ : PL.Proposition Atom}, P φ = true → GHAValid.{u, u} φ → Derivable Ax φ
  /-- Soundness: derivability in `Ax` yields GHA-validity. -/
  sound    : ∀ {φ : PL.Proposition Atom}, Derivable Ax φ → GHAValid.{u, u} φ

/-- The packaged completeness theorem: on the `P`-fragment, derivability in the target logic
is equivalent to GHA-validity. -/
theorem canAlgComplete_iff {Atom : Type u} {P : PL.Proposition Atom → Bool}
    (C : CanAlgComplete P) {φ : PL.Proposition Atom} (hφ : P φ = true) :
    Derivable C.Ax φ ↔ GHAValid.{u, u} φ :=
  ⟨C.sound, C.complete hφ⟩

/-- With evaluation-independence, the GHA characterization upgrades to an HA characterization
on the ⊥-free fragment (combines `generic_gha_implies_ha` with the `WithBot` converse). -/
theorem canAlgComplete_haValid_iff {Atom : Type u} {P : PL.Proposition Atom → Bool}
    (C : CanAlgComplete P) (_hInd : AlgEvalIndependent P)
    (hsub : ∀ {φ}, P φ = true → φ.IsBotFree = true)   -- P ⊆ IsBotFree
    {φ : PL.Proposition Atom} (hφ : P φ = true) :
    Derivable C.Ax φ ↔ HAValid.{u, u} φ := by
  rw [canAlgComplete_iff C hφ]; exact ghaValid_iff_haValid_of_botFree (hsub hφ)

end Cslib.Logic.PL
```

Notes on the sketch:
- `Derivable`, `GHAValid`, `HAValid`, `AlgEvalIndependent`, `ghaValid_iff_haValid_of_botFree` are
  all verified existing names (read from source this session). `canAlgComplete_iff` is a literal
  unpacking; `canAlgComplete_haValid_iff` is the literal composite the task asks for.
- Using a `structure` (data, holding `Ax`) is preferable to a `class` here because `Ax` is *output*
  data that varies per fragment, not something to be inferred by instance search. (Lean's
  instance resolution cannot guess `Ax`.) If a `class` form is desired, make `Ax` a class field
  and provide named instances `instCanAlgComplete_botFree`, etc. — but the structure form is
  cleaner and matches how `ConjImpAxioms` is *consumed*. Recommend structure.
- The `hsub : P ⊆ IsBotFree` side-condition is needed for the HAValid form because the `WithBot`
  converse is only valid on ⊥-free formulas; `IsBotFree`, `IsOrBotFree`, `IsImpTopOnly` all
  satisfy it (`IsOrBotFree_implies_IsBotFree`, `IsImpTopOnly_implies_IsOrBotFree` ∘ that).

---

## Research Goal 3 — Instantiations (by reuse)

### `IsBotFree` (target `MinPropAxiom`)

```lean
def canAlgComplete_isBotFree {Atom : Type u} :
    CanAlgComplete (Atom := Atom) Proposition.IsBotFree where
  Ax := MinPropAxiom
  complete := fun _ h => MPL.hilbert_alg_complete.mpr h      -- total; ignores ⊥-freeness
  sound    := fun h => MPL.hilbert_alg_complete.mp h
```
`Derivable MinPropAxiom φ ↔ HAValid φ` for ⊥-free φ then follows from
`canAlgComplete_haValid_iff` with `hsub := id` and `isBotFree_eval_independent` (407).

### `IsOrBotFree` (target `ConjImpAxiom`)

```lean
def canAlgComplete_isOrBotFree {Atom : Type u} :
    CanAlgComplete (Atom := Atom) Proposition.IsOrBotFree where
  Ax := ConjImpAxiom
  complete := fun hφ h =>
    conjImp_brouwerian_complete hφ (GHAValid_implies_BrouwerianValid_direct hφ h)
  sound    := fun h => MPL.hilbert_alg_complete.mp (derivableMinOfDerivableConjImp h)
```
Mathlib/CSLib API used: `LowerSet B` (free-join Heyting completion) inside
`GHAValid_implies_BrouwerianValid_direct`; `BrouwerianSemilattice` + Lindenbaum quotient inside
`conjImp_brouwerian_complete`. Both already sorry-free. (Equivalently, `Ax := MinPropAxiom` with
`complete`/`sound` from `mplAxiom_iff_conjImpAxiom` composed with `MPL.hilbert_alg_complete` — pick
whichever target logic the task wants to name as "the IsOrBotFree logic". The `ConjImpAxiom`
target is the more faithful "fragment logic".)

### `IsImpTopOnly` (target `ImpAxiom`) — see Goal 4

```lean
def canAlgComplete_isImpTopOnly {Atom : Type u} :
    CanAlgComplete (Atom := Atom) Proposition.IsImpTopOnly where
  Ax := ImpAxiom
  complete := fun hφ h =>
    -- route imp-top-only ⟶ or-bot-free, reuse the ConjImp completeness, then ImpAxiom subsumption
    (mplAxiom_iff_impAxiom hφ).mp (MPL.hilbert_alg_complete.mpr h)
  sound    := fun h => MPL.hilbert_alg_complete.mp (derivableMinOfDerivableImp h)
```

---

## Research Goal 4 — `IsImpTopOnly` verdict

**RECOVERABLE TODAY, by reuse, without the Rasiowa free algebra.** `mplAxiom_iff_impAxiom`
(`MplConservativeChain.lean:263`) already provides the two-way link for imp-top-only φ via the
`IsImpTopOnly → IsOrBotFree → LowerSet B` route. The instance above composes it with the total
`MPL.hilbert_alg_complete`. The Rasiowa free implicative algebra ([Rasiowa1974], the implicational
fragment's term algebra) is a legitimate *alternative* canonical model but is **not required** and
should be **deferred / declined** for task 410 — building it is large net-new work with no
zero-debt benefit here. Flag this as a correction to the residual's framing in the report handoff.

---

## Research Goal 5 — Literature verification (Rasiowa1974)

- `Rasiowa1974` present at `references.bib:771` (Helena Rasiowa, *An Algebraic Approach to
  Non-Classical Logics*, North-Holland, 1974, vol. 78). Cited in `FragmentGeneric.lean:62`,
  `Conservative.lean:25`, `Algebra.lean`, `BrouwerianCompletenessGeneric.lean:56`.
- `Nemitz1965` (`:825`), `Kohler1981` (`:835`): the Brouwerian-semilattice completeness sources,
  cited in `BrouwerianCompletenessGeneric.lean` and `MplConservativeChain.lean`.
- **Method fidelity**: the design follows Rasiowa's algebraic-completeness program (Lindenbaum
  quotient → canonical algebra → truth lemma → completeness). CSLib realizes the canonical algebra
  via `LowerSet B` (join completion) and `WithBot G` (bottom adjunction) rather than per-fragment
  free term algebras; this is a faithful, more reusable instance of the same method. No new BibKey
  required.

---

## Recommendations (prioritized)

1. **Implement `CanAlgComplete` as a `structure`** (not a class) in a new additive file
   `Semantics/Algebra/CanAlgComplete.lean`, with `canAlgComplete_iff` and
   `canAlgComplete_haValid_iff` as the two packaged theorems (§2 sketch). Zero churn to existing files.
2. **Provide the three instances by reuse** (§3): `IsBotFree`→`MinPropAxiom`,
   `IsOrBotFree`→`ConjImpAxiom`, `IsImpTopOnly`→`ImpAxiom`. Each is a 2-field record built from
   verified sorry-free theorems. Optionally add `IsOrFree`→`ConjImpBotMinAxiom` (also free, via
   `mplAxiom_iff_conjImpBotMinAxiom`).
3. **Decline the Rasiowa free implicative algebra** for this task (F3/Goal 4). Document the
   `LowerSet B` route as the chosen canonical model. If a faithful Rasiowa free-algebra
   formalization is independently desired, spawn a separate task — it is not on the zero-debt
   critical path here.
4. **Update `FragmentGeneric.lean` residual note** (lines 40-53) to point at `CanAlgComplete` and
   correct the "open research" / "Rasiowa free algebra required" framing once 410 lands.
5. **CI**: a new file requires `lake exe mk_all --module` (barrel import) and
   `lake exe checkInitImports` (the new file must `import Cslib.Init`). Add docstrings to all new
   declarations (docBlame); use `theorem`/`def` appropriately; lowerCamelCase names with no
   underscores (the existing `canAlgComplete_*` style matches repo convention).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| Universe-polymorphism friction passing `GHAValid` through the structure field | M | M | Pin `.{u,u}` as the existing chain does (`brouwerianBot_complete`, `GHAValid_implies_BrouwerianValid_direct` both do this) |
| `structure` vs `class` choice causes instance-search confusion | L | L | Use `structure` (Ax is output data); consume explicitly, do not rely on instance resolution |
| Reviewer expects a literal single-`AlgEvaluate` generic proof | M | L | Document F6: that form is not achievable across 3 evaluator types; typeclass-instance form is idiomatic (precedent: `ConjImpAxioms`) |
| Diamond on `Preorder B` in `LowerSet.Iic` (seen in chain) | M | M | Reuse `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra` exactly as `MplConservativeChain.lean:127` does, or keep instances inside the already-working `mplAxiom_iff_*` lemmas (preferred — don't re-prove) |

## Tactic Survey (advisory)

All proof obligations in the proposed instances are *term-level compositions* of existing
theorems (`.mp`/`.mpr`, function composition); no search tactics are needed. The two packaged
theorems close by `⟨_, _⟩` / `rw` + `exact`. No `sorry`, no `aesop`/`omega` shortcuts required.

## Open Questions for Planner

- Which target logic should be *named* "the IsBotFree P-logic": `MinPropAxiom` (MPL, the natural
  GHA-complete system) — recommended. Confirm naming with the connective-typeclass reconciliation
  in sibling task 400 if relevant.
- Should `CanAlgComplete` additionally expose the canonical algebra (for downstream reuse) or stay
  minimal (just the iff)? Recommend minimal first; widen only if a consumer needs it.
```
