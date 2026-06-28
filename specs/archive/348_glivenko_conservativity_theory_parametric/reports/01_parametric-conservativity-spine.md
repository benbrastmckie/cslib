# Research Report: Theory-Parametric Glivenko & Conservativity Spine

- **Task**: 348 - glivenko_conservativity_theory_parametric
- **Started**: 2026-06-26T00:00:00Z
- **Completed**: 2026-06-27T00:00:00Z
- **Effort**: ~3 hours
- **Dependencies**: Task 341 (parametric algebraic completeness — landed), Task 345 (`IsMinimal`/`MinimalAxioms` bridge — researched), Task 352 (classical implicational fragment — the obstruction boundary)
- **Sources/Inputs**:
  - `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpBotConservative.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/MplPointedConservative.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaum.lean`
  - `Cslib/Logics/Propositional/Semantics/Algebra.lean` (`AlgEvaluate`, `AlgTValid`, `⊨[`)
  - `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean`
  - `Cslib/Logics/Propositional/Defs.lean` (`IsIntuitionistic`/`IsClassical`)
  - `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (`MinimalAxioms`)
  - `specs/345_reconcile_logic_encodings_isminimal/reports/01_team-research.md`
  - Mathlib `Mathlib/Order/Heyting/Hom.lean` (`HeytingHom`, `HeytingHomClass`)
- **Artifacts**: `specs/348_glivenko_conservativity_theory_parametric/reports/01_parametric-conservativity-spine.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `HilbertCompleteness.lean` (`hilbert_alg_complete_theory` — the single parametric completeness backend), `HilbertLindenbaum.lean` (Lindenbaum quotient + `canonicalV`/`canonicalBotVal`), `FragmentPredicates.lean` (`IsBotFree ⊃ IsOrFree ⊃ IsOrBotFree ⊃ IsImpTopOnly`), task 345 `IsMinimal`/`MinimalAxioms` bridge.
- **Downstream Dependents**: the `*Conservative*`/`Glivenko` family theorems, `ConservativeChain.lean` capstone, and any future PR that wants per-tier results as corollaries.
- **Alternative Paths**: direct-algebraic MPL route (`MplConservativeChain.lean`) vs IPL-routing (`ConservativeChain.lean`) — both already exist; parametrization should not collapse the pair, only factor the shared skeleton.
- **Potential Extensions**: a future bundled `GeneralizedHeytingHom` class (does not exist in Mathlib) could later subsume the embedding-combinator hypothesis, but is out of scope here.

## Executive Summary

- The conservativity programme is **three layers, not one**: (L1) algebraic completeness — *already unified* as `hilbert_alg_complete_theory (Axioms) [MinimalAxioms Axioms]`; (L2) the **syntactic subsumption + ND-bridge skeleton** — uniform and fully parametrizable; (L3) the **embedding/commutation lemmas gated by fragment predicates** — irreducibly per-completion. Task 348's wins live in L2 and in a thin parametric wrapper over L3, plus a theory-parametric Glivenko.
- A **theory-parametric Glivenko** is clean: its algebraic core `glivenko_algebraic` (BA-valid `φ` ⟹ HA-valid `¬¬φ`) is *already theory-agnostic*. The proof-level statement parametrizes over a classical-strength source `Axioms_cl` and an intuitionistic-strength target `Axioms_int`, with the strength predicates supplying exactly the two hypotheses (BA-soundness of the source, HA-completeness of the target).
- A **theory-parametric conservativity** statement is only *partially* unifiable: the outer skeleton "complete-to-big-algebra → embed into a free completion → commute → complete-from-small-algebra" can be one combinator, but each of the five completions (`WithBot`, `Heyting.Regular`, `FreeMeetExtension`, `LowerSet`, `NonemptyLowerSet`) supplies a bespoke commutation lemma that must remain an explicit hypothesis.
- **No `GeneralizedHeytingHom.map_interpret` and no Waring `Heyting.lean` exist** in CSLib (verified by grep). Mathlib supplies only `HeytingHom`/`HeytingHomClass` (`map_himp`, `map_inf`, `map_sup`, `map_bot`, `map_top`) between *HeytingAlgebras*. The actual reusable kernel is a generic `AlgEvaluate`-intertwining lemma the plan must *introduce*, not reuse — and several real embeddings (`toRegular`, `LowerSet.Iic`) are not hom-class instances, so the combinator cannot derive its commutation hypothesis from a generic hom.
- **345 reuse**: state the strength hypotheses as set-inclusions on `AxiomTheory Axioms` (`minimal ⊆ AxiomTheory A`, `IPL ⊆ AxiomTheory A_int`, `CPL ⊆ AxiomTheory A_cl`) and convert to/from `[MinimalAxioms]`/`IsIntuitionistic`/`IsClassical` via 345's `mem_axiomTheory` (`Iff.rfl`) + `Set.setOf_subset_setOf` bridge. This is the `AxiomTheory ⊆` inclusion idiom the task names.
- **The faithfulness risk** is real and singular: any parametric statement must keep Glivenko's target pinned at intuitionistic-strength + *Heyting*-completeness and must keep the conservativity combinator's commutation lemma explicit — otherwise it would silently assert the classical fragments are Heyting/Brouwerian-complete (false; Peirce invalid in free Heyting completions — the task 352 obstruction).

## Context & Scope

The task asks: restate Glivenko and the `*Conservative*` family theory-parametrically over `Axioms` plus a strength predicate / `AxiomTheory ⊆` hypothesis, so per-tier results become corollaries. The grounding context fixes the boundary: L1 completeness is done (341); the obstruction is that classical fragments are not Heyting-complete (352), so 348 targets the **syntactic bridge layer + the algebraic (min/int) completeness backends + Glivenko**, not classical fragment completeness.

### The single parametric backend that already exists (L1)

`HilbertCompleteness.lean:64`:

```
theorem hilbert_alg_complete_theory {Atom : Type u}
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms]
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms → AlgEvaluate v bot_val φ = ⊤
```

`MPL.hilbert_alg_complete` / `IPL.hilbert_alg_complete` / `CPL.hilbert_alg_complete`
(`HilbertCompleteness.lean:93,122,155`) are already corollaries; the efq/dne distinction
rides entirely as the semantic hypothesis `v ⊨[bot_val] AxiomTheory Axioms`. The Lindenbaum
quotient enters only in the backward direction via `canonicalV`, `canonicalBotVal`,
`canonicalV_spec`, `canonicalV_algTValid`, `hilbertLindenbaumMk_eq_top_iff`
(`HilbertLindenbaum.lean:591,596,607,638,557`). Task 348 should treat this theorem as a
fixed black box and build the conservativity/Glivenko layer on top of it.

## Findings

### F1. The syntactic subsumption skeleton (L2) is already one shape — make it one lemma

Every "subsumption" theorem in the family is `liftDerivationTree` applied to a `toX` coercion
(`ConjImpConservative.lean:59` defines `liftDerivationTree` over `h_sub : ∀ ψ, A1 ψ → A2 ψ`):

| Concrete theorem | File:line | `h_sub` used |
|---|---|---|
| `derivableConjImpOfDerivableInt` | `ConjImpConservative.lean:104` | `hψ.toMinPropAxiom.toIntPropAxiom` |
| `derivableMinOfDerivableInt` | `ConservativeChain.lean:110` | `hψ.toIntPropAxiom` |
| `derivableIntOfDerivableProp` | `ConservativeChain.lean:121` | `hψ.toPropAxiom` |
| `derivableImpOfDerivableInt` | `ImpConservative.lean:135` | `hψ.toConjImpAxiom.toMinPropAxiom.toIntPropAxiom` |
| `derivableConjImpBotOfDerivableInt` | `ConjImpBotConservative.lean:108` | `hψ.toIntPropAxiom` |
| `derivableMinOfDerivableConjImp` / `…OfDerivableImp` | `MplConservativeChain.lean:278,290` | `.toMinPropAxiom` chains |

**Proposed parametric form** (the `AxiomTheory ⊆` idiom):

```
theorem derivable_mono {Atom : Type u} {A₁ A₂ : PL.Proposition Atom → Prop}
    (h_sub : ∀ ψ, A₁ ψ → A₂ ψ) {φ} (h : Derivable A₁ φ) : Derivable A₂ φ
  := let ⟨d⟩ := h; ⟨liftDerivationTree h_sub d⟩
```

All six concrete subsumptions then become one-liners `derivable_mono (fun _ h => h.toX…)`.
Equivalently, state `h_sub` as `AxiomTheory A₁ ⊆ AxiomTheory A₂` (defeq to the predicate
implication via `mem_axiomTheory = Iff.rfl`, per 345), aligning with the inclusion idiom.

### F2. The ND bridges (L2) are already `MinimalAxioms`-parametric under the hood

`derivableInMplIffDerivableMin` / `…IplIffDerivableInt` / `…CplIffDerivableProp`
(`HilbertConservativeGlivenko.lean:128,138,148`) each compose `axiomTheory_*_iff_*`
(from `AxiomAdmissibility.lean`) with `hilbert_iff_nd_*.symm` (from `Equivalence.lean`).
The `hilbert_iff_nd_*` lemmas are specializations of a generic `[MinimalAxioms Axioms]`
equivalence (`Equivalence.lean:291,307`). So the three bridges are instances of a single:

```
theorem derivableIn_axiomTheory_iff_derivable {Atom} [DecidableEq Atom]
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms] {φ} :
    DerivableIn (AxiomTheory Axioms) φ ↔ Derivable Axioms φ
```

The three named bridges recover by `(axiomTheory_*_iff_*).trans (this …)`. This consolidation
is low-risk and directly serves "per-tier results as corollaries of a parametric statement."

### F3. Theory-parametric Glivenko: clean, because the algebraic core is already theory-free

`glivenko_algebraic` (`Glivenko.lean:88`) is *already* parametric over nothing but the formula:
`(∀ BA, AlgEvaluate v ⊥ A = ⊤) → (∀ HA, AlgEvaluate v ⊥ (¬¬A) = ⊤)`. The proof-level
`hilbertGlivenko` (`HilbertConservativeGlivenko.lean:109`) only wires it between two fixed
tiers via `CPL.hilbert_alg_complete.mp` and `IPL.hilbert_alg_complete.mpr`. The parametric
restatement abstracts the two tiers:

```
theorem hilbertGlivenko_theory {Atom : Type u}
    (A_cl A_int : PL.Proposition Atom → Prop) [MinimalAxioms A_cl] [MinimalAxioms A_int]
    (h_cl  : ∀ φ, Derivable A_cl φ → BAValid.{u,u} φ)        -- classical-strength source
    (h_int : ∀ φ, HAValid.{u,u} φ → Derivable A_int φ)       -- intuitionistic-strength target
    {φ} (h : Derivable A_cl φ) : Derivable A_int (¬¬φ)
  := h_int _ (glivenko_algebraic (h_cl _ h))
```

The two hypotheses are exactly where the **strength predicates enter**:
- `h_cl` (Hilbert-soundness toward Boolean algebras) holds iff every `BooleanAlgebra` models
  `AxiomTheory A_cl` — i.e. `A_cl` is classical-strength. Derivable from
  `hilbert_alg_complete_theory.mp` + `prop_alg_axiom_sound`-style BA-soundness, gated by
  `IsClassical (AxiomTheory A_cl)` / `CPL ⊆ AxiomTheory A_cl`.
- `h_int` (Heyting-completeness toward the target) holds iff `A_int` is intuitionistic-strength
  and the target stays at the *Heyting* level. Derivable from `hilbert_alg_complete_theory.mpr`
  + `int_alg_axiom_sound`, gated by `IsIntuitionistic (AxiomTheory A_int)` / `IPL ⊆ AxiomTheory A_int`.

A strength-predicate-facing wrapper is therefore:

```
theorem hilbertGlivenko_strength {Atom : Type u}
    (A_cl A_int : PL.Proposition Atom → Prop) [MinimalAxioms A_cl] [MinimalAxioms A_int]
    (hcl : CPL ⊆ AxiomTheory A_cl) (hint : IPL ⊆ AxiomTheory A_int)
    {φ} (h : Derivable A_cl φ) : Derivable A_int (¬¬φ)
```

with `hcl`/`hint` discharged through `IsClassical`/`IsIntuitionistic` via 345's bridge.
`hilbertGlivenko` is then literally `hilbertGlivenko_theory PropositionalAxiom IntPropAxiom
(fun _ => CPL.hilbert_alg_complete.mp) (fun _ => IPL.hilbert_alg_complete.mpr)`.

**Boundary preserved**: the target is pinned at `HAValid` (Heyting). You cannot weaken
`h_int` to a GHA target (efq would be needed and minimal logic lacks it) nor push the
`¬¬φ` conclusion below IPL — this is the faithful, non-collapsing content.

### F4. Theory-parametric conservativity: skeleton parametrizes, commutation lemmas do not

Every conservativity theorem has the identical four-move skeleton (verified across all five):

| Theorem | Big completeness | Free completion | Commutation lemma | Small completeness | Predicate |
|---|---|---|---|---|---|
| `hilbertIplConservativeOverMpl` (`HilbertConservativeGlivenko.lean:88`) | `IPL.hilbert_alg_complete.mp` | `WithBot G` | `coe_AlgEvaluate` (`Conservative.lean:129`) | `MPL.hilbert_alg_complete.mpr` | `IsBotFree` |
| `hilbertIplConservativeOverConjImp` (`ConjImpConservative.lean:89`) | `IPL.hilbert_alg_complete.mp` | `LowerSet B` | `brouwerianEmbeddingLemma` | `conjImp_brouwerian_complete` | `IsOrBotFree` |
| `hilbertIplConservativeOverConjImpBot` (`ConjImpBotConservative.lean:91`) | `IPL.hilbert_alg_complete.mp` | `NonemptyLowerSet B` | `nonemptyLowerSet_evaluate_commutes` | `conjImpBot_pointedBrouwerian_complete` | `IsOrFree` |
| `hilbertConjImpConservativeOverImp` (`ImpConservative.lean:101`) | `conjImp_brouwerian_soundness_derivable` | `FreeMeetExtension H` | `freeMeetEvaluateEq` (`ImpConservative.lean:74`) | `imp_hilbert_complete` | `IsImpTopOnly` |
| Glivenko's BA→HA step (`Glivenko.lean:88`) | `CPL.hilbert_alg_complete.mp` | `Heyting.Regular H` | `eval_regular_val` (`Glivenko.lean:60`) | `IPL.hilbert_alg_complete.mpr` | (¬¬, all formulas) |

**The shared skeleton** can be one combinator (schematic — the commutation lemma is an
explicit hypothesis, not derived):

```
theorem conservative_via_embedding {Atom : Type u}
    (A_big A_small : PL.Proposition Atom → Prop) {P : PL.Proposition Atom → Bool}
    (big_complete  : ∀ φ, Derivable A_big φ → BigValid φ)
    (small_complete: ∀ φ, P φ = true → SmallValid φ → Derivable A_small φ)
    (commute : ∀ φ, P φ = true → (BigValid φ → SmallValid φ))   -- the bespoke embedding lemma
    {φ} (hP : P φ = true) (h : Derivable A_big φ) : Derivable A_small φ
  := small_complete φ hP (commute φ hP (big_complete φ h))
```

Each of the five rows instantiates `commute` with its own completion + commutation lemma.
**This is the irreducible L3 layer**: the embeddings `WithBot`/`Heyting.Regular`/
`FreeMeetExtension`/`LowerSet`/`NonemptyLowerSet` are genuinely different objects, several are
*not* Heyting-hom instances (`Heyting.Regular.toRegular` is the double-negation nucleus, not a
lattice hom; `LowerSet.Iic` does not preserve `⊥`), and each commutation lemma is proved by a
distinct structural induction gated by a distinct fragment predicate. The plan must keep these
as supplied hypotheses; it must **not** attempt to derive them from a single hom typeclass.

### F5. The `*_iff_chain` biconditionals (L2) are mechanical `⟨conservativity, mono⟩` pairs

`impAxiom_iff_chain`, `conjImpAxiom_iff_chain`, `minAxiom_iff_chain`
(`ConservativeChain.lean:265,272,279`), `mplAxiom_iff_conjImpAxiom`/`…BotMinAxiom`/`…impAxiom`
(`MplConservativeChain.lean:197,231,263), and the `hilbert…_iff` triple all have the form
`⟨forward conservativity, derivable_mono (toX…)⟩`. Once F1 (`derivable_mono`) and F4
(`conservative_via_embedding`) land, these are uniform two-field anonymous constructors. They
need no new parametric statement — they are recovered, not restated.

### F6. The `GeneralizedHeytingHom.map_interpret` / Waring `Heyting.lean` machinery does not exist

`grep` over the whole repo (excluding `.lake`) returns **zero** hits for `GeneralizedHeytingHom`,
`map_interpret`, or any `Heyting.lean`. Mathlib (`Mathlib/Order/Heyting/Hom.lean:41,69`) provides
only `HeytingHom`/`HeytingHomClass` between `HeytingAlgebra`s, exporting `map_himp`, `map_inf`,
`map_sup`, `map_bot`, `map_top`. **Implication for the plan**: the "Heyting-homomorphism
machinery" the task description hopes to reuse must be *introduced*, not reused. The honest,
minimal new asset is a generic intertwining lemma over a Mathlib `HeytingHom` (or a
locally-defined GHA hom):

```
theorem AlgEvaluate_heytingHom {H K} [HeytingAlgebra H] [HeytingAlgebra K]
    (f : HeytingHom H K) (v : Atom → H) (bot_val : H) (φ) :
    AlgEvaluate (f ∘ v) (f bot_val) φ = f (AlgEvaluate v bot_val φ)
```

provable by induction reusing `map_himp/map_inf/map_sup`. **But** this only covers full
Heyting homs; the four fragment commutation lemmas in F4 hold on *fragments* precisely because
their embeddings are *not* full homs (which is why fragment predicates gate them). So
`AlgEvaluate_heytingHom` is a nice-to-have that subsumes at most the `coe_AlgEvaluate` /
Glivenko cases partially, not the Brouwerian/free-meet cases. Recommend treating it as optional.

### F7. 345 reuse — inclusion view reconciles the two carrier conventions

345 establishes `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` and, via `mem_axiomTheory`
(`@[simp] Iff.rfl`) + `Set.setOf_subset_setOf`, the bridges
`IsMinimal T ↔ minimal ⊆ T` and `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`.
This is what lets 348 state strength hypotheses uniformly:
- `IsIntuitionistic`/`IsClassical` live on `Theory Atom` (a `Set`) — `Defs.lean:166,175`,
  with `isIntuitionisticIff : IsIntuitionistic T ↔ IPL ⊆ T` and
  `isClassicalIff : IsClassical T ↔ CPL ⊆ T` (`Defs.lean:171,180`).
- `MinimalAxioms` lives on a predicate `Proposition → Prop` (`Equivalence.lean:114`).
- The completeness backend `hilbert_alg_complete_theory` consumes the **predicate** form.

345's bridge is the adapter: a Glivenko/conservativity statement may take `IPL ⊆ AxiomTheory A_int`
and `CPL ⊆ AxiomTheory A_cl` (set inclusions, matching `IsIntuitionistic`/`IsClassical`) and
push them through to the predicate-level `MinimalAxioms`/strength facts the backend needs.
**Dependency confirmed**: 348 should not re-derive these; it consumes 345's `minimal ⊆ AxiomTheory`
view and `isIntuitionisticIff`/`isClassicalIff`.

### F8. Corollary recovery map (deliverable 4)

| Existing per-tier theorem | Recovered as |
|---|---|
| `hilbertGlivenko` / `glivenko` | `hilbertGlivenko_theory PropositionalAxiom IntPropAxiom …`; ND via F2 bridge |
| `hilbertIplConservativeOverMpl` / `ipl_conservative_over_mpl` | `conservative_via_embedding` @ `WithBot` + `coe_AlgEvaluate`; ND via F2 |
| `hilbertIplConservativeOverConjImp(Bot)` | `conservative_via_embedding` @ `LowerSet`/`NonemptyLowerSet` |
| `hilbertConjImpConservativeOverImp` | `conservative_via_embedding` @ `FreeMeetExtension` |
| `hilbertMplConservativeOver{ConjImp,Imp,ConjImpBot}(_direct)` | composition of `conservative_via_embedding` instances + `derivable_mono` (F1) |
| `*_iff_chain`, `*Axiom_iff_*` | `⟨conservativity, derivable_mono⟩` (F5) |
| `derivableIn{Mpl,Ipl,Cpl}Iff…` | instances of `derivableIn_axiomTheory_iff_derivable` (F2) |

## Decisions

- **D1.** Scope L1 (completeness) out — `hilbert_alg_complete_theory` is the fixed backend.
- **D2.** Parametrize L2 fully: introduce `derivable_mono` (F1) and `derivableIn_axiomTheory_iff_derivable` (F2); recover all subsumptions/bridges/`_iff_chain` as corollaries.
- **D3.** Introduce `hilbertGlivenko_theory` + a strength wrapper (F3) as the theory-parametric Glivenko; keep the target pinned at `HAValid`/`IsIntuitionistic`.
- **D4.** Introduce `conservative_via_embedding` (F4) as the shared skeleton, with the commutation lemma as an explicit hypothesis; do **not** unify the five completions or their commutation lemmas.
- **D5.** Reuse 345's `minimal ⊆ AxiomTheory` / `isIntuitionisticIff` / `isClassicalIff` to state strength hypotheses as inclusions; do not re-derive.
- **D6.** `AlgEvaluate_heytingHom` (F6) is optional; do not block on it and do not pretend it covers the Brouwerian/free-meet fragments.

## Recommendations

1. **Phase 1 — subsumption skeleton (L2 core).** Add public `derivable_mono` (F1) in a low file
   (it only needs `liftDerivationTree`); re-express the six `derivableXOfDerivableY` as one-liners.
   Lowest risk; unlocks F5.
2. **Phase 2 — ND bridge consolidation (L2).** Add `derivableIn_axiomTheory_iff_derivable
   [MinimalAxioms]` (F2); recover the three `derivableIn*Iff*`. Pure composition, no new math.
3. **Phase 3 — theory-parametric Glivenko (L1-min/int + Glivenko core).** Add
   `hilbertGlivenko_theory` and the `IsClassical`/`IsIntuitionistic` wrapper (F3); recover
   `hilbertGlivenko`/`glivenko`. This is the task's headline deliverable.
4. **Phase 4 — conservativity combinator (skeleton over L3).** Add `conservative_via_embedding`
   (F4); re-derive the four `hilbertXConservativeOverY` and the MPL chain as instantiations,
   keeping each bespoke commutation lemma. Largest surface; do after Phases 1–3 are green.
5. **Phase 5 — inclusion-view restatements + (optional) `AlgEvaluate_heytingHom`.** Surface
   345's `AxiomTheory ⊆` forms on the new statements; add the optional hom-intertwining lemma
   only if it lands clean and demonstrably shortens the Glivenko/`WithBot` cases.
6. **CI discipline throughout**: every new file `import Cslib.Init`; docstrings on all new decls
   (docBlame); `theorem`/`lemma` for Prop-valued; camelCase, no underscores in new names
   (existing snake_case ND corollaries are pre-existing and out of scope to rename); build the
   whole `Logics/Propositional/Semantics/Algebra` subtree (new lemmas may perturb `simp`/`grind`);
   run `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake test`,
   `lake shake`. **Zero-debt**: no `sorry`, no new axiom — every restatement here is a
   composition of existing, fully-proved lemmas, so a sorry-free path is guaranteed.

## Risks & Mitigations

- **R1 (headline) — collapsing the classical/algebraic boundary.** Over-generalizing Glivenko's
  target or the conservativity combinator could implicitly assert Heyting/Brouwerian completeness
  for classical fragments (false — Peirce invalid in free Heyting completions; task 352's
  separate Boolean/Kalmár proof exists precisely for this). *Mitigation*: pin the Glivenko target
  at `HAValid`/`IsIntuitionistic`; keep `conservative_via_embedding`'s commutation lemma an
  explicit hypothesis so no instantiation can be created without an actually-proved embedding.
- **R2 — phantom Heyting-hom reuse.** The task names `GeneralizedHeytingHom.map_interpret`/Waring
  `Heyting.lean`, which do not exist (F6). *Mitigation*: the plan treats the intertwining lemma
  as a new (optional) asset over Mathlib `HeytingHom`, and does not route the Brouwerian/free-meet
  cases through it.
- **R3 — carrier mismatch (Set vs predicate).** `IsIntuitionistic`/`IsClassical` are on `Theory`
  (Set) while the backend is predicate-keyed. *Mitigation*: 345's `mem_axiomTheory = Iff.rfl` +
  `setOf_subset_setOf` bridge (F7) is exactly the adapter; depend on 345.
- **R4 — universe pinning.** `hilbert_alg_complete_theory` pins `{Atom : Type u}` and `(H : Type u)`
  to one level (`HilbertCompleteness.lean:60–63`); the validity abbrevs use `.{u,u}`. *Mitigation*:
  carry the explicit `.{u,u}` annotations in all parametric statements, mirroring the existing
  `MPL/IPL/CPL.hilbert_alg_complete` signatures.
- **R5 — `attribute [-instance]` fragility.** `MplConservativeChain.lean:128` locally suppresses
  `BrouwerianSemilattice.toHilbertAlgebra` to avoid a `Preorder` diamond. *Mitigation*: any
  combinator that abstracts the `LowerSet` route must preserve that local attribute scoping, or it
  will reintroduce the diamond; keep the combinator's `BigValid`/`SmallValid` as opaque `Prop`s so
  the instance resolution stays at the call site.

## Context Extension Recommendations

- **Topic**: "Three-layer anatomy of the propositional conservativity programme (completeness
  backend / syntactic skeleton / embedding-commutation lemmas)."
- **Gap**: No CSLib context file records which layer is unified (341), which is unifiable (348),
  and which is irreducibly per-completion (the task 352 obstruction). Future agents re-derive this.
- **Recommendation**: add a short note under the propositional algebra context capturing the
  L1/L2/L3 split and the "commutation lemma stays explicit" rule, cross-referencing tasks 341,
  345, 348, 352.

## Appendix

### Key signatures (grounded, verbatim locations)

- `hilbert_alg_complete_theory` — `HilbertCompleteness.lean:64`
- `glivenko_algebraic` — `Glivenko.lean:88`; `eval_regular_val` — `Glivenko.lean:60`
- `hilbertGlivenko` — `HilbertConservativeGlivenko.lean:109`; `glivenko` (ND) — `:172`
- `liftDerivationTree` — `ConjImpConservative.lean:59`
- `coe_AlgEvaluate` / `instHeytingAlgebraWithBot` — `Conservative.lean:129` / `:102`
- `AlgEvaluate` / `AlgTValid` / `⊨[` notation — `Algebra.lean:90` / `:149` / `:156`
- Fragment predicates + subsumption lemmas — `FragmentPredicates.lean:46,54,63,73,85,99,113`
- `IsIntuitionistic`/`IsClassical` + `…Iff` — `Defs.lean:166,171,175,180`
- `MinimalAxioms` class + instances — `Equivalence.lean:114,135,146,157`
- Lindenbaum quotient API — `HilbertLindenbaum.lean:146,591,596,607,557,638`
- Mathlib `HeytingHom`/`HeytingHomClass` — `Mathlib/Order/Heyting/Hom.lean:41,69` (`map_himp` exported)

### Negative findings (verified absent)

- `GeneralizedHeytingHom`, `map_interpret`, `Heyting.lean` (Waring): zero hits in `Cslib/` and zero `GeneralizedHeytingHom` in Mathlib.
- No existing theory-parametric Glivenko or theory-parametric conservativity statement; the only parametric theorem in the family is `hilbert_alg_complete_theory` (completeness, L1).

### References

- [Glivenko1929], [Rasiowa1974], [RasiowaSikorski1963], [Nemitz1965], [Kohler1981] — as cited across the family file headers.
- `specs/345_reconcile_logic_encodings_isminimal/reports/01_team-research.md` — `IsMinimal`/`MinimalAxioms` bridge.
