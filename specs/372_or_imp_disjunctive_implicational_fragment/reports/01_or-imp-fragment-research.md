# Task 372 Research: Disjunctive-Implicational Fragment IPL⟨∨,→,⊤⟩

## 1. Objective

Add the one missing vertex of the propositional fragment lattice: the
disjunctive-implicational fragment `OrImpAxiom` (K, S, orI1, orI2, orE), with its
subsumption, witnesses, substitution closure, fragment-predicate-compatibility lemmas,
deduction-theorem instance, the `Propositional.HilbertOrImp` tag type and its
`InferenceSystem`/`MinimalHilbert` instances, and (optionally) a conservativity step.

**Bottom line.** The core deliverable (axioms + subsumption + witnesses + substitution +
predicate compatibility + deduction theorem + tag type + instances) is a near-mechanical
mirror of the existing fragments and is fully sorry-free / zero-new-axiom. It is **highly
desirable** and low-risk. The **conservativity step is genuinely heavy** (requires a free
*meet* completion that does not exist in the codebase) and should be treated as an optional,
separately-confirmed extension — exactly the caution the task statement anticipates.

## 2. Reuse-First Findings (substrate already present)

Everything the mirror needs already exists; this is an additive task with one small new
predicate.

- **Axiom-predicate pattern**: `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`
  already houses 8 fragment predicates (`ImpAxiom`, `ConjImpAxiom`, `ConjImpBotAxiom`,
  `ConjImpBotMinAxiom`, `ClassicalImpAxiom`, `ClassicalConjImpAxiom`,
  `ClassicalConjImpBotAxiom`) with an identical 5-part structure per fragment. OrImp is the
  9th, slotting in beside `ConjImpAxiom`.
- **Or constructors exist in `MinPropAxiom`**: `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`
  `MinPropAxiom` has `orI1 : φ → φ∨ψ`, `orI2 : ψ → φ∨ψ`,
  `orE : (φ→χ) → ((ψ→χ) → ((φ∨ψ)→χ))` (lines 143–149). The subsumption
  `OrImpAxiom.toMinPropAxiom` is a direct 5-case `cases … exact .ctor` mirror of
  `ConjImpAxiom.toMinPropAxiom` (FragmentAxioms.lean:102–109).
- **Or notation typeclasses exist**: `Cslib/Foundations/Logic/ProofSystem.lean` already
  defines `HasAxiomOrI1`/`HasAxiomOrI2`/`HasAxiomOrE` (lines 154–162). No new notation/axiom
  typeclasses are needed — reuse these for the `HilbertOrImp` instances.
- **Bundled class**: `MinimalHilbert` (ProofSystem.lean:341–346) extends only
  `ModusPonens + HasAxiomImplyK + HasAxiomImplyS`. OrImp has K and S, so it gets a
  `MinimalHilbert` instance for free (exactly like `HilbertConjImp`/`HilbertImp` in
  `ProofSystem/Instances.lean:79–82, 111–113`). **No new bundled class is required.**
- **Deduction theorem**: `hasDeductionTheorem` (consumed in FragmentAxioms.lean:235–242,
  392–394, etc.) needs only `mem_implyK`/`mem_implyS` witnesses, which OrImp supplies.
- **Strength substrate (task 345)**:
  `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` provides `MinimalAxioms`
  (8-field class), `IsMinimal`, the bridge `minimalAxioms_iff_forall_minPropAxiom` (★),
  `isMinimalIff`, `minimalAxioms_iff_subset`. **Coherence note**: OrImp deliberately does
  **not** get a `MinimalAxioms` (nor `ConjImpAxioms`) instance — it lacks andI/andE1/andE2,
  so it is strictly weaker than MPL. The strength story stays coherent through the
  axiom-level subsumption `OrImpAxiom → MinPropAxiom` (the same way `ImpAxiom`/`ConjImpAxiom`
  situate themselves below MPL). No new bridging into the 345 substrate is required; the
  subsumption lemma is the entire connection.

## 3. One genuinely new piece: the `IsAndBotFree` predicate

The fragment-predicate-compatibility lemmas need a syntactic predicate naming the fragment
the OrImp axioms live in. Existing predicates in
`Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` are `IsOrFree`,
`IsOrBotFree`, `IsImpTopOnly` (and `IsBotFree` in `Conservative.lean`). **None permits `or`
while forbidding `and`**, which is what IPL⟨∨,→,⊤⟩ requires. So one new predicate is needed:

```
def Proposition.IsAndBotFree : Proposition Atom → Bool
  | .atom _ => true
  | .bot    => false
  | .imp a b => a.IsAndBotFree && b.IsAndBotFree
  | .and _ _ => false
  | .or a b  => a.IsAndBotFree && b.IsAndBotFree
```

(Note: `⊤ := .imp .bot .bot` is a derived abbrev — `IsImpTopOnly` likewise marks `bot` as
`false`. The fragment axioms K/S/orI1/orI2/orE never literally contain `⊥` or `⊤`, so the
compatibility lemmas only ever feed `imp`/`or` nodes — the predicate is correct for them.)

Accompanying mechanical lemmas to add (mirroring `imp_isOrFree`/`subst_preserves_isOrFree`):
- `imp_isAndBotFree`, `or_isAndBotFree` (connective closure),
- `subst_preserves_isAndBotFree`,
- optional subsumption `IsImpTopOnly_implies_IsAndBotFree` (imp-top-only ⊆ and-bot-free),
- **optional, conservativity-only**: `coe_AlgEvaluate_andBotFree` (the independence lemma:
  for and-bot-free formulas `AlgEvaluate` depends only on `⊔`, `⇨`, `⊤` — a direct dual of
  `coe_AlgEvaluate_orFree`, FragmentPredicates.lean:230–248). Cheap to add even if the full
  conservativity theorem is deferred.

## 4. Exact mirror map (core deliverable, sorry-free)

All in `Cslib.Logic.PL` namespace unless noted. Model each item on the cited
`ConjImpAxiom` line numbers in `FragmentAxioms.lean`.

| Item | Model (FragmentAxioms.lean) | Notes |
|------|------------------------------|-------|
| `inductive OrImpAxiom` (implyK, implyS, orI1, orI2, orE) | `ConjImpAxiom` 59–74 | orI1/orI2/orE shapes from `MinPropAxiom` (Axioms.lean 143–149) |
| `ImpAxiom.toOrImpAxiom` | `ImpAxiom.toConjImpAxiom` 95–99 | optional but natural (ImpAxiom ⊆ OrImpAxiom) |
| `OrImpAxiom.toMinPropAxiom` | `ConjImpAxiom.toMinPropAxiom` 102–109 | required subsumption |
| `OrImpAxiom.mem_implyK` / `mem_implyS` | 116–125 | for deduction theorem |
| `subst_preserves_orImpAxiom` | 148–158 | add `orI1/orI2/orE` subst cases |
| compatibility lemmas `orImpAxiom_{implyK,implyS,orI1,orI2,orE}_isAndBotFree` | 175–212 | use `imp_isAndBotFree`/`or_isAndBotFree` |
| `orImpAxiom_hasDeductionTheorem` | 235–237 | `hasDeductionTheorem mem_implyK mem_implyS` |

`Cslib/Logics/Propositional/ProofSystem/Instances.lean` (new `section OrImpInstances`,
model on `HilbertConjImp` 38–83):
- `InferenceSystem Propositional.HilbertOrImp (PL.Proposition Atom)` via
  `DerivationTree OrImpAxiom [] φ`
- `ModusPonens`
- `HasAxiomImplyK`, `HasAxiomImplyS` (`.ax [] _ (.implyK _ _)`, etc.)
- `HasAxiomOrI1`, `HasAxiomOrI2`, `HasAxiomOrE` (`.ax [] _ (.orI1 _ _)`, etc.)
- `MinimalHilbert Propositional.HilbertOrImp`

`Cslib/Foundations/Logic/ProofSystem.lean`: add
`opaque Propositional.HilbertOrImp : Type := Empty` beside `HilbertImp` (line 503).

**Import wiring already in place**: `Cslib.lean` already imports `FragmentAxioms` (439),
`FragmentInstances` (440), `FragmentPredicates` (453). The new predicate lands in the
already-imported `FragmentPredicates.lean`; new instances land in the already-imported
`Instances.lean` (verify whether OrImp instances belong in `Instances.lean` or
`FragmentInstances.lean` — the existing ConjImp/Imp fragment instances live in
`ProofSystem/Instances.lean`; place OrImp there for consistency, and confirm that module is
imported by `Cslib.lean`).

## 5. Conservativity step — assessment: optional, heavy, recommend deferral/confirmation

The analogous `ConjImpConservative.lean` proves "IPL conservative over IPL⟨∧,→,⊤⟩ for
or-bot-free formulas" by eliminating `⊔` via the **LowerSet free-join completion**
(`FreeJoinCompletion.lean`) + `conjImp_brouwerian_complete`. For the *disjunctive* fragment
the dual problem is to eliminate `⊓` (conjunction) while **preserving `⊔` and `⇨`**, i.e. a
**free *meet* completion**. Findings:

- Only `FreeJoinCompletion.lean` exists; there is **no free-meet-completion** in the codebase.
- A free meet completion interacts non-trivially with the Heyting implication `⇨`, so it is
  not a symmetric copy-paste of the join case — it is real new algebraic infrastructure.
- The `coe_AlgEvaluate_andBotFree` independence lemma (§3) is cheap and worth landing as
  groundwork, but the end-to-end `hilbertIplConservativeOverOrImp` theorem is a substantial
  separate effort.

**Recommendation**: ship §3–§4 as the sorry-free core (and optionally the independence
lemma). Mark the full conservativity theorem as a stretch goal requiring explicit user
confirmation before investment; if confirmed, scope it as its own phase/task that builds a
free-meet completion. Do **not** introduce a sorry or axiom to bridge conservativity.

## 6. Zero-debt / lint compliance notes

- Pure additive mirror; no sorry, no new `axiom`. All constructors/lemmas get docstrings
  (docBlame) as in every existing fragment block.
- Prop-valued items are `theorem`/`lemma` (defLemma); names are lowerCamelCase
  (e.g. `orImpAxiom_hasDeductionTheorem`, `subst_preserves_orImpAxiom`) with no underscores
  in the camelCase stems (the existing files use `subst_preserves_*` snake segments — match
  the surrounding file's established convention exactly).
- Instances wrapped in `namespace Cslib.Logic.PL` (topNamespace); tag type under
  `Propositional.` namespace as siblings.
- CI gates: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`. No new test is strictly required (no fragment tests exist in
  `CslibTests/Propositional.lean` today), but a smoke `#check`/instance-resolution line is a
  cheap safeguard.

## 7. Suggested phase plan for the planner

1. **Phase 1 — predicate**: add `IsAndBotFree` + closure/subst lemmas (+ optional
   `IsImpTopOnly_implies_IsAndBotFree`) to `FragmentPredicates.lean`.
2. **Phase 2 — axioms**: add `OrImpAxiom`, subsumptions (`ImpAxiom.toOrImpAxiom`,
   `OrImpAxiom.toMinPropAxiom`), witnesses, `subst_preserves_orImpAxiom`, compatibility
   lemmas, `orImpAxiom_hasDeductionTheorem` to `FragmentAxioms.lean`.
3. **Phase 3 — tag + instances**: add `Propositional.HilbertOrImp` opaque tag and the
   `InferenceSystem`/`ModusPonens`/`HasAxiom*`/`MinimalHilbert` instances.
4. **Phase 4 — CI green**: run the full gate set.
5. **Phase 5 (optional, gated on confirmation)** — `coe_AlgEvaluate_andBotFree` groundwork
   and, only if approved, the full free-meet-completion conservativity theorem.

## 8. Key files

- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (mirror target)
- `Cslib/Logics/Propositional/ProofSystem/Instances.lean` (tag instances)
- `Cslib/Logics/Propositional/ProofSystem/FragmentInstances.lean` (confirm placement)
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` (new predicate)
- `Cslib/Foundations/Logic/ProofSystem.lean` (tag type, HasAxiomOr* + MinimalHilbert)
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` (or-constructor shapes)
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (345 strength substrate)
- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` (conservativity model)
- `Cslib.lean` (import aggregator — fragment modules already imported)
