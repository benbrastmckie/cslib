# Reuse-Consolidation Survey: Lindenbaum / MCS / Conservativity Constructions

## Scope

Survey the duplicated Lindenbaum-algebra, MCS-extension, generic-MCS-bridge, and
morphism-lift constructions across the CSLib logic families (Propositional, Modal,
Temporal, Bimodal) and determine, per cluster, whether consolidation onto the shared
`Cslib.Foundations.Logic.Metalogic` machinery is (a) already done, (b) a clean
retirement, (c) a feasible partial generalization, or (d) a larger separate refactor.

## Shared Foundations machinery (the reuse target)

The reuse-first target already exists and is mature:

| Foundations module | Provides |
|---|---|
| `Foundations/Logic/Metalogic/Consistency.lean` | `set_lindenbaum` (generic Lindenbaum's lemma via Zorn), `SetConsistent`, `SetMaximalConsistent`, `HasDeductionTheorem` |
| `Foundations/Logic/Metalogic/GenericMCS.lean` | `algebraicDerivationSystem` seam, `algebraic_has_deduction_theorem`, `unfoldListImp` |
| `Foundations/Logic/Metalogic/MCSProperties.lean` | `mcs_bot_not_mem`, `mcs_mp_axiom`, `mcs_theorem_in_mcs`, ... (proved once for any `MinimalHilbert`) |
| `Foundations/Logic/Metalogic/ProofSystemMorphism.lean` | `ProofSig`, `ProofSigHom`, `Metalogic.Deriv`, functorial `Deriv.map` (the generic lift) |

There is **no** generic Lindenbaum–Tarski *quotient-algebra* abstraction in Foundations
(confirmed by grep); that is the one genuine gap (Cluster D below).

## Findings by cluster

### Cluster A — Per-family `*_lindenbaum` MCS lemmas: ALREADY consolidated (no action)

The MCS-extension lemmas named in the task are already **one-line delegations** to the
Foundations generic:

- `modal_lindenbaum` (`Modal/Metalogic/MCS.lean:59`) → `Metalogic.set_lindenbaum (modalDerivationSystem Axioms) hS`
- `prop_lindenbaum` (`Propositional/Metalogic/MCS.lean:60`) → `Metalogic.set_lindenbaum (propDerivationSystem Axioms) hS`
- `temporal_lindenbaum` (`Temporal/Metalogic/MCS.lean:67`) → `Metalogic.set_lindenbaum temporalDerivationSystem hS`
- `bimodal_lindenbaum` (`Bimodal/Metalogic/Core/MaximalConsistent.lean:92`) → `Metalogic.set_lindenbaum bimodalDerivationSystem hΩ`

The sibling `*_closed_under_derivation`, `*_implication_property`, `*_negation_complete`
in the same files likewise delegate to `Metalogic.SetMaximalConsistent.*`.
`lindenbaumMCS` / `lindenbaumMCSSet` (`Bimodal/Metalogic/Bundle/Construction.lean:57,73`)
package `Classical.choose (set_lindenbaum_base …)` behind named noncomputable defs +
spec lemmas.

**These are naming/signature adapters, not proof duplication.** They fix the
`DerivationSystem` argument and give family-local names used across each metalogic.
Recommendation: **keep as-is.** Retiring them forces every call site to inline
`set_lindenbaum <family>DerivationSystem`, churning many files for negative readability
with zero proof-debt reduction. Document this rationale so the cluster is not re-flagged.

Exception: `restricted_lindenbaum` (`Bimodal/Metalogic/Core/RestrictedMCS.lean:303`) is a
**genuine variant** — a Zorn argument over *closure-restricted* consistent supersets, not
reducible to `set_lindenbaum` (different superset collection). Optional future work:
generalize `set_lindenbaum` over the superset-family predicate so both the plain and
restricted versions instantiate one Zorn scaffold. Lower priority; not required.

### Cluster B — `LiftViaMorphism.lean` x3: RETIRE (highest-value, lowest-risk)

Files:
- `Modal/Metalogic/InterSystem/LiftViaMorphism.lean` (221 lines)
- `Propositional/Semantics/Algebra/LiftViaMorphism.lean` (203 lines)
- `Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean` (183 lines)

These are **demonstration-only overlays** that re-derive each family's existing lift
combinator (`liftDerivation` / `liftDerivationTree` / `DerivationTree.lift`) as a corollary
of the generic `Metalogic.Deriv.map`. Each file states in its own header "This module does
NOT modify … `liftDerivation` … is unchanged" — i.e. the family combinators keep their
original independent definitions; these overlays add a parallel proof but replace nothing.

Evidence of zero downstream value:
- **No importers.** Reverse-dependency grep for all three modules returns nothing; they are
  reached only by the `Cslib.lean` root aggregator (build coverage) and one doc comment in
  `ConjImpConservative.lean:57`.
- **No external references** to their headline results (`modalEquiv`, `plEquiv`,
  `toDeriv_liftDerivation`, `Derivable_mono_via_morphism`, `bimodalHom`, `toDeriv_lift`, …)
  anywhere outside the three files and `ProofSystemMorphism.lean`.
- The Bimodal overlay additionally documents an **unresolvable obstruction** (`ofDeriv` /
  `bimodalEquiv` blocked by large elimination of `List.Mem : Prop` into `Type u`), so it
  cannot even reach the full equivalence it exists to demonstrate.

Recommendation: **delete all three files and their `public import` lines in `Cslib.lean`
(lines ~250, ~385, ~560)**, and drop the doc mention in `ConjImpConservative.lean:57`. If
the "this lift is an instance of the generic morphism" narrative is worth preserving,
consolidate it into a **single** short example/doc block appended to Foundations
`ProofSystemMorphism.lean` rather than three per-family copies (~607 lines → ~0–40).

Caveat (low risk): confirm none of the three registers a typeclass `instance` consumed
transitively — the reverse-dep and symbol greps indicate they do not, but the implementer
should run a full `lake build` after removing the import lines to confirm.

### Cluster C — `GenericMCSBridge.lean` x4: PARTIAL generalization (medium effort)

Files (all IN use — cannot be deleted): Modal (211), Temporal (299), Propositional (199),
Bimodal/Core (325). Each is imported by that family's `DeductionTheorem.lean` (plus Modal
`CanonicalModel.lean`, Temporal `MCS.lean`).

Structure per file:
1. `HilbertTree …` instance + forward `derivTreeToList` — **irreducibly per-family**
   (structural induction over that family's own `DerivationTree` inductive; 4 arms for PL,
   5 for Modal, more for Temporal/Bimodal with the `_fc` frame-class layer).
2. Backward helper `unfoldListImpInTree` — **already consolidated**: every copy is a
   one-line delegation to `GenericMCS.unfoldListImp` (Temporal/Bimodal add a thin `_fc`
   wrapper that also delegates to it).
3. The tail triple `*_deriv_iff_algebraic` / `*_setConsistent_iff_algebraic` /
   `*_setMaxConsistent_iff_algebraic` — **structurally identical** across families: they
   glue `derivTreeToList` + `listDerivToTree` to the generic consistency/MCS definitions.

Recommendation: hoist the tail triple into a Foundations lemma parameterized over a
supplied `deriv_iff_algebraic` equivalence (plus the two transport maps), so each family
supplies only the forward induction and the `listDerivToTree` direction and receives the
consistency + MCS equivalences for free. This removes ~3 near-identical boilerplate lemmas
× 4 families while leaving the genuinely per-family induction in place. Medium effort,
no proof debt.

### Cluster D — Lindenbaum *algebra* quotient variants: SEPARATE follow-on task (high value, high effort/risk)

Four parallel quotient-algebra constructions, ~2,400 lines total:
- `LindenbaumAlg` — `Bimodal/Metalogic/Algebraic/LindenbaumQuotient.lean:83` (Boolean algebra + interior ops; file 293 lines, plus `BooleanStructure`/`InteriorOperators`/`UltrafilterMCS`)
- `HilbertLindenbaumAlgebra` — `Propositional/Semantics/Algebra/HilbertLindenbaum.lean:149` (Heyting/Boolean; 764 lines)
- `ImpLindenbaumAlgebra` — `Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean:154` (implicational Hilbert algebra; 499 lines)
- `RelLindenbaumAlgebra` — `Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean:146` (Γ-relativized GeneralizedHeyting; 849 lines)

Common skeleton across all four: `Setoid` on formulas by (fragment/relativized)
derivational equivalence → `Quotient` → quotient map → `Quotient.liftOn₂` order from
derivability → algebra instance. Differences: the target algebra (Boolean / Heyting /
Hilbert / GeneralizedHeyting) and the well-definedness proofs (family-specific derivability
lemmas: contraposition, cut, monotonicity).

Recommendation: introduce a Foundations `LindenbaumTarski` generic — parameterized over a
formula type + a preorder-valued derivability relation + congruence witnesses — that yields
the `Quotient`, quotient map, and `PartialOrder` once, with the algebra instances layered
per fragment. This is the largest single duplication source but the highest-risk
(touches four large, actively-used completeness files with divergent algebra targets).
**Recommend scoping this as its own dedicated task**, not bundled with Clusters B/C, to keep
each change zero-debt and independently `lake build`-verifiable.

## Recommended implementation ordering (zero-debt, incremental)

1. **Phase A (Cluster B):** delete the 3 `LiftViaMorphism.lean` files + their `Cslib.lean`
   imports + the `ConjImpConservative.lean` doc mention; optional single Foundations example.
   Fastest win (~607 lines removed), lowest risk. Verify with full `lake build`.
2. **Phase B (Cluster C):** hoist the bridge consistency/MCS-equivalence triple into a
   Foundations lemma; refactor the 4 bridges to consume it.
3. **Defer (Cluster D):** spawn a separate task for the generic Lindenbaum–Tarski quotient.
4. **No action (Cluster A):** document that the per-family `*_lindenbaum` wrappers already
   delegate and are intentionally retained as naming adapters.

## Zero-debt / lint notes

- None of the recommended changes introduce `sorry` or axioms; all are code motion or
  generalization over existing sorry-free proofs.
- New Foundations declarations (Phase B lemma, optional example) require docstrings
  (docBlame), `lemma`/`theorem` for Prop-valued results (defLemma), lowerCamelCase names,
  and explicit namespace wrapping for any instances (topNamespace).
- Deleting the `LiftViaMorphism` files removes their `@[expose] public section` decls; run
  `lake build` to confirm no transitive instance was consumed (reverse-dep grep says none).

## No literature source referenced

The task cites no paper or proof sketch; the Literature Extraction Protocol does not apply.
