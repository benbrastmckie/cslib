# MPL Base Structure-First Design Note

**Task**: 407 — MPL base structure first redesign (Waves 1–4)
**Status**: Implemented (Phases 1–9 complete)
**Date**: 2026-06-29

## Design Decision: Design A Adopted

**Design A** (this implementation): `⊥` is a **primitive nullary connective** in the fixed
signature `{⊥, →, ∧, ∨}`. MPL is the base derivation relation with no ⊥-rule. The meaning
of `⊥` is determined by **property modules** (typeclasses), not syntax.

**Design B** (not implemented, documented here for reference): Two variants were considered
but rejected:
- B1: A fragment language without `⊥` for MPL, extending the language to add `⊥` for IPL.
- B2: Encoding `⊥` as a distinguished atom `⊥ : Atom`.

Both violate **substitution-invariance**: the type `Proposition Atom` is the free monad on
`{⊥, →, ∧, ∨}`, so `⊥` is an element of this algebra, not an external constant. Any
renaming of atoms that sends `p₀ ↦ ⊥` must commute with derivability. B1 would require a
language extension; B2 treats `⊥` as syntactically distinguishable from atoms while in the
same type, breaking the free-algebra structure.

The canonical justification is the **free-algebra argument** (Zulip #604219492, Benjamin
Brast-McKie): `Proposition Atom` is the free monad on `{⊥, →, ∧, ∨}`, so `⊥` belongs to
the algebra as an element, not as meta-syntax. This is also the only choice compatible with
the shared `Proposition` type and the single-substitution-monad architecture supporting MPL,
IPL, CPL, Modal, Temporal, and Bimodal logics.

See the in-source design note at `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
(lines 51–114) for the full technical argument and references.

## Property Hierarchy (Wave 1–2 deliverables)

### Proof-theoretic property hierarchy (NaturalDeduction/Basic.lean)

- **MPL** (minimal propositional logic, [Johansson1937]): base derivation with 10 ungated
  primitive rules; `efq` is **gated off** via `[IsIntuitionistic T]` instance. The
  gate-free fragment is named:
  - `MinimalDerivation T Γ A := (AxiomTheory MinPropAxiom).Derivation Γ A` (abbreviation,
    zero proof churn).
  - `IsBotRuleFree d : Prop := True` (additive predicate on derivations; `efq` constructors
    are simply unavailable at MPL strength; the predicate records this for documentation).
- **IPL** (intuitionistic propositional logic): `[IsIntuitionistic T]` holds; the explosion
  module `efq : ⊥ → A` is available. IPL = MPL + explosion.
- **CPL** (classical propositional logic): adds double negation elimination. CPL = IPL + classicality.

### Semantic bottom-property hierarchy (Semantics/Algebra/BotProperties.lean)

Mirror of the proof-theoretic hierarchy at the algebraic level:

1. **Designated bottom** (`bot_val : H` free parameter): `GHAValid` (MPL semantics). No
   semantic constraint on `⊥`.
2. **Least bottom** (`HasLeastBot bot_val`): `bot_val ≤ a` for all `a`. Algebraic correlate
   of `IsIntuitionistic`. Proved: `HasLeastBot bot_val → ∀ A, AlgEvaluate v bot_val (⊥→A) = ⊤`.
3. **Canonical bottom** (`bot_val = ⊥` from `OrderBot`): `HAValid` and `BAValid` (IPL/CPL
   algebraic completeness). Used by Heyting and Boolean algebras.

The `HasLeastBot` class is a **thin Prop-mixin** on a specific element, not a typeclass on
the algebra type. This avoids duplicating `IsIntuitionistic` at the semantic level.

### Brouwerian evaluator wiring (Semantics/Algebra/BrouwerianBot.lean)

- `BrouwerianBot`: `GeneralizedHeytingAlgebra` with free `bot_val` (no leastness constraint).
  Models **MPL algebraic semantics**.
- `PointedBrouwerian`: `GeneralizedHeytingAlgebra` with `HasLeastBot bot_val`. Models **IPL
  algebraic semantics** (explosion-sound evaluator).
- Bridge: `PointedBrouwerian.hasLeastBot_himp` wires leastness to the IPL completeness chain;
  `PointedBrouwerianCompleteness.lean` proves `IPL Hilbert ↔ HAValid` via this bridge.

## Generic Lindenbaum Substrate (Wave 3, Phases 5–6)

**File**: `Metalogic/GenericLindenbaum.lean`

A single **explosion-parameterized Lindenbaum substrate** (`GenericDCCS`, `GenericLindenbaumAlg`,
`GenericLindenbaum`) that is instantiated twice:

- `MinLindenbaum`: the MPL Lindenbaum algebra (no explosion instance; `GenericDCCS` with
  `IsExplosionFree` constraint).
- `IntLindenbaum`: the IPL Lindenbaum algebra (`GenericDCCS` with `IsIntuitionistic`).

**Reduction**: The duplication in `MinLindenbaum.lean` and `IntLindenbaum.lean` (deductive
closure, MCS construction, Lindenbaum algebra fields) is now derived from the generic substrate
via instantiation. Both `Min*/Int*` completeness proofs (`MinStrongCompleteness`,
`IntStrongCompleteness`) route through the generic substrate and remain sorry-free.

## Fragment-Genericity Spike (Wave 4 spike, Phase 7, S3)

**File**: `Semantics/Algebra/FragmentGeneric.lean`

**Mechanism delivered** (research-or-defer gate: DEFERRED, follow-on task spawned):

- `AlgEvalIndependent P`: abstract evaluation-independence property for formula predicates.
- `isBotFree_eval_independent`: `IsBotFree` satisfies `AlgEvalIndependent`.
- `isOrBotFree_eval_independent`: `IsOrBotFree` satisfies `AlgEvalIndependent`.
- `generic_gha_implies_ha`: for any P with `AlgEvalIndependent`, `GHAValid φ → HAValid φ`
  (generic, always holds).
- `ghaValid_of_botFree`: for bot-free `φ`, `HAValid φ → GHAValid φ` (converse via `WithBot`
  embedding).
- `ghaValid_iff_haValid_of_botFree`: the `GHAValid ↔ HAValid` equivalence for bot-free
  formulas as one worked generic conservativity corollary.

**Residual (open research, task 410)**:

The remaining step — `HAValid φ → Derivable X-logic φ` for a specific sub-logic `X` —
requires **per-fragment algebraic completeness**, which is not currently generic in `P`:
- `IsBotFree`: routes through `WithBot G` + Heyting completeness.
- `IsOrBotFree`: routes through `LowerSet B` + Brouwerian completeness.
- `IsImpTopOnly`: routes through the Rasiowa free algebra.

A fully generic `Derivable P-logic φ ← HAValid φ` parameterized by `P` is **open research**.
Task 410 is spawned to research and formalize the per-fragment algebraic completeness needed
to instantiate this generic framework.

**No sorry introduced**: The fragment-genericity spike is additive; `Conservative.lean`,
`BrouwerianCompleteness.lean`, and `MplConservativeChain.lean` are not modified.

## Tableau Unification (Wave 4, Phase 8)

**File**: `Tableau/Intuitionistic/Expansion.lean` (modified); `Tableau/Intuitionistic/Scheme.lean`
(closure-predicate parameterization; Phase 8 delivers the `IntMinScheme` unified interface).

**Deliverable**: A single `intExpandBranches`/`propExpandBranches` expansion loop
parameterized by `closurePred : IBranch Atom → Bool`:
- `intuitionisticTableau`: `closurePred = isIntuitionisticallyClosed`.
- `minimalTableau`: `closurePred = isMinimallyClosed`.

There is no duplicate expansion function. The `IntMinScheme` structure in `Scheme.lean`
bundles both divergence points (closure predicate + countermodel `botForces`) into a single
parameterized interface.

## CI Verification (Phase 9)

- `lake build`: PASS (3151 jobs, zero errors)
- `lake exe checkInitImports`: PASS (no output = all imports OK)
- `lake lint`: PASS for task-407 files (pre-existing lint errors in unmodified files:
  `Rules.lean`, `Saturation.lean`, `Subformula.lean`, `DeductionTheorem.lean`,
  `Termination.lean`, `Soundness.lean`, `DenseMCS.lean`, `GenericMCSBridge.lean`)
- `lake exe lint-style`: PASS (no output)
- `lake shake --add-public --keep-implied --keep-prefix`: pre-existing findings in
  unmodified files (SequentCalculus, Temporal); no findings in task-407 files
- `lake exe mk_all --module`: pre-existing `IntFMPSpike` stub issue (task 385); all
  task-407 new files are properly listed in `Cslib.lean`
- `lake test`: PASS (9142/9142 jobs)
- Sorries: 0 new (4 pre-existing in Intuitionistic/Scheme.lean + Completeness.lean; many
  in Bimodal/BXCanonical tracked by tasks 36/37)
- New axioms: 0

## References

- [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
- [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
- [A. S. Troelstra, D. van Dalen, *Constructivism in Mathematics*][TroelstraVanDalen1988]
- [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
- [M. H. B. Sørensen, P. Urzyczyn, *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006]
- [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
- CSLib Zulip thread on Propositional Logic, msg #604219492 (substitution-invariance argument)

## Zulip Note

No Zulip post was authored by AI for this task. The design note is internal only.
The Zulip thread reference (#604219492, Benjamin Brast-McKie's substitution-invariance
argument) is documented-only; no AI-authored public post was made.
