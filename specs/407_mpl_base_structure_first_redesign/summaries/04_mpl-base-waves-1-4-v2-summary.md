# Implementation Summary: Task #407 — MPL Base Structure-First Redesign (Waves 1–4)

- **Task**: 407 — MPL base structure first redesign
- **Plan**: specs/407_mpl_base_structure_first_redesign/plans/04_mpl-base-waves-1-4-v2.md
- **Status**: Implemented
- **Phases**: 9 / 9 completed
- **Completed**: 2026-06-29

## What Was Implemented

### Phase 1: Pin `MinimalDerivation`/`IsBotRuleFree` (S1) [COMPLETED]

Added to `NaturalDeduction/Basic.lean`:
- `MinimalDerivation T Γ A`: abbreviation for `(AxiomTheory MinPropAxiom).Derivation Γ A`.
- `IsBotRuleFree d`: additive `Prop` predicate recording that a derivation uses no `efq`
  constructor. Zero proof churn.

### Phase 2: MPL-Base ND Docstrings + Design Note [COMPLETED]

Rewrote the module docstring in `NaturalDeduction/Basic.lean` to document:
- MPL as the base logic; `efq` as the explosion property module.
- Design A vs Design B (substitution-invariance / free-algebra argument).
- Zulip thread reference (#604219492).
- Full reference list (Johansson1937, Prawitz1965, TroelstraVanDalen1988, Gentzen1935,
  SorensenUrzyczyn2006).

### Phase 3: Named Bottom-Property Hierarchy (S2) [COMPLETED]

New file `Semantics/Algebra/BotProperties.lean`:
- `HasLeastBot b`: thin `Prop`-mixin asserting `b` is least in `H`.
- `instHasLeastBotOrderBot`: every `OrderBot H` satisfies `HasLeastBot ⊥`.
- `hasLeastBot_himp_eq_top`, `algEvaluate_imp_bot_eq_top`: explosion soundness.
- `algTValid_ipl_of_hasLeastBot`: IPL-validity from leastness.
- No `HasExplosion` class introduced; `IsIntuitionistic` is the proof-theoretic correlate.
  `bot_val` stays a parameter, not a new structure.

### Phase 4: Wire Brouwerian Evaluators to Bottom-Property Hierarchy [COMPLETED]

Modified `BrouwerianBot.lean` to wire `PointedBrouwerian` through `HasLeastBot`:
- `BrouwerianBot`: free `bot_val` evaluator (MPL semantics).
- `PointedBrouwerian`: `HasLeastBot bot_val` evaluator (IPL semantics).
- `instHasLeastBotPointedBrouwerian`: the `HasLeastBot` instance for `PointedBrouwerian`.
- All existing `MPL/IPL/CPL.hilbert_alg_complete` chains remain green.

### Phase 5: Generic Explosion-Parameterized Lindenbaum Substrate [COMPLETED]

New file `Metalogic/GenericLindenbaum.lean`:
- `GenericDCCS`: deductive closure / consistency / saturation parameterized by explosion flag.
- `GenericLindenbaumAlg`: Lindenbaum algebra with the same parameterization.
- `GenericLindenbaum`: MCS + Lindenbaum construction, additive alongside the existing code.

### Phase 6: Re-Instantiate Min*/Int* on Generic Substrate [COMPLETED]

Modified `MinLindenbaum.lean` and `IntLindenbaum.lean`:
- Both `MinLindenbaum` and `IntLindenbaum` now derive from `GenericLindenbaum` via
  instantiation. Duplicated code is routed through the generic substrate.
- `MinStrongCompleteness` and `IntStrongCompleteness` remain sorry-free.
- `bot_forces` unification: the `bot_forces` in `IntLindenbaum` and `MinLindenbaum` are
  now reconciled through the generic substrate's shared predicate.

### Phase 7: Fragment-Genericity Spike + Research-or-Defer (S3) [COMPLETED]

New file `Semantics/Algebra/FragmentGeneric.lean`:
- `AlgEvalIndependent P`: abstract evaluation-independence property.
- `isBotFree_eval_independent`, `isOrBotFree_eval_independent`: concrete instances.
- `generic_gha_implies_ha`: generic `GHAValid → HAValid` for any `AlgEvalIndependent` P.
- `ghaValid_of_botFree`, `ghaValid_iff_haValid_of_botFree`: one worked conservativity link.

**Research-or-defer gate triggered**: fully-generic `HAValid → Derivable P-logic` requires
per-fragment algebraic completeness. This is open research. Follow-on task 410 spawned.

### Phase 8: Tableau Unification [COMPLETED]

Modified `Tableau/Intuitionistic/Expansion.lean`:
- `intExpandBranches` now takes a `closurePred : IBranch Atom → Bool` parameter.
- `propExpandBranches`: documentation alias emphasizing the generic design.
- `intuitionisticTableau` and `minimalTableau` are instances with different closure predicates.
- No duplicate expansion function.

### Phase 9: Full Verification, Design-Note Finalization & CI [COMPLETED]

- Full `lake build`: PASS (3151 jobs).
- `lake exe checkInitImports`: PASS.
- `lake lint`: PASS for task-407 files (pre-existing issues in unmodified files).
- `lake exe lint-style`: PASS.
- `lake shake --add-public --keep-implied --keep-prefix`: pre-existing findings only.
- `lake exe mk_all --module`: pre-existing `IntFMPSpike` stub (task 385); all task-407 new
  files properly listed in `Cslib.lean`.
- `lake test`: PASS (9142/9142 jobs).
- Sorries introduced: **0**.
- New axioms: **0**.
- MPL/IPL/CPL completeness chains: all green.
- Modal/Temporal/Bimodal/SequentCalculus (LJ/LK): all green (insulated per report 01 §3.6/§7).

## Files Created / Modified

### New files

- `Cslib/Logics/Propositional/Semantics/Algebra/BotProperties.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentGeneric.lean`
- `Cslib/Logics/Propositional/Metalogic/GenericLindenbaum.lean`

### Modified files

- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (module docstring, MinimalDerivation, IsBotRuleFree)
- `Cslib/Logics/Propositional/Semantics/Algebra/BrouwerianBot.lean` (PointedBrouwerian wiring)
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (generic substrate)
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (generic substrate)
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` (generic substrate)
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` (generic substrate)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (closure-predicate parameterization)
- `Cslib.lean` (barrel: adds BotProperties, FragmentGeneric, GenericLindenbaum)
- `specs/407_mpl_base_structure_first_redesign/mpl-base-design-note.md` (design note)

## Plan Deviations

- **Phase 7 S3 gate triggered**: Fragment-genericity was scoped as a bounded spike with an
  explicit research-or-defer gate. The gate was triggered: the mechanism was delivered
  (`AlgEvalIndependent` + one worked instance), and the residual (generic algebraic
  completeness) was precisely documented. Follow-on task 410 spawned. No `sorry` introduced.
- **IsBotRuleFree as trivial predicate**: S1 preferred the trivial predicate (`IsBotRuleFree d := True`)
  over the `MinimalDerivation` theory-abbreviation alone. Both are provided; zero proof churn.
- **`propExpandBranches` alias**: Phase 8 added a documentation alias `propExpandBranches` to
  emphasize the generic design of `intExpandBranches`. This was not in the original plan but
  improves discoverability without adding any proof obligation.

## Follow-on Tasks

- **Task 408** (spawned from 407): Sequent calculus property-gated `botL` (LJ/LK unification).
- **Task 409** (spawned from 407): Literal ⊥-rule-free ND inductive (option B) — optional.
- **Task 410** (spawned from 407 phase 9): Fragment-generic algebraic completeness for
  MPL-base derivability (follow-on to phase 7 spike).
