# Implementation Plan: Fragment Syntactic Predicates and Independence Lemmas

- **Task**: 302 - Fragment Syntactic Predicates and Independence Lemmas
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None (IsBotFree and AlgEvaluate already exist in Conservative.lean and Algebra.lean)
- **Research Inputs**: specs/302_fragment_syntactic_predicates/reports/01_fragment-predicates-research.md
- **Artifacts**: plans/01_fragment-predicates-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Define three syntactic fragment predicates (IsOrFree, IsOrBotFree, IsImpTopOnly) on `Proposition Atom` following the established `IsBotFree` Bool-valued recursive pattern from Conservative.lean. Prove AlgEvaluate independence lemmas using a two-GHA-instance formulation showing evaluation is independent of unused operations. Prove subsumption hierarchy and closure properties (connective and substitution preservation). All definitions and proofs go in a single new file `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean`, estimated at 150-200 lines.

### Research Integration

The research report (01_fragment-predicates-research.md) confirmed:
- The IsBotFree pattern from Conservative.lean is the right template for all three predicates
- The two-GHA-instance formulation is the cleanest approach for independence lemmas, avoiding parameterized evaluators
- Proof strategy: structural induction with `simp` decomposition and `congr`/rewrite with instance-equality hypotheses
- Subsumption: `IsImpTopOnly => IsOrBotFree <=> IsOrFree /\ IsBotFree`
- Substitution closure follows by induction with the `hf` hypothesis at atoms
- Estimated 150-200 lines, no blockers

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation needed for this task.

## Goals & Non-Goals

**Goals**:
- Define `Proposition.IsOrFree`, `Proposition.IsOrBotFree`, `Proposition.IsImpTopOnly` as Bool-valued recursive predicates
- Prove subsumption hierarchy lemmas relating the four predicates (including existing IsBotFree)
- Prove connective closure lemmas for each predicate
- Prove substitution closure theorems for each predicate
- Prove AlgEvaluate independence lemmas using two-GHA-instance formulation
- Register file in barrel import via `lake exe mk_all --module`

**Non-Goals**:
- Fragment-specific evaluators (e.g., AlgEvaluateOrFree) -- not needed; two-instance formulation suffices
- Embedding lemmas for specific constructions (WithBot, downsets) -- those belong to downstream tasks 307, 311
- Proof system definitions (ConjImpAxiom, ImpAxiom) -- those belong to task 305

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Two-instance @-notation makes independence proofs verbose | M | M | Use `congr` and function extensionality; research report shows proof sketch is ~15 lines per lemma |
| Instance equality hypotheses awkward to state | L | L | Follow exact pattern from research report; use `@Inf.inf H inst.toInf` etc. |
| Typeclass resolution interference with @-notation | M | L | Use `simp only` with explicit lemma names; avoid implicit instance resolution in proofs |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Full Implementation [COMPLETED]

**Goal**: Create `FragmentPredicates.lean` with all predicate definitions, subsumption hierarchy, closure properties, and independence lemmas. Run CI verification.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean`
- [ ] Add module header, copyright, imports (`Cslib.Logics.Propositional.Semantics.Algebra.Conservative`)
- [ ] Define `Proposition.IsOrFree` (Bool-valued, recursive: atom=>true, bot=>true, imp/and=>recurse, or=>false)
- [ ] Define `Proposition.IsOrBotFree` (Bool-valued: atom=>true, bot=>false, imp/and=>recurse, or=>false)
- [ ] Define `Proposition.IsImpTopOnly` (Bool-valued: atom=>true, bot=>false, imp=>recurse, and/or=>false)
- [ ] Prove subsumption: `IsImpTopOnly_implies_IsOrBotFree`, `IsOrBotFree_implies_IsOrFree`, `IsOrBotFree_implies_IsBotFree`, `IsOrBotFree_iff` (iff IsOrFree and IsBotFree)
- [ ] Prove connective closure: `imp_isOrFree`, `and_isOrFree`, `imp_isOrBotFree`, `and_isOrBotFree`, `imp_isImpTopOnly`
- [ ] Prove substitution closure: `subst_preserves_isOrFree`, `subst_preserves_isOrBotFree`, `subst_preserves_isImpTopOnly`
- [ ] Prove `AlgEvaluate_orFree_independent_of_sup` (two-instance: agree on inf, himp, top => equal on or-free formulas)
- [ ] Prove `AlgEvaluate_orBotFree_independent` (two-instance: agree on inf, himp, top, plus different bot_val => equal on or-bot-free)
- [ ] Prove `AlgEvaluate_impTopOnly_independent` (two-instance: agree on himp, top, plus different bot_val => equal on imp-top-only)
- [ ] Run `lake exe mk_all --module` to update barrel import
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates`
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style`

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` - new file, all definitions and proofs (~150-200 lines)
- `Cslib.lean` - barrel import update (automated via `lake exe mk_all --module`)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lean_verify` confirms no `sorry` in any theorem

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates` compiles without errors
- [ ] `lake exe checkInitImports` passes (file imports Cslib.Init transitively via Conservative.lean)
- [ ] `lake exe lint-style` passes
- [ ] All three predicate definitions match the Bool-valued recursive pattern of IsBotFree
- [ ] All independence lemmas are sorry-free (verified via `lean_verify`)
- [ ] Subsumption hierarchy is complete: IsImpTopOnly => IsOrBotFree => IsOrFree, IsOrBotFree => IsBotFree

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` - main implementation file
- `specs/302_fragment_syntactic_predicates/plans/01_fragment-predicates-plan.md` - this plan
- `specs/302_fragment_syntactic_predicates/summaries/01_fragment-predicates-summary.md` - execution summary (after implementation)

## Rollback/Contingency

Delete `Cslib/Logics/Propositional/Semantics/Algebra/FragmentPredicates.lean` and re-run `lake exe mk_all --module` to remove the barrel import entry. No other files are modified.

If the two-instance independence formulation proves too unwieldy in practice, the implementation agent may pivot to simpler per-construction embedding lemmas (e.g., proving independence for the specific `WithBot` or downset constructions used downstream). This would narrow the generality but still serve tasks 305-311.
