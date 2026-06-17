# Implementation Plan: Task #227

- **Task**: 227 - algebraic_completeness_design
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: None (Task 226 GHA semantics refactor is upstream context, not a blocker)
- **Research Inputs**: reports/05_hard-implementation-research.md, reports/01_algebraic-completeness-design.md
- **Artifacts**: plans/06_algebraic-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Build algebraic completeness for propositional logic in three tiers (MPL/IPL/CPL) by
constructing the Lindenbaum quotient algebra and proving the truth lemma. The core insight
from research report 05 is that Dedekind-MacNeille completion is NOT needed for the main
completeness theorems: stating completeness over GeneralizedHeytingAlgebra (rather than
HeytingAlgebra) allows the Lindenbaum quotient to serve directly. CSLib's primitive `.bot`
constructor eliminates all `[Bot Atom]` and `[Inhabited Atom]` requirements present in
Thomas Waring's original code. Three new files are created (~585 lines total) plus ~35 lines
of additions to existing files. The conservative extension theorem is deferred to a follow-up
task because it requires Dedekind-MacNeille completion.

### Research Integration

Key findings from report 05 (hard-mode implementation research):
- Thomas's `Theory.complete` quantifies over GHA directly; Lindenbaum quotient IS a GHA, so no D-M needed
- Three congruence lemmas (`Theory.Equiv.imp_congr`, `and_congr`, `or_congr`) are MISSING from CSLib and must be proved for `Quotient.lift2` well-definedness
- `BooleanAlgebra.ofRegular` from Mathlib (`Heyting._root_.BooleanAlgebra.ofRegular`) promotes HA to BA given regularity (DNE)
- CSLib's `top = .bot -> .bot` needs no `[Inhabited Atom]`; `bot := quotient_mk .bot` needs no `[Bot Atom]`
- ND-level soundness must be proved (existing soundness is Hilbert-level only)
- Hilbert corollaries require bridging `AxiomTheory MinPropAxiom` to `MPL` -- may be complex; defer if needed
- Conservative extension needs D-M completion -- deferred to separate task

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances propositional algebraic completeness infrastructure. While not explicitly listed in ROADMAP.md (which focuses on Bimodal/Temporal porting), this provides foundational algebraic completeness results that complement the existing Kripke completeness proofs at `Logics/Propositional/Metalogic/` and could support future algebraic approaches in Modal/Temporal metalogic.

## Goals & Non-Goals

**Goals**:
- Prove congruence lemmas for `Theory.Equiv` (imp, and, or)
- Build Lindenbaum quotient algebra with PartialOrder, Lattice, GHA, HA, and BA instances
- Define `AlgTValid` predicate and canonical valuation
- Prove the truth lemma (`canonicalV_spec`) with the `.bot` case
- Prove ND-level algebraic soundness
- Prove general algebraic completeness (`Theory.alg_complete`) over GHA
- Prove tier-specific completeness: MPL/GHA, IPL/HA, CPL/BA
- Define `IsBotFree` predicate and prove `AlgEvaluate_botFree_independent`
- Prove validity subsumption lemmas (GHAValid -> HAValid -> BAValid)
- Update Algebra.lean docstrings to reference Johansson algebras
- Add missing BibKeys to references.bib

**Non-Goals**:
- Dedekind-MacNeille completion (deferred to separate task)
- Conservative extension theorem `ipl_conservative_over_mpl` (depends on D-M)
- JohanssonAlgebra typeclass (deferred; current bot_val parameter suffices)
- Hilbert-level completeness corollaries (defer if AxiomTheory bridging is complex)
- Modifications to Kripke completeness proofs

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `le_himp_iff` proof (deduction theorem in quotient) is complex | M | M | CSLib already has `impI` and `cut`; pattern proven in BimodalLogic codebase |
| `Quotient.lift2` well-definedness proofs are verbose | M | M | Congruence lemmas break this into modular pieces; each ~5 lines |
| ND-level soundness induction on Derivation tree is tedious | M | L | Each case is 2-5 lines using known GHA lemmas from existing Hilbert soundness |
| AxiomTheory bridging for Hilbert corollaries is harder than expected | L | M | Defer Hilbert corollaries entirely to a follow-up if bridging exceeds 30 min |
| `le_sup_inf` (distributivity) not automatically available in GHA | L | L | GHA extends DistribLattice in Mathlib; should be inherited |
| references.bib has unresolved merge conflict markers | L | H | Fix conflicts manually before adding new BibKeys |
| IPL/CPL specialization from general completeness has bot_val mismatch | M | M | Use direct proof via Lindenbaum HA/BA instance instead of going through general theorem |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 5 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

### Phase 1: Congruence Lemmas and Lindenbaum Algebra [NOT STARTED]

**Goal**: Prove the three missing congruence lemmas and build the Lindenbaum quotient with PartialOrder, Lattice, GHA, HA, and BA instances.

**Tasks**:
- [ ] Prove `Theory.Equiv.imp_congr`: if `A equiv A'` and `B equiv B'` then `(A -> B) equiv (A' -> B')` -- use `impI`, `impE`, cut
- [ ] Prove `Theory.Equiv.and_congr`: congruence for conjunction -- use `andI`, `andE1`, `andE2`
- [ ] Prove `Theory.Equiv.or_congr`: congruence for disjunction -- use `orI1`, `orI2`, `orE`
- [ ] Define `PartialOrder` on `Quotient T.propositionSetoid` where `le` uses `Quotient.lift2` with `DerivableIn T ({A} |- B)`
- [ ] Prove `mk_le_mk` simp lemma: `quotient_mk A <= quotient_mk B <-> DerivableIn T ({A} |- B)`
- [ ] Define `Lattice` instance with `sup := Quotient.lift2 (fun A B => quotient_mk (A or B))` and `inf` for conjunction, using congruence lemmas for well-definedness
- [ ] Prove `mk_sup_mk` and `mk_inf_mk` simp lemmas
- [ ] Define `GeneralizedHeytingAlgebra` instance with `top := quotient_mk top` and `himp := Quotient.lift2 (fun A B => quotient_mk (A -> B))`
- [ ] Prove `le_himp_iff` (deduction theorem in quotient form): `a inf b <= c <-> a <= b himp c`
- [ ] Prove `mk_himp_mk` simp lemma and `top_eq` lemma
- [ ] Define `HeytingAlgebra` instance (conditional on `[IsIntuitionistic T]`) with `bot := quotient_mk .bot` and `bot_le` via `botE`
- [ ] Define `BooleanAlgebra` instance (conditional on `[IsClassical T]`) via `BooleanAlgebra.ofRegular` + DNE
- [ ] Prove `nontrivial_of_consistent`: if T does not derive bot, then the quotient is nontrivial

**Timing**: 3.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Add 3 congruence lemmas (~30 lines) after the existing `equiv` section
- `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` - NEW FILE (~300 lines): all Lindenbaum algebra instances

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Lindenbaum` compiles without errors or sorries
- All 5 algebra instances typecheck: PartialOrder, Lattice, GHA, HA (with IsIntuitionistic), BA (with IsClassical)
- Simp lemmas `mk_le_mk`, `mk_sup_mk`, `mk_inf_mk`, `mk_himp_mk` are present

---

### Phase 2: Completeness Theorems [NOT STARTED]

**Goal**: Prove algebraic completeness for all three tiers using the Lindenbaum algebra from Phase 1.

**Tasks**:
- [ ] Add `AlgTValid` definition to `Algebra.lean` (~5 lines): `forall B in T, AlgEvaluate v bot_val B = top`
- [ ] Define `Theory.canonicalV`: canonical valuation `fun x => quotient_mk (.atom x)`
- [ ] Prove truth lemma `Theory.canonicalV_spec`: `AlgEvaluate T.canonicalV (quotient_mk .bot) A = quotient_mk A` by induction on A (5 cases including `.bot`)
- [ ] Prove `Theory.lindenbaum_complete`: `quotient_mk A = top <-> DerivableIn T A` using `derivable_iff_equiv_top`
- [ ] Prove `Theory.tValid_canonicalV`: canonical valuation models T
- [ ] Prove ND-level soundness `nd_sound_aux` by structural induction on `Theory.Derivation` (~40 lines, each constructor case 2-5 lines)
- [ ] Prove `nd_alg_sound`: wrapper from `DerivableIn T (empty |- A)` to `AlgEvaluate v bot_val A = top`
- [ ] Prove `Theory.alg_complete`: general completeness `DerivableIn T A <-> forall GHA H, v, bot_val, AlgTValid T v bot_val -> AlgEvaluate v bot_val A = top`
- [ ] Prove `MPL.alg_complete`: `DerivableIn MPL A <-> GHAValid A` (MPL = empty, so AlgTValid is vacuous)
- [ ] Prove `IPL.alg_complete`: `DerivableIn IPL A <-> HAValid A` -- direct proof using Lindenbaum HA instance
- [ ] Prove `CPL.alg_complete`: `DerivableIn CPL A <-> BAValid A` -- direct proof using Lindenbaum BA instance

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - Add `AlgTValid` definition (~5 lines)
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` - NEW FILE (~200 lines): all completeness proofs

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Completeness` compiles without errors or sorries
- `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`, `CPL.alg_complete` all typecheck
- ND soundness `nd_alg_sound` covers all 10 Derivation constructors

---

### Phase 3: Conservative Extension Infrastructure and Validity Lemmas [NOT STARTED]

**Goal**: Build the bot-free analysis infrastructure, prove validity subsumption lemmas, and state the conservative extension theorem (with sorry for the D-M-dependent direction).

**Tasks**:
- [ ] Define `Proposition.IsBotFree : Proposition Atom -> Bool` (recursive, decidable)
- [ ] Prove `AlgEvaluate_botFree_independent`: for bot-free formulas, evaluation is independent of `bot_val`
- [ ] Prove `GHAValid_implies_HAValid`: if valid in all GHAs then valid in all HAs (instantiate `bot_val := bot`)
- [ ] Prove `HAValid_implies_BAValid`: if valid in all HAs then valid in all BAs (BA extends HA)
- [ ] State `ipl_conservative_over_mpl` with sorry: `IsBotFree A -> DerivableIn IPL A -> DerivableIn MPL A` -- leave sorry with doc comment explaining D-M dependency

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - NEW FILE (~80 lines): IsBotFree, botFree independence, validity subsumption, conservative extension (sorry)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Conservative` compiles (one expected sorry for conservative extension)
- `IsBotFree` computes correctly on sample propositions
- `AlgEvaluate_botFree_independent` typechecks
- `GHAValid_implies_HAValid` and `HAValid_implies_BAValid` are sorry-free

---

### Phase 4: Docstrings, BibKeys, CI Verification [NOT STARTED]

**Goal**: Update documentation, fix references.bib, register new files, and pass full CI.

**Tasks**:
- [ ] Update `Algebra.lean` module docstring to reference Johansson algebras, Rasiowa 1974, and the algebraic lineage (GHA = Johansson, HA = Heyting, BA = Boolean)
- [ ] Add `@[inherit_doc]` or doc comments to `AlgTValid`
- [ ] Fix merge conflict markers in `references.bib` (around Fitting1969/Heyting1930/Herbrand1930/Trufas2024 region)
- [ ] Add missing BibKeys to `references.bib`: Rasiowa1974, RasiowaSikorski1963, BlokPigozzi1989, Font2016, MacNeille1937, TroelstraSchwichtenberg2000
- [ ] Run `lake exe mk_all --module` to register new files in `Cslib.lean` barrel import
- [ ] Run `lake exe checkInitImports` to verify all new files import `Cslib.Init`
- [ ] Run `lake exe lint-style` and fix any style issues
- [ ] Run `lake build` (full project) to verify no regressions
- [ ] Run `lake test` to verify test suite passes
- [ ] Attempt Hilbert corollaries (`Hilbert.MPL.alg_complete`, etc.) via bridge theorems -- if AxiomTheory bridging exceeds 30 min, document as future work in Completeness.lean docstring

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - Updated docstrings (~15 lines changed)
- `references.bib` - Fix conflicts + add 6 BibKeys (~20 lines)
- `Cslib.lean` - Auto-updated by `mk_all`
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` - Optionally add Hilbert corollaries (~20 lines) or document as future work

**Verification**:
- `lake build` passes (full project, no regressions)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- `references.bib` has no merge conflict markers
- All new BibKeys are present in `references.bib`

---

### Phase 5: Algebra.lean Docstring Update (Independent) [NOT STARTED]

**Goal**: Independently update the `Algebra.lean` module docstring to reference Johansson algebras before the main implementation work, providing algebraic context.

NOTE: This phase can execute in parallel with Phase 1 since it only modifies the docstring/comment portion of `Algebra.lean`, which Phase 1 does not touch. However, given Phase 4 also touches `Algebra.lean` docstrings, this phase is subsumed by Phase 4 if executed sequentially. If running in parallel, Phase 4 should skip the docstring update.

**Tasks**:
- [ ] Add reference to Johansson algebras in `Algebra.lean` module docstring: explain that GHA + designated bot constant = Johansson algebra
- [ ] Add Rasiowa 1974 citation to module docstring references section
- [ ] Add design note explaining bot_val = Johansson algebra designated constant

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - Docstring updates only (~10 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra` compiles
- Docstring references Johansson algebras and Rasiowa 1974

## Testing & Validation

- [ ] All three new files compile without errors via `lake build`
- [ ] Zero sorries in Lindenbaum.lean and Completeness.lean (one expected sorry in Conservative.lean for D-M-dependent conservative extension)
- [ ] `lake exe checkInitImports` passes for all new files
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `lake build` (full project) shows no regressions in existing Modal/Temporal/Bimodal code
- [ ] Verify `Theory.alg_complete` via `lean_verify` for axiom check (no Prop or Classical.choice in proof term)
- [ ] Verify `MPL.alg_complete`, `IPL.alg_complete`, `CPL.alg_complete` type signatures match research report 05

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` - NEW (~300 lines): Lindenbaum quotient algebra with all instances
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` - NEW (~200 lines): Truth lemma, ND soundness, completeness theorems
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` - NEW (~80 lines): IsBotFree, bot-free independence, validity subsumption
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - MODIFIED: 3 congruence lemmas (~30 lines added)
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - MODIFIED: AlgTValid definition + docstring updates (~20 lines)
- `references.bib` - MODIFIED: Fix merge conflicts + 6 new BibKeys
- `Cslib.lean` - AUTO-UPDATED by `mk_all`

## Rollback/Contingency

If implementation fails or introduces regressions:
1. `git stash` or `git checkout -- .` to revert all changes
2. New files (Lindenbaum.lean, Completeness.lean, Conservative.lean) can be deleted without affecting existing code
3. The 3 congruence lemmas added to Basic.lean are backward-compatible additions
4. The `AlgTValid` addition to Algebra.lean is purely additive
5. If the conservative extension sorry is problematic for CI, remove Conservative.lean entirely -- it has no downstream dependents
6. If Hilbert corollaries are complex, omit them and document in Completeness.lean docstring as future work
