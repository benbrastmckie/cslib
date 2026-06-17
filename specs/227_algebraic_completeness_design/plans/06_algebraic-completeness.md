# Implementation Plan: Task #227

- **Task**: 227 - algebraic_completeness_design
- **Status**: [COMPLETED]
- **Effort**: 10 hours
- **Dependencies**: None (Task 226 GHA semantics refactor is upstream context, not a blocker)
- **Research Inputs**: reports/05_hard-implementation-research.md, reports/01_algebraic-completeness-design.md, reports/06_completeness-statement-alternatives.md
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

Key findings from report 06 (completeness statement alternatives):
- The explicit `(v, bot_val)` completeness statement is confirmed as the correct design
- Five alternatives evaluated (bundled AlgInterp, Option Atom, Atom ⊕ Unit, Johansson typeclass, AAL); all dismissed or demoted to optional sugar
- JohanssonAlgebra typeclass has a fatal diamond problem: typeclass resolution picks one `designated` per type, but MPL needs all choices while IPL needs `designated = ⊥`
- CSLib's `HAValid`/`BAValid` are strictly cleaner than Thomas's IPL/CPL statements (0 extra hypotheses vs his `v ⊥ = ⊥`)
- The `bot_val` quantifier is only visible in the general theorem and `GHAValid`; IPL/CPL specializations are already optimal
- The `v ⊨ T` parametric completeness architecture (via `AlgTValid`) is orthogonal to the Proposition type design and should be adopted

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
- JohanssonAlgebra typeclass (dismissed: diamond problem — typeclass resolution forces one `designated` per type, blocking MPL/IPL joint quantification; see report 06)
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
| IPL/CPL specialization from general completeness has bot_val mismatch | L | L | Confirmed non-issue (report 06): `HAValid`/`BAValid` hardcode `bot_val = ⊥`, eliminating the parameter entirely. Direct proof via Lindenbaum HA/BA instance |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 5 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

### Phase 1: Congruence Lemmas and Lindenbaum Algebra [COMPLETED]

**Goal**: Prove the three missing congruence lemmas and build the Lindenbaum quotient with PartialOrder, Lattice, GHA, HA, and BA instances.

**Tasks**:
- [x] Prove `Theory.Equiv.imp_congr`: if `A equiv A'` and `B equiv B'` then `(A -> B) equiv (A' -> B')` *(Basic.lean:402)*
- [x] Prove `Theory.Equiv.and_congr`: congruence for conjunction *(Basic.lean:426)*
- [x] Prove `Theory.Equiv.or_congr`: congruence for disjunction *(Basic.lean:445)*
- [x] Define order via `lindenbaumLe` using `Quotient.liftOn₂` with well-definedness by cut *(Lindenbaum.lean:64, subsumed into GHA instance at :275)*
- [x] Prove `lindenbaumLe_mk` / `lindenbaumMk_le_mk` simp lemma *(Lindenbaum.lean:81, :297)*
- [x] Define `lindenbaumSup` / `lindenbaumInf` via `Quotient.lift₂` with congruence lemmas *(Lindenbaum.lean:88, :94)*
- [x] Prove `lindenbaumSup_mk`, `lindenbaumInf_mk`, `lindenbaumMk_sup`, `lindenbaumMk_inf` simp lemmas *(Lindenbaum.lean:106-311)*
- [x] Define `GeneralizedHeytingAlgebra` instance with `top := lindenbaumMk T (.imp .bot .bot)` and standalone axiom lemmas *(Lindenbaum.lean:275)*
- [x] Prove `lindenbaumLe_himp_iff` (deduction theorem in quotient form) *(Lindenbaum.lean:208)*
- [x] Prove `lindenbaumHimp_mk` / `lindenbaumMk_himp` simp lemma and `lindenbaumTop` *(Lindenbaum.lean:114, :315, :320)*
- [x] Define `HeytingAlgebra` instance with `bot := lindenbaumMk T .bot`, `compl x := x ⇨ ⊥`, `himp_bot _ := rfl` *(Lindenbaum.lean:340)*
- [x] Define `BooleanAlgebra` instance via `BooleanAlgebra.ofRegular` + `lindenbaumEM` + `lindenbaumRegular` *(Lindenbaum.lean:403)*
- [x] Prove `nontrivialOfConsistent`: consistent T gives nontrivial quotient *(Lindenbaum.lean:410)*

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

### Phase 2: Completeness Theorems [COMPLETED] *(Completeness.lean:236 lines, sorry-free)*

**Goal**: Prove algebraic completeness for all three tiers using the Lindenbaum algebra from Phase 1.

**Design rationale** (report 06): The completeness statement uses explicit `(v, bot_val)` quantification, adopting Thomas's `v ⊨ T` parametric style via `AlgTValid`. The `bot_val` quantifier is the correct cost of primitive `⊥` — it is only visible in the general theorem and `GHAValid`. The IPL/CPL specializations hardcode `bot_val = ⊥` into `HAValid`/`BAValid`, eliminating the parameter entirely (0 extra hypotheses, strictly cleaner than Thomas's `v ⊥ = ⊥` condition). Five alternatives were evaluated and dismissed; see report 06 for details.

**Exact statement forms**:
```
-- General (parametric in T, adopts v ⊨ T pattern):
Theory.alg_complete :
  DerivableIn T A ↔
    ∀ {H} [GHA H] (v : Atom → H) (bot_val : H),
      AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤

-- MPL (T = ∅, AlgTValid vacuous, bot_val free):
MPL.alg_complete :
  DerivableIn ∅ A ↔
    ∀ {H} [GHA H] (v : Atom → H) (bot_val : H),
      AlgEvaluate v bot_val A = ⊤

-- IPL (bot_val = ⊥, no extra hypothesis):
IPL.alg_complete :
  DerivableIn IPL A ↔
    ∀ {H} [HA H] (v : Atom → H), AlgEvaluate v ⊥ A = ⊤

-- CPL (bot_val = ⊥, no extra hypothesis):
CPL.alg_complete :
  DerivableIn CPL A ↔
    ∀ {H} [BA H] (v : Atom → H), AlgEvaluate v ⊥ A = ⊤
```

**Tasks**:
- [x] Add `AlgTValid` definition to `Algebra.lean` *(Algebra.lean:120)*
- [x] Define `Theory.canonicalV` and `Theory.canonicalBotVal` *(Completeness.lean:42, :45)*
- [x] Prove `Theory.canonicalBotVal_eq`: bot_val = ⊥ for intuitionistic theories *(Completeness.lean:48)*
- [x] Prove truth lemma `Theory.canonicalV_spec` by induction on A (5 cases) *(Completeness.lean:54)*
- [x] Prove `Theory.tValid_canonicalV`: canonical valuation models T *(Completeness.lean:68)*
- [x] Prove `lindenbaumMk_eq_top_iff`: `lindenbaumMk T A = ⊤ ↔ DerivableIn T A` *(Completeness.lean:164)*
- [x] Prove ND-level soundness `nd_alg_sound_aux` by structural induction — meet formulation handles `orE` via distributivity *(Completeness.lean:78, ~70 lines, covers all 10 constructors)*
- [x] Prove `nd_alg_sound`: consequence-form wrapper *(Completeness.lean:150)*
- [x] Prove `Theory.alg_complete`: general completeness over GHA (Type u) *(Completeness.lean:179)*
- [x] Prove `MPL.alg_complete`: T = ∅, AlgTValid vacuous *(Completeness.lean:194)*
- [x] Prove `IPL.alg_complete`: uses HeytingAlgebra, bot_val = ⊥ *(Completeness.lean:205)*
- [x] Prove `alg_complete_classical`: classical completeness for `[IsIntuitionistic T] [IsClassical T]` *(Completeness.lean:222)* — NOTE: named `alg_complete_classical` rather than `CPL.alg_complete` since CSLib's `CPL` only contains DNE axioms without efq; quantifies over `BooleanAlgebra`

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

### Phase 3: Conservative Extension Infrastructure and Validity Lemmas [COMPLETED] *(Conservative.lean:100 lines, 1 expected sorry)*

**Goal**: Build the bot-free analysis infrastructure, prove validity subsumption lemmas, and state the conservative extension theorem (with sorry for the D-M-dependent direction).

**Tasks**:
- [x] Define `Proposition.IsBotFree : Proposition Atom -> Bool` (recursive) *(Conservative.lean:38)*
- [x] Prove `AlgEvaluate_botFree_independent`: bot_val independence for bot-free formulas *(Conservative.lean:48)*
- [x] Prove `GHAValid_implies_HAValid`: validity subsumption GHA → HA *(Conservative.lean:69)*
- [x] Prove `HAValid_implies_BAValid`: validity subsumption HA → BA *(Conservative.lean:77)*
- [x] State `ipl_conservative_over_mpl` with sorry + D-M docstring *(Conservative.lean:96)*

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

### Phase 4: Docstrings, BibKeys, CI Verification [COMPLETED]

**Goal**: Update documentation, fix references.bib, register new files, and pass full CI.

**Tasks**:
- [x] Update `Algebra.lean` module docstring with Johansson algebra lineage, bot_val rationale, AlgTValid unification story, Rasiowa/RasiowaSikorski references *(Algebra.lean:23-53)*
- [x] `AlgTValid` already has adequate doc comment *(Algebra.lean:115-119)*
- [x] Fix 3 merge conflict regions in `references.bib` (kept upstream, discarded empty stash)
- [x] Add all 6 BibKeys: Rasiowa1974, RasiowaSikorski1963, BlokPigozzi1989, Font2016, MacNeille1937, TroelstraSchwichtenberg2000
- [x] Run `lake exe mk_all --module` — Cslib.lean updated with new modules
- [x] Run `lake exe checkInitImports` — passes
- [x] Run `lake exe lint-style` — passes
- [x] Run `lake build` — full project builds (3004 jobs, only expected Conservative.lean sorry warning)
- [x] Run `lake test` — GrindLint failure is pre-existing (not caused by our changes)
- [x] Hilbert corollaries deferred — requires ND↔Hilbert bridge; documented as future work in Completeness.lean docstring

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

### Phase 5: Algebra.lean Docstring Update (Independent) [COMPLETED] *(subsumed by Phase 4)*

**Goal**: Independently update the `Algebra.lean` module docstring to reference Johansson algebras before the main implementation work, providing algebraic context.

NOTE: Subsumed by Phase 4 which executed sequentially and included all docstring updates.

**Tasks**:
- [x] Add reference to Johansson algebras in `Algebra.lean` module docstring *(done in Phase 4, Algebra.lean:23-27)*
- [x] Add Rasiowa 1974 citation to module docstring references section *(done in Phase 4)*
- [x] Add design note: `bot_val` is the Johansson designated constant; `AlgTValid` adopts Thomas Waring's `v ⊨ T` style *(done in Phase 4, Algebra.lean:43-53)*

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - Docstring updates only (~10 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra` compiles
- Docstring references Johansson algebras and Rasiowa 1974

## Testing & Validation

- [x] All new files compile without errors via `lake build` (3004 jobs)
- [x] Zero sorries in Lindenbaum.lean and Completeness.lean; one expected sorry in Conservative.lean (D-M-dependent)
- [x] `lake exe checkInitImports` passes
- [x] `lake exe lint-style` passes
- [x] `lake test` — GrindLint failure is pre-existing, not caused by our changes
- [x] `lake build` (full project) shows no regressions
- [ ] Verify `Theory.alg_complete` via `lean_verify` for axiom check (deferred to final verification)
- [x] Tier specializations: `IPL.alg_complete` uses `HeytingAlgebra` with `bot_val = ⊥`; `MPL.alg_complete` uses `GHA` with free `bot_val`; `alg_complete_classical` uses `BooleanAlgebra` (named differently from plan due to CPL = DNE only)

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
