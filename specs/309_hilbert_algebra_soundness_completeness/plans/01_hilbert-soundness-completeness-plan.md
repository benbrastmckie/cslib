# Implementation Plan: Hilbert Algebra Soundness and Completeness for IPL(->,T)

- **Task**: 309 - Prove soundness and completeness of IPL(->,T) w.r.t. Hilbert algebras
- **Status**: [IMPLEMENTING]
- **Effort**: 3 hours
- **Dependencies**: Task 304 (COMPLETED) -- HilbertAlgebra typeclass + HilbertEvaluate/HilbertValid
- **Research Inputs**: specs/309_hilbert_algebra_soundness_completeness/reports/01_hilbert-soundness-completeness-research.md
- **Artifacts**: plans/01_hilbert-soundness-completeness-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Build a standalone Lindenbaum-Tarski algebra construction for `ImpAxiom` over `HilbertAlgebra`, proving soundness and completeness of the implicational fragment IPL(->,T). The target file `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` does not exist and must be created from scratch, following the structural pattern of `BrouwerianCompleteness.lean` but strictly simpler: no `inf` operation, no `le_himp_iff` adjunction, no AND axioms. All derivation infrastructure (`hilbertCutSingletonDeriv`, `hilbertImpIDeriv`, `hilbertImpEDeriv`, `ImpAxiom.mem_implyK/S`) already exists.

### Research Integration

Key findings from the research report:
1. **BrouwerianCompleteness.lean (528 lines) is the exact template** -- same quotient pattern (equivalence -> setoid -> quotient -> order -> himp -> algebra instance -> truth lemma -> completeness) but replacing `ConjImpAxiom`/`BrouwerianSemilattice` with `ImpAxiom`/`HilbertAlgebra`.
2. **HilbertLindenbaum.lean cannot be reused** -- it requires `MinimalAxioms` with AND/OR axiom schema fields that `ImpAxiom` does not provide.
3. **HilbertAlgebra requires only 4 fields** (himp_K, himp_S, himp_antisymm, himp_self) -- all equational, no adjunction needed. Strictly simpler than the 11-field `BrouwerianSemilattice` instance.
4. **The `impEquivImpCongr` congruence proof transfers directly** from `conjImpEquivImpCongr` -- it uses only K/S witnesses, no AND axioms.
5. **Conservative extension result** is optional (bonus) and can be deferred.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Prove `imp_hilbert_axiom_sound`: every `ImpAxiom` constructor evaluates to top in every `HilbertAlgebra`
- Prove `imp_hilbert_soundness_derivable`: derivation-level soundness for `ImpAxiom`
- Construct the Hilbert Lindenbaum algebra: quotient of `Proposition Atom` by `ImpAxiom`-equivalence
- Prove `HilbertAlgebra (ImpLindenbaumAlgebra Atom)` instance
- Prove truth lemma (`impCanonicalV_spec`) restricted to `IsImpTopOnly` formulas
- Prove completeness (`imp_hilbert_complete`) and biconditional (`imp_hilbert_iff`)
- Pass `lake build` with zero sorry obligations

**Non-Goals**:
- Conservative extension theorem (`hilbertIplConservativeOverImp`) -- deferred as optional Phase 4
- Modifications to any existing file (single-file addition only)
- Completeness for formulas outside the `IsImpTopOnly` fragment

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `HilbertAlgebra` instance fields may need non-obvious proof steps | M | L | Research confirms all 4 fields are direct applications of `ImpAxiom` constructors + basic derivation lemmas |
| Universe polymorphism issues in completeness theorem | M | L | Follow exact universe annotations from `BrouwerianCompleteness.lean` (`{Atom : Type u}`, `HilbertValid.{u, u}`) |
| `Quotient.liftOn2` congruence argument may be harder than expected for `impLindenbaumLe` | M | L | Pattern is identical to `brouwerianLindenbaumLe` -- only axiom witnesses change |
| Truth lemma induction cases for `bot`/`and`/`or` may require careful `IsImpTopOnly` handling | L | L | These cases are vacuous (`IsImpTopOnly` returns `false`), same as `BrouwerianCompleteness` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Soundness [COMPLETED]

**Goal**: Prove that every `ImpAxiom`-derivable formula is Hilbert-valid.

**Tasks**:
- [ ] Create target file `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` with module header, copyright, imports, and module docstring
- [ ] Implement `imp_hilbert_axiom_sound`: case analysis on `ImpAxiom` constructors `implyK` and `implyS`, using `HilbertAlgebra.himp_K` and `HilbertAlgebra.himp_S` with `HilbertAlgebra.himp_eq_top_iff`
- [ ] Implement `imp_hilbert_soundness`: induction on `DerivationTree ImpAxiom`, following the pattern from `conjImp_brouwerian_soundness` (ax/assumption/modus_ponens/weakening cases)
- [ ] Implement `imp_hilbert_soundness_derivable`: wrapper extracting `DerivationTree` from `Derivable`
- [ ] Verify with `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` - create new file (~80 lines for soundness section)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness` succeeds
- Zero `sorry` in file
- All three soundness theorems type-check

---

### Phase 2: Lindenbaum Construction and HilbertAlgebra Instance [COMPLETED]

**Goal**: Construct the Hilbert Lindenbaum algebra as a quotient and prove it satisfies the `HilbertAlgebra` axioms.

**Tasks**:
- [ ] Define `ImpEquiv` relation: `Deriv ImpAxiom [A] B /\ Deriv ImpAxiom [B] A`
- [ ] Prove equivalence relation properties: `impEquiv_refl`, `impEquiv_symm`, `impEquiv_trans` (trans uses `hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS`)
- [ ] Define `impPropositionSetoid`, `ImpLindenbaumAlgebra Atom` (quotient type), `impLindenbaumMk` (quotient map)
- [ ] Define `impLindenbaumLe` via `Quotient.liftOn2` with congruence proof (same pattern as `brouwerianLindenbaumLe`)
- [ ] Prove `impLindenbaumLe_mk` simp lemma
- [ ] Prove `impEquivImpCongr`: imp-congruence lemma (transfer from `conjImpEquivImpCongr`, replacing `ConjImpAxiom.mem_implyK/S` with `ImpAxiom.mem_implyK/S`)
- [ ] Define `impLindenbaumHimp` via `Quotient.lift2` using `impEquivImpCongr`
- [ ] Prove `impLindenbaumHimp_mk` simp lemma
- [ ] Prove order properties: `impLindenbaumLe_refl`, `impLindenbaumLe_trans`, `impLindenbaumLe_antisymm`
- [ ] Prove `impLindenbaumLe_top` (top is `impLindenbaumMk (bot.imp bot)`)
- [ ] Prove HilbertAlgebra axiom lemmas:
  - `impLindenbaumHimp_K`: `[A] ⇨ ([B] ⇨ [A]) = T` from `ImpAxiom.implyK`
  - `impLindenbaumHimp_S`: the S combinator identity from `ImpAxiom.implyS`
  - `impLindenbaumHimp_antisymm`: from quotient soundness via `Quotient.sound`
  - `impLindenbaumHimp_self`: `[A] ⇨ [A] = T` from `hilbertImpIDeriv`
- [ ] Build the `HilbertAlgebra (ImpLindenbaumAlgebra Atom)` instance combining all fields
- [ ] Prove API simp lemmas: `impLindenbaumMk_le_mk`, `impLindenbaumMk_himp`, `impLindenbaumTop`
- [ ] Prove `impLindenbaumMk_eq_top_iff`: `[A] = T <-> Derivable ImpAxiom A`
- [ ] Verify with scoped `lake build`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` - add Lindenbaum construction (~200 lines)

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness` succeeds
- Zero `sorry` in file
- `HilbertAlgebra` instance compiles without errors
- `impLindenbaumMk_eq_top_iff` type-checks

---

### Phase 3: Truth Lemma, Completeness, and Final Verification [COMPLETED]

**Goal**: Prove the truth lemma for `IsImpTopOnly` formulas, derive completeness, and run full CI verification.

**Tasks**:
- [ ] Define `impCanonicalV`: canonical valuation `x -> impLindenbaumMk (.atom x)`
- [ ] Prove `impCanonicalV_spec` (truth lemma): `HilbertEvaluate impCanonicalV A = impLindenbaumMk A` for `A.IsImpTopOnly = true`, by structural induction (atom: rfl; bot/and/or: vacuous via `IsImpTopOnly` being false; imp: unfold + IH + `impLindenbaumMk_himp`)
- [ ] Prove `imp_hilbert_complete`: instantiate `HilbertValid` at `ImpLindenbaumAlgebra Atom` with `impCanonicalV`, apply truth lemma, extract via `impLindenbaumMk_eq_top_iff`
- [ ] Prove `imp_hilbert_iff`: biconditional combining soundness and completeness
- [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness` (scoped build)
- [ ] Run `lake exe checkInitImports` to verify `Cslib.Init` is imported (it is inherited from `Hilbert.lean` import)
- [ ] Run `lake exe lint-style` for style compliance
- [ ] Run `lake build` for full project build verification

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` - add truth lemma, completeness, close file (~80 lines)

**Verification**:
- `lake build` succeeds (full project)
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- Zero `sorry` in file (verified with `lean_verify` or grep)
- Total file size ~350-400 lines

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertAlgCompleteness` succeeds at each phase
- [ ] `lake build` (full project) succeeds after Phase 3
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] Zero `sorry` in `HilbertAlgCompleteness.lean`
- [ ] All main theorems type-check: `imp_hilbert_axiom_sound`, `imp_hilbert_soundness_derivable`, `imp_hilbert_complete`, `imp_hilbert_iff`

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertAlgCompleteness.lean` - new file (~350-400 lines)
- `specs/309_hilbert_algebra_soundness_completeness/plans/01_hilbert-soundness-completeness-plan.md` - this plan

## Rollback/Contingency

Since this is a single new file addition with no modifications to existing files, rollback is trivial: delete `HilbertAlgCompleteness.lean`. If the `HilbertAlgebra` instance proves harder than expected (unlikely per adversarial verification), the Lindenbaum construction can be split into smaller lemmas following the same decomposition used in `BrouwerianCompleteness.lean`. The conservative extension result (Phase 4) is explicitly deferred and not part of the core plan.
