# Implementation Plan: Task #352 - CPL Conservative over Classical Implicational Fragment

- **Task**: 352 - Prove CPL is conservative over its classical implicational fragment CPL⟨→,⊤⟩
- **Status**: [NOT STARTED]
- **Effort**: 7 hours
- **Dependencies**: None (additive; coordinate footprint with running task 350)
- **Research Inputs**: specs/352_cpl_conservative_over_classical_implicational_fragment/reports/01_cpl-conservative-classical-implicational.md
- **Artifacts**: plans/01_classical-imp-conservativity.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Extend the propositional conservativity chain to the classical side by proving CPL is
conservative over its purely implicational fragment CPL⟨→,⊤⟩, axiomatized Tarski–Bernays-style
by **K + S + Peirce**. The research phase fixed the route decisively: use **truth-assignment
(bivalent) semantics, NOT algebraic** semantics. No `ImplicationAlgebra`/Tarski-algebra
typeclass is introduced. The entire task reduces to one genuinely new theorem,
`classicalImp_completeness : IsImpTopOnly φ → Tautology φ → Derivable ClassicalImpAxiom φ`,
proved Kalmár-style with the conclusion formula as a falsum-surrogate and Peirce for classical
case-elimination; the conservativity deliverable `cpl_conservative_over_imp` (classical) is then
a two-line composition with the existing `prop_soundness_tautology`. Definition of done: the new
fragment, completeness, and conservativity declarations compile with full CI green and the
existing intuitionistic chain untouched.

### Research Integration

Report 01 is integrated in full. Key load-bearing conclusions honored by this plan:
- Fragment = `ImpAxiom` (K, S) + the existing `PropositionalAxiom.peirce` shape; new
  `ClassicalImpAxiom` inductive in `ProofSystem/FragmentAxioms.lean`. Subsumption chain
  `ImpAxiom ⊆ ClassicalImpAxiom ⊆ PropositionalAxiom`. It is a **separate classical branch**,
  NOT a sub-predicate of `IntPropAxiom` (Peirce is non-intuitionistic).
- Truth-assignment route only. New completeness/conservativity module lives under `Metalogic/`
  (`Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`), overriding the original
  task text's incorrect `Semantics/Algebra/ClassicalImpConservative.lean` placement.
- Reuse (all local): `Tautology`/`Evaluate` (Semantics/Bool.lean), `prop_soundness_tautology`
  (Metalogic/Soundness.lean:89), `prop_completeness` (Metalogic/StrongCompleteness.lean:548),
  `hasDeductionTheorem` + the `ImpAxiom.mem_implyK/mem_implyS` witness pattern, `IsImpTopOnly`.
- Caveat honored: existing Foundations Peirce lemmas assume ⊥/EFQ and are NOT reusable for the
  negation-free Kalmár proof; new pure-implicational derived lemmas are required.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path / roadmap_flag in delegation context). The task itself
advances the propositional conservativity chain to its classical branch.

## Goals & Non-Goals

**Goals**:
- Define `ClassicalImpAxiom` (K, S, Peirce) in `ProofSystem/FragmentAxioms.lean` with full
  plumbing: `ImpAxiom.toClassicalImpAxiom`, `ClassicalImpAxiom.toPropAxiom`,
  `mem_implyK`/`mem_implyS` witnesses, `subst_preserves_classicalImpAxiom`, the
  `classicalImpAxiom_*_isImpTopOnly` lemmas (including the Peirce schema), and
  `classicalImpAxiom_hasDeductionTheorem`.
- Prove the new `classicalImp_completeness` (Tarski–Bernays / Kalmár) in a new `Metalogic/`
  module, together with the easy soundness direction.
- Deliver `cpl_conservative_over_imp` (classical) and the `classicalImpAxiom_iff_chain`
  biconditional; extend `Semantics/Algebra/ConservativeChain.lean` with the classical-branch
  subsumption (`derivableClassicalImpOfDerivableProp`) and doc table edge `CPL⟨→,⊤⟩ ⊂ CPL`.
- Keep CI green: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`; new file registered in the barrel (`lake exe mk_all --module`); existing chain
  preserved.

**Non-Goals**:
- No algebraic route: no `ImplicationAlgebra`/`TarskiAlgebra` typeclass, no Lindenbaum–Tarski
  construction, no Abbott representation embedding, no new Foundations math.
- No `sorry` and no new `axiom`. If the Kalmár proof proves intractable, the honest outcome is a
  `[BLOCKED]` completeness phase for user review (zero-debt fallback).
- No edits outside `Logics/Propositional/{ProofSystem,Metalogic,Semantics/Algebra}` (conflict
  avoidance with running task 350, which edits Foundations/Logic/Metalogic and deduction files).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Kalmár implicational completeness (truth lemma + atom elimination) is fiddly | H | M | Isolated in Phases 3-4; pure-implicational derived lemmas built first (Phase 2); if blocked, mark phase `[BLOCKED]` — no sorry, no axiom (zero-debt) |
| R2: Foundations Peirce lemmas assume ⊥/EFQ, not reusable | M | H (known) | Phase 2 builds fresh negation-free derived lemmas (`⊢ φ→φ`, `imp_trans`, Peirce case lemma); do not import ⊥-based Core/HilbertDerivedRules Peirce lemmas |
| R3: File-footprint conflict with running task 350 | M | L | Footprint strictly additive within Propositional/{ProofSystem,Metalogic,Semantics/Algebra}; FragmentAxioms addition appended after task-353's `ConjImpBotMinAxiom` block (end of file) |
| R4: `decide`/`aesop` shortcut on `Tautology` | M | M | Forbidden: `Tautology` is only decidable for `Fintype Atom`; theorem is for arbitrary `Atom`. Follow Kalmár induction step-by-step per report §6 |
| R5: lint/CI failures (docstrings, naming, imports, barrel, shake) | L | M | All new decls get docstrings; `theorem`/`lemma` for Prop-valued; lowerCamelCase; new module imports `Cslib.Init`; run full CI gate in Phase 5 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
builds incrementally on the previous one's declarations.

---

### Phase 1: Define ClassicalImpAxiom fragment and plumbing [COMPLETED]

**Goal**: Add the `ClassicalImpAxiom` inductive (K, S, Peirce) and all mechanical
subsumption/witness/predicate/deduction-theorem plumbing to `FragmentAxioms.lean`, mirroring the
existing `ImpAxiom` block.

**Tasks**:
- [ ] Read the existing `ImpAxiom` block (FragmentAxioms.lean:84-143, 161-242) and the
  `PropositionalAxiom.peirce` constructor (ProofSystem/Axioms.lean:58-60) + `toPropAxiom`
  pattern (Axioms.lean:168) to match shapes exactly.
- [ ] Append (after the task-353 `ConjImpBotMinAxiom` block, end of file) a new
  `inductive ClassicalImpAxiom : PL.Proposition Atom → Prop` with constructors `implyK`,
  `implyS` (identical schemas to `ImpAxiom`), and `peirce φ ψ : ClassicalImpAxiom (((φ.imp ψ).imp φ).imp φ)`.
- [ ] `theorem ImpAxiom.toClassicalImpAxiom : ImpAxiom φ → ClassicalImpAxiom φ` (maps implyK/implyS).
- [ ] `theorem ClassicalImpAxiom.toPropAxiom : ClassicalImpAxiom φ → PropositionalAxiom φ`
  (implyK → `.implyK`, implyS → `.implyS`, peirce → `.peirce`).
- [ ] `namespace ClassicalImpAxiom`: `mem_implyK`, `mem_implyS` witnesses (mirror ImpAxiom).
- [ ] `theorem subst_preserves_classicalImpAxiom` (mirror `subst_preserves_impAxiom`, add peirce case).
- [ ] `lemma classicalImpAxiom_peirce_isImpTopOnly` plus reuse/restate
  `classicalImpAxiom_implyK_isImpTopOnly` / `classicalImpAxiom_implyS_isImpTopOnly` via
  `imp_isImpTopOnly` (covers Peirce: `((φ→ψ)→φ)→φ` over imp-top-only `φ,ψ` is imp-top-only).
- [ ] `theorem classicalImpAxiom_hasDeductionTheorem :=
  hasDeductionTheorem ClassicalImpAxiom.mem_implyK ClassicalImpAxiom.mem_implyS`.
- [ ] Docstrings on every new declaration; lowerCamelCase; `theorem`/`lemma` for Prop-valued.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — append the ClassicalImpAxiom
  block at end of file (additive; do not touch existing blocks).

**Verification**:
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` succeeds.
- `#check @ClassicalImpAxiom.toPropAxiom` and `#check @classicalImpAxiom_hasDeductionTheorem`
  typecheck (can use `lean_goal`/`lean_diagnostic_messages` while iterating).

---

### Phase 2: New Metalogic module — soundness and pure-implicational derived lemmas [NOT STARTED]

**Goal**: Create `Metalogic/ClassicalImpCompleteness.lean`, prove the easy soundness direction,
and build the negation-free derived Hilbert lemmas the Kalmár proof requires (these cannot reuse
the ⊥/EFQ-based Foundations Peirce lemmas).

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean`; `import Cslib.Init`
  plus FragmentAxioms, Semantics/Bool, Metalogic/Soundness, Metalogic/DeductionTheorem,
  FragmentPredicates. Module docstring.
- [ ] Soundness: `theorem classicalImp_soundness : Derivable ClassicalImpAxiom φ → Tautology φ`
  (mirror `prop_soundness`; route via `ClassicalImpAxiom.toPropAxiom` + `prop_soundness_tautology`,
  or direct induction — pick the shorter).
- [ ] Identity: `⊢ φ → φ` over `ClassicalImpAxiom` (from K, S; standard S K K derivation).
- [ ] Composition/transitivity: `imp_trans`-style `⊢ (φ→ψ) → (ψ→χ) → (φ→χ)` (or hypothetical form
  usable under the deduction theorem).
- [ ] Peirce-driven classical case lemma (report §6 step 2/4): the elimination shape
  `from ⊢ Γ, (p → θ) and ⊢ Γ, (p → θ) → θ derive ⊢ Γ → θ` building blocks
  (`⊢ ((p → θ) → θ) → ... → θ` via Peirce + S).
- [ ] Use `classicalImpAxiom_hasDeductionTheorem` for hypothesis discharge throughout.
- [ ] Register the new module in the barrel: `lake exe mk_all --module Cslib`.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (new).
- Barrel file updated by `mk_all`.

**Verification**:
- Module builds; soundness and each derived lemma are `sorry`-free (`lean_diagnostic_messages`).
- `lake exe checkInitImports` passes for the new module.

---

### Phase 3: Kalmár truth lemma (per-assignment derivability) [NOT STARTED]

**Goal**: Prove the core Kalmár truth lemma by induction on imp-top-only `φ`, relative to a
Boolean assignment `v` and a fixed target `θ` (the goal formula): if `v ⊨ φ` then `⊢ Γᵥ → φ`,
and if `v ⊭ φ` then `⊢ Γᵥ → (φ → θ)`, where `Γᵥ` lists, for each atom `p`, either `p`
(if `v p = true`) or `p → θ` (if `v p = false`). This is the risk-concentrated phase.

**Tasks**:
- [ ] Define `Γᵥ` as a `List`/`Finset` context keyed on the (finite) atoms of `φ`; entries stay
  implicational so the `IsImpTopOnly` invariant is preserved.
- [ ] Prove the truth lemma by `induction φ` over the imp-top-only structure: `atom`, `top`, and
  `imp` cases. The `imp` case uses S/K; the false-branch closure uses Peirce and the Phase-2 case
  lemma. Use `simp [Proposition.IsImpTopOnly]` for fragment-predicate side goals (as in
  `ImpConservative.lean`).
- [ ] Keep `θ` abstract (the eventual goal formula); do NOT use `decide`/`aesop` (Atom not Fintype).

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (extend).

**Verification**:
- Truth lemma compiles `sorry`-free.
- Spot-check both branches via `lean_goal` at the lemma's induction cases.
- **Blocked fallback**: if intractable, mark this phase `[BLOCKED]` with a precise note of the
  stuck goal state; leave NO sorry and NO axiom; downstream phases 4-5 then also block.

---

### Phase 4: Atom elimination and classicalImp_completeness [NOT STARTED]

**Goal**: Discharge the context `Γᵥ` atom-by-atom (S + Peirce) to collapse all Boolean
assignments, concluding `⊢ θ` for any tautology `θ`, yielding the one new theorem
`classicalImp_completeness`.

**Tasks**:
- [ ] Atom elimination step (report §6 step 4): from `⊢ Γ, p → θ` and `⊢ Γ, (p → θ) → θ` derive
  `⊢ Γ → θ`, halving the assignment set; iterate over the finite atom set of `φ`.
- [ ] Assemble: every Boolean branch yields `θ` (using the Phase-3 truth lemma with target
  `θ = φ`), so `Tautology φ → Derivable ClassicalImpAxiom φ`.
- [ ] State `theorem classicalImp_completeness {φ : PL.Proposition Atom} (hITO : φ.IsImpTopOnly)
  (h : Tautology φ) : Derivable ClassicalImpAxiom φ`.
- [ ] Docstrings; lowerCamelCase; `theorem` for the Prop-valued result.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (extend).

**Verification**:
- `classicalImp_completeness` compiles `sorry`-free; `lean_verify Cslib...classicalImp_completeness`
  shows no unexpected axioms.

---

### Phase 5: Conservativity theorem, chain extension, and CI gate [NOT STARTED]

**Goal**: Deliver the classical conservativity theorem as a short composition, extend the
conservative-extension chain with the classical branch, and pass the full CI pipeline.

**Tasks**:
- [ ] In the new module: `theorem cpl_conservative_over_imp {φ : PL.Proposition Atom}
  (hITO : φ.IsImpTopOnly) (h : Derivable PropositionalAxiom φ) : Derivable ClassicalImpAxiom φ :=
  classicalImp_completeness hITO (prop_soundness_tautology h)` and the
  `classicalImpAxiom_iff_chain` biconditional (`⟨derivableClassicalImpOfDerivableProp, cpl_conservative_over_imp hITO⟩`).
- [ ] In `Semantics/Algebra/ConservativeChain.lean` (additive): add the classical-branch
  subsumption `derivableClassicalImpOfDerivableProp`? No — the subsumption direction needed is
  `Derivable ClassicalImpAxiom φ → Derivable PropositionalAxiom φ` (the easy lift, name e.g.
  `derivablePropOfDerivableClassicalImp`) via `liftDerivationTree (fun ψ hψ => hψ.toPropAxiom)`
  (mirror `derivableIntOfDerivableProp`). The hard direction (`Prop → ClassicalImp` for
  imp-top-only) is exactly `cpl_conservative_over_imp` from the new module. Re-export/locate the
  classical conservativity result and extend the chain doc table (ConservativeChain.lean:25-36)
  with the classical-branch edge `CPL⟨→,⊤⟩ ⊂ CPL`.
- [ ] Confirm imports/barrel: `lake exe mk_all --module Cslib`.
- [ ] Run full CI gate (see Testing & Validation) and fix any lint/shake/import issues.

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (extend).
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` (additive: subsumption +
  doc table edge).

**Verification**:
- Full CI gate green (below). Existing intuitionistic chain theorems still compile unchanged.

---

## Testing & Validation

- [ ] `lake build` — whole library compiles, no `sorry`/`axiom` introduced.
- [ ] `lake test` — CslibTests suite passes.
- [ ] `lake exe checkInitImports` — new module imports `Cslib.Init`.
- [ ] `lake exe lint-style` — style clean (docstrings present, naming, line length).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports.
- [ ] `lake exe mk_all --module Cslib` — new module registered in the barrel.
- [ ] Existing chain preserved: `ConservativeChain.lean` intuitionistic theorems unchanged and
  still compile; no edits outside Propositional/{ProofSystem,Metalogic,Semantics/Algebra}.
- [ ] `lean_verify` on `classicalImp_completeness` and `cpl_conservative_over_imp` — expected
  axioms only (no `sorryAx`).

## Artifacts & Outputs

- `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` — `ClassicalImpAxiom` fragment +
  plumbing (appended block).
- `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` — new module:
  `classicalImp_soundness`, derived implicational lemmas, Kalmár truth lemma, atom elimination,
  `classicalImp_completeness`, `cpl_conservative_over_imp`, `classicalImpAxiom_iff_chain`.
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` — classical-branch
  subsumption + chain doc-table edge `CPL⟨→,⊤⟩ ⊂ CPL`.
- Barrel/import file updated via `mk_all`.
- `specs/352_cpl_conservative_over_classical_implicational_fragment/summaries/01_classical-imp-conservativity-summary.md`
  (at implementation completion).

## Rollback/Contingency

- All changes are additive and confined to three Propositional files plus the barrel. To revert,
  remove the `ClassicalImpAxiom` block from `FragmentAxioms.lean`, delete
  `Metalogic/ClassicalImpCompleteness.lean`, revert the `ConservativeChain.lean` additions, and
  re-run `lake exe mk_all --module Cslib`. The existing intuitionistic/minimal chain is never
  edited, so rollback cannot regress it.
- **Zero-debt fallback** (Risk R1): if the Kalmár proof (Phase 3/4) is intractable within budget,
  mark the offending phase `[BLOCKED]` with the stuck goal state recorded, leave NO `sorry` and NO
  `axiom`, and surface for user review. Phases 1-2 (fragment + soundness + derived lemmas) still
  land as self-contained, CI-green, additive value.
