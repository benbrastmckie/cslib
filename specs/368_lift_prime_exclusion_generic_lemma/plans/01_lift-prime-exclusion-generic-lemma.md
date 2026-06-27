# Implementation Plan: Task #368

- **Task**: 368 - lift_prime_exclusion_generic_lemma
- **Status**: [NOT STARTED]
- **Effort**: 6.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/368_lift_prime_exclusion_generic_lemma/reports/01_lift-prime-exclusion-generic-lemma.md
- **Artifacts**: plans/01_lift-prime-exclusion-generic-lemma.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Deduplicate the prime-exclusion machinery shared by the intuitionistic (`IntLindenbaum.lean`)
and minimal (`MinLindenbaum.lean`) Lindenbaum constructions by lifting their ~70% identical
Zorn + orE + chain-union logic into a single new generic file
`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`. The generic lemma is stated purely
over an abstract `Metalogic.DerivationSystem F` (never mentioning `PL.Proposition`,
`DerivationTree`, or concrete axioms), mirroring the existing `set_lindenbaum` template in
`Consistency.lean`. The sole real divergence — intuitionistic threads an EFQ consistency check —
is isolated into two parameters: an optional consistency predicate `Cons` (default `fun _ => True`)
and an EFQ-bridge witness `phi_mem_cl_of_not_cons` (vacuous in the minimal case). Both call sites
become ~10-line wrappers; net ~150-line reduction with no new axioms and both StrongCompleteness
proofs staying sorry-free.

### Research Integration

The research report provides the full generic design (Section 4): exact Lean signatures for
`DeductivelyClosed`, `Admissible`, `PrimeExcludingSupersets`, `PrimeAdmissible`, the main
`prime_maximal_is_prime` lemma with its ~8 structural parameters, and the supporting
`prime_excluding_base_mem`, `deductivelyClosed_chain_union`, `prime_excluding_chain_union`,
and `prime_exclusion` (Zorn) lemmas. Section 5 gives the call-site re-derivation sketch for both
minimal (`Cons := fun _ => True`, EFQ bridge vacuous) and intuitionistic
(`Cons := SetConsistent (propDerivationSystem IntPropAxiom)`, EFQ block lifted from `Int:344-355`)
sides. Section 6 confirms every referenced symbol against source line numbers. Section 7 flags the
key watch-items integrated into Risks below (`insert a U` vs `U ∪ {a}` adapter, definitional
`cl_mem_imp`, parameter count, preserving public names, CI commands).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` with the generic
  prime-exclusion / maximal-is-prime machinery over abstract `DerivationSystem F`.
- Re-derive `int_prime_exclusion` (IntLindenbaum.lean) and `min_prime_exclusion`
  (MinLindenbaum.lean) as thin wrappers over the generic lemma.
- Achieve a ~150-line net reduction across the two Lindenbaum files.
- Keep both StrongCompleteness proofs sorry-free; introduce no new axioms; keep CI green.

**Non-Goals**:
- No changes to the underlying logic of either Lindenbaum construction (behavior-preserving refactor).
- No deletion of public names (`IntDCCS`, `MinTheory`, `IntPrimeDCCS`, `MinPrimeTheory`) — they are
  re-expressed as `abbrev`/iff wrappers, not removed (downstream `StrongCompleteness` depends on them).
- No optional `structure PrimeExclusionData` bundling unless trivially beneficial (Risk 3 — polish only).
- No changes outside the three target Lean files plus the `Cslib.lean` barrel.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `insert a U` vs `U ∪ {a}` mismatch between generic `hCut` and existing witnesses | M | H | One-line `Set.union_comm` / `insert` defeq adapter per call site (Research §7.1); not a blocker |
| orE combination block (heavy part) fails to generalize cleanly | H | M | Block uses only `D.weakening`/`D.assumption`/`D.mp`/`hOrE` (all `DerivationSystem` fields); transcribe `Int:386-418`≡`Min:316-351` once, verify with `lean_goal` incrementally |
| EFQ bridge parameter mis-typed when threaded from int side | M | M | Lift the exact `Int:344-355` block unchanged into `phi_mem_cl_of_not_cons`; verify int build before declaring phase done |
| Breaking downstream StrongCompleteness by altering public predicate names | H | L | Keep `IntDCCS`/`MinTheory`/`*Prime*` as `abbrev`/iff over `Admissible`; do not delete (Research §7.4) |
| docBlame / lint-style failures on new file | L | H | Add `import Cslib.Init`, docstring on every new declaration; run `lake exe lint-style` + `checkInitImports` in Phase 5 |
| New file not registered in barrel | L | M | Run `lake exe mk_all --module` and confirm `Cslib.lean` updated (Phase 5) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. Phases 3 and 4 touch different files
(`MinLindenbaum.lean` vs `IntLindenbaum.lean`) and both depend only on the completed generic
lemma, so they are independently completable.

### Phase 1: Generic scaffolding — defs + base/chain lemmas [NOT STARTED]

**Goal**: Create `PrimeExclusion.lean` with the generic predicate definitions and the lightweight
supporting lemmas (base membership and chain-union closure), all building sorry-free.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` with header
  `import Cslib.Init` + `import Cslib.Foundations.Logic.Metalogic.Consistency`,
  `namespace Cslib.Logic.Metalogic`, and `variable {F : Type*} [HasImp F] [HasBot F] [HasOr F]`.
- [ ] Define `DeductivelyClosed`, `Admissible` (with `Cons` predicate), `PrimeExcludingSupersets`,
  `PrimeAdmissible` per Research §4 (all `def`, each with a docstring).
- [ ] Implement `prime_excluding_base_mem` (Research §4.2) — `⟨Set.Subset.refl, hS, h_not⟩`.
- [ ] Implement `deductivelyClosed_chain_union` mirroring `Int:299-303`/`Min:254-260` using
  `finite_list_in_chain_member` (reuse from `Consistency.lean:115`).
- [ ] Implement `prime_excluding_chain_union` (Research §4.2) threading `hConsChain : Cons (⋃₀ C)`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` - new file: generic defs + base/chain lemmas

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.PrimeExclusion` succeeds with no `sorry` and no errors.
- `lean_goal` confirms `deductivelyClosed_chain_union` and `prime_excluding_chain_union` close fully.

---

### Phase 2: Generic main lemma — prime_maximal_is_prime + prime_exclusion [NOT STARTED]

**Goal**: Implement the core generic `prime_maximal_is_prime` (including the heavy orE combination
block) and the `prime_exclusion` Zorn application, completing the generic file sorry-free.

**Tasks**:
- [ ] Implement `prime_maximal_is_prime` with the ~8 structural parameters (`hOrE`, `cl`,
  `cl_subset`, `cl_mem_imp`, `cl_admissible_of_cons`, `phi_mem_cl_of_not_cons`, `hCut`, `hmax`)
  per Research §4.1.
- [ ] Transcribe the orE combination block once (currently `Int:386-418` ≡ `Min:316-351`): build
  `(A⟶φ)⟶((B⟶φ)⟶((A⊔B)⟶φ))` from `[]`, weaken to `ctx`, three `modus_ponens`, close via
  `DeductivelyClosed D T`, using only `D.weakening`/`D.assumption`/`D.mp`/`hOrE`.
- [ ] Implement the `by_cases hc : Cons (insert A T)` split (Research §4.1 proof body): consistent
  branch is the shared maximality argument; inconsistent branch delegates to `phi_mem_cl_of_not_cons`.
- [ ] Implement `prime_exclusion` (Research §4.2) — `zorn_subset_nonempty` application mirroring
  `set_lindenbaum`, wiring `prime_excluding_base_mem`, `prime_excluding_chain_union`, and
  `prime_maximal_is_prime`.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` - add `prime_maximal_is_prime` + `prime_exclusion`

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.PrimeExclusion` succeeds; `lean_verify` shows no
  new axioms beyond those already used by `Consistency.lean`.
- `grep -c sorry` on the file returns 0.

---

### Phase 3: Re-derive minimal side (min_prime_exclusion wrapper) [NOT STARTED]

**Goal**: Replace the duplicated minimal prime-exclusion machinery in `MinLindenbaum.lean` with a
thin wrapper over the generic lemma using `Cons := fun _ => True` and a vacuous EFQ bridge.

**Tasks**:
- [ ] Set `D := propDerivationSystem MinPropAxiom`, `Cons := fun _ => True`.
- [ ] Re-express `MinTheory` / `MinPrimeTheory` as `abbrev`/iff over `Admissible` / `PrimeAdmissible`
  (keep public names — Research §7.4).
- [ ] Wire instantiations (Research §5.1): `cl := minDeductiveClosure`;
  `cl_subset := min_subset_deductive_closure`; `cl_mem_imp := fun h => h` (definitional);
  `cl_admissible_of_cons := fun _ => ⟨trivial, minDeductiveClosure_is_theory _⟩`;
  `phi_mem_cl_of_not_cons := fun h => absurd trivial h` (vacuous);
  `hCut := @min_deriv_imp_of_union` (with `Set.union_comm`/`insert` adapter);
  `hOrE` from `MinPropAxiom.orE`; `hConsChain := fun _ _ _ _ => trivial`.
- [ ] Rewrite `min_prime_exclusion` as a ~10-line wrapper calling `prime_exclusion`.
- [ ] Delete the now-redundant `MinPrimeExcludingSupersets`, `min_excluding_base_mem`,
  `min_excluding_chain_union`, `min_maximal_is_prime` (superseded by generic copies).

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/.../MinLindenbaum.lean` - import PrimeExclusion; replace duplicated machinery with wrapper

**Verification**:
- `lake build` of the minimal Lindenbaum module and its `StrongCompleteness` dependents succeeds.
- The minimal StrongCompleteness proof remains sorry-free (`grep -c sorry` unchanged at 0).

---

### Phase 4: Re-derive intuitionistic side (int_prime_exclusion wrapper) [NOT STARTED]

**Goal**: Replace the duplicated intuitionistic prime-exclusion machinery in `IntLindenbaum.lean`
with a thin wrapper, threading the EFQ consistency check through the generic parameters.

**Tasks**:
- [ ] Set `D := propDerivationSystem IntPropAxiom`,
  `Cons := SetConsistent (propDerivationSystem IntPropAxiom)` (= `PropSetConsistent IntPropAxiom`).
- [ ] Re-express `IntDCCS` / `IntPrimeDCCS` as `abbrev`/iff over `Admissible` / `PrimeAdmissible`
  (keep public names — Research §7.4).
- [ ] Wire instantiations (Research §5.2): `cl := intDeductiveClosure`;
  `cl_admissible_of_cons := fun hc => intDeductiveClosure_is_dccs hc`;
  `phi_mem_cl_of_not_cons :=` the EFQ block lifted unchanged from `Int:344-355`
  (unfold inconsistency, `.efq`, weaken, MP from `⊥`);
  `hCut := @int_deriv_imp_of_union` (with `insert` adapter);
  `hOrE` from `IntPropAxiom.orE`; `hConsChain := consistent_chain_union` (Foundations).
- [ ] Rewrite `int_prime_exclusion` as a ~10-line wrapper calling `prime_exclusion`.
- [ ] Delete the now-redundant `IntPrimeExcludingSupersets`, `int_excluding_base_mem`,
  `int_excluding_chain_union`, `int_maximal_is_prime`.

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/.../IntLindenbaum.lean` - import PrimeExclusion; replace duplicated machinery with wrapper

**Verification**:
- `lake build` of the intuitionistic Lindenbaum module and its `StrongCompleteness` dependents succeeds.
- The intuitionistic StrongCompleteness proof remains sorry-free; no new axioms via `lean_verify`.

---

### Phase 5: CI verification, barrel registration, and cleanup [NOT STARTED]

**Goal**: Register the new file in the barrel, run the full CSLib CI pipeline, and confirm the
net line reduction and zero-sorry / zero-new-axiom invariants.

**Tasks**:
- [ ] Run `lake exe mk_all --module` and confirm `PrimeExclusion.lean` is added to the `Cslib.lean` barrel.
- [ ] Run `lake build` (full) — green.
- [ ] Run `lake test` (CslibTests suite) — green.
- [ ] Run `lake exe checkInitImports` — confirms new file imports `Cslib.Init`.
- [ ] Run `lake exe lint-style` — fix any docBlame / style issues on new declarations.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` — prune any unused imports.
- [ ] Confirm net ~150-line reduction across the two Lindenbaum files (`git diff --stat`).

**Timing**: 1 hour

**Depends on**: 3, 4

**Files to modify**:
- `Cslib.lean` - barrel entry for the new module (via `mk_all`)
- Minor import/docstring fixups across the three target files as surfaced by CI

**Verification**:
- All five CI commands pass (`lake build`, `lake test`, `checkInitImports`, `lint-style`, `shake`).
- `git diff --stat` shows a net reduction of approximately 150 lines.
- No `sorry` and no new axioms anywhere in the three touched files.

## Testing & Validation

- [ ] `lake build` passes (full library) with no errors and no `sorry`.
- [ ] `lake test` passes (CslibTests).
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (docstrings on all new declarations).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports.
- [ ] Both `IntLindenbaum` and `MinLindenbaum` StrongCompleteness proofs remain sorry-free.
- [ ] `lean_verify` confirms no axioms beyond the pre-existing ones.
- [ ] Net ~150-line reduction confirmed via `git diff --stat`.

## Artifacts & Outputs

- New file `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (generic prime-exclusion machinery).
- Modified `MinLindenbaum.lean` (minimal side reduced to wrapper).
- Modified `IntLindenbaum.lean` (intuitionistic side reduced to wrapper).
- Updated `Cslib.lean` barrel.

## Rollback/Contingency

The refactor is confined to one new file plus two existing Lindenbaum files and the barrel. If any
phase fails CI or cannot stay sorry-free:
- Phases are committed incrementally (one commit per completed phase), so `git revert` of the
  offending phase's commit restores the prior green state without losing earlier phases.
- The generic file (Phases 1-2) is additive and independent: if call-site re-derivation (Phases 3-4)
  proves intractable, the generic file can remain unused while the original duplicated machinery is
  restored, yielding no behavior change.
- If the orE block (Phase 2) resists generalization, fall back to keeping `prime_maximal_is_prime`
  as the only shared piece and leaving thinner per-site Zorn applications (partial dedup, smaller
  reduction) rather than blocking the task.
