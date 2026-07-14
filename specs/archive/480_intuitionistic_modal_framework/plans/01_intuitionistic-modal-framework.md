# Implementation Plan: Task #480 — Intuitionistic Modal Metalogic Framework

- **Task**: 480 - Intuitionistic modal metalogic FRAMEWORK (prime-theory machinery + birelational canonical-model construction)
- **Status**: [IMPLEMENTING]
- **Effort**: 11 hours
- **Dependencies**: Task 478 (classical Hilbert/metalogic framework, COMPLETED), Task 490 (birelational semantics `Birelational.lean`, must be present in-tree)
- **Research Inputs**: specs/480_intuitionistic_modal_framework/reports/01_intuitionistic-modal-framework.md
- **Artifacts**: plans/01_intuitionistic-modal-framework.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Build the reusable intuitionistic modal metalogic framework as a new subtree
`Cslib/Logics/Modal/Metalogic/Intuitionistic/` with four files: `PrimeTheory.lean`,
`CanonicalModel.lean`, `TruthLemma.lean`, `Completeness.lean`. The framework provides
prime-theory machinery (worlds as `PrimeAdmissible` prime theories, not MCS) and a
birelational canonical-model construction (with BOTH box-clause and diamond-clause
accessibility, since `◇` is primitive) so that downstream tasks IK (492), CK (493),
extensions (494), and minimal (495) instantiate parametric soundness/completeness with
no framework changes. Every framework lemma is parameterized over an `Axioms` predicate
with the base intuitionistic axioms as explicit hypotheses and `h_efq` as a SEPARATE
hypothesis (so minimal 495 can omit it). Definition of done: all four files build under
`lake build`, the full CSLib CI pipeline passes, ZERO-DEBT is upheld (no `sorry`, no new
`axiom`), and the classical `Metalogic/` files are left byte-for-byte untouched.

### Research Integration

Integrated from `reports/01_intuitionistic-modal-framework.md`:
- **Reuse verdict is strong.** Three sorry-free pieces compose: (1) the axiom-parameterized
  modal Hilbert calculus `DerivationTree`/`modalDerivationSystem`
  (`Cslib/Logics/Modal/Metalogic/DerivationTree.lean`), reused verbatim; (2) the F-generic
  `Metalogic.prime_exclusion` (`Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`),
  instantiated at `F = Modal.Proposition Atom`; (3) the propositional intuitionistic
  canonical model (`Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` +
  `IntStrongCompleteness.lean`) as a line-for-line template for the five non-modal
  truth-lemma cases and the `Preorder` = set-inclusion instance.
- **Genuinely new work is narrow**: (a) the intuitionistic modal axiom framework
  (base axioms as hypotheses, minus Peirce; `h_efq` separate); (b) `canonicalR` over prime
  theories with box-clause `□φ∈w→φ∈v` AND diamond-clause `φ∈v→◇φ∈w`; (c)
  `canonical_box_witness` (via prime exclusion, NOT negation+Peirce) and
  `canonical_diamond_witness`; (d) `canonical_f1`/`canonical_f2`; (e) the two modal
  truth-lemma cases (`box`, `diamond`).
- **Highest risk** is `canonical_diamond_witness` + the `.diamond` truth-lemma case
  (primitive `◇`, no classical analogue), grounded on Wijesekera 1990 prime-filter
  accessibility (chunk 0111) and Simpson 1994 canonical birelation model.
- K-derivation helpers `iteratedDeduction`/`derive_box_from_box_context` from `MCS.lean`
  (implyK/implyS/K only, no Peirce) are directly reusable for the box-witness derivation step.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_flag` set for this dispatch; ROADMAP.md not consulted. This framework task is the
shared dependency for tasks 492 (IK), 493 (CK), 494 (extensions IT/IS4/IS5), and 495 (minimal MK);
those relationships are recorded in the research report and orchestrator handoff, not in a roadmap.

## Goals & Non-Goals

**Goals**:
- Deliver `Cslib/Logics/Modal/Metalogic/Intuitionistic/{PrimeTheory,CanonicalModel,TruthLemma,Completeness}.lean`,
  all sorry-free and axiom-free, building under `lake build`.
- Keep every framework declaration parametric over `Axioms : Proposition Atom → Prop` with base
  intuitionistic axioms as explicit `h_*` hypotheses and `h_efq` as a SEPARATE hypothesis.
- Provide `canonicalR` with box + diamond clauses, the two witness lemmas, `canonical_f1`/`f2`,
  a single parametric `canonical_truth_lemma`, and parametric `ivalid`/`mvalid` completeness
  statements that 492–495 can instantiate.
- Pass the full CSLib CI pipeline (`lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake`), including docstrings on all new public declarations.

**Non-Goals**:
- No instantiation of concrete axiom systems (IK/CK/IT/IS4/IS5/MK) — those are tasks 492–495.
- No soundness proof of any specific `IntModalAxiom` set (consistency of concrete systems is a
  492/493 lemma); the framework only exposes the consistency hook, it does not discharge it.
- No modification of any classical file under `Cslib/Logics/Modal/Metalogic/` (Completeness.lean,
  MCS.lean, etc.) or of the propositional `Int*` files — reuse by import/transliteration only.
- No new notation, typeclass, or `axiom` declarations.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `canonical_diamond_witness` + `.diamond` truth-lemma case has no classical analogue | H | M | Ground on Wijesekera 1990 prime-filter accessibility (chunk 0111) and the `canonicalR` diamond-clause design in report §6.4–6.5; `--lit` active. Verify the witness construction set (`{ψ\|□ψ∈w} ∪ {φ}`) with lean-lsp `lean_goal` before committing the proof shape. |
| `canonicalR`'s two clauses must be mutually consistent with F1/F2 on prime worlds | H | M | Prove F1 via the diamond witness and F2 via the box witness (standard confluence over prime sets, report §6.6); check both frame-condition obligations against `BFrame.f1`/`BFrame.f2` signatures. |
| The eight `cl`/law arguments to `modal_prime_exclusion` are non-trivial transliterations of `int_prime_exclusion` (IntLindenbaum.lean:223-256) | M | M | Copy structurally from `IntLindenbaum.lean`; keep `modalDeductiveClosure` + laws adjacent so the `prime_exclusion` call site mirrors the propositional one; build incrementally. |
| `Birelational.lean` (task 490) API drift — `BForces`/`BFrame`/`IValid`/`MValid` signatures may differ from report assumptions | M | L | Read `Birelational.lean` first in Phase 2/3 and confirm exact field names and `@[simp]` unfold lemmas (`BForces_box`/`BForces_diamond`) before wiring `canonicalR`/truth lemma. |
| Lint failures (docBlame missing docstrings; lowerCamelCase; namespace wrapping) | M | M | Follow `IntStrongCompleteness.lean` conventions; docstring every new `def`/`theorem`; run `lake exe lint-style` + `lake shake` at each phase end. |
| `MValid`/fallible-world treatment for CK not exercised by framework, breaking 495 later | M | L | Keep `botForces` a parameter of the truth lemma (`fun _ => False` for IK, arbitrary upward-closed for minimal); do not hard-code `⊥∉w`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential (each phase
imports and builds on the previous file), so each wave contains one phase.

### Phase 1: PrimeTheory.lean — prime-theory machinery [COMPLETED]

**Goal**: Establish the intuitionistic modal prime-theory layer as a thin, parametric wrapper
over the reused generic `prime_exclusion`, mirroring the propositional `IntLindenbaum.lean`.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` with imports of
      `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`,
      `Cslib/Foundations/Logic/Metalogic/Consistency.lean`,
      `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`,
      `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean`, and `Cslib/Logics/Modal/Basic.lean`.
- [ ] Define `ModalSetConsistent Axioms S` and `ModalPrimeTheory Axioms S` (abbrevs over
      `Metalogic.SetConsistent` / `Metalogic.PrimeAdmissible` at
      `D = modalDerivationSystem Axioms`) — report §6.1.
- [ ] Define `modalDeductiveClosure Axioms` + closure laws (`cl_subset`, `cl_mem_imp`,
      `cl_admissible_of_cons`, `phi_mem_cl_of_not_cons`, `hCut`, `hConsChain`), transliterating
      the eight arguments from `IntLindenbaum.lean:223-256`.
- [ ] State and prove `modal_prime_exclusion` (report §6.2) as a wrapper over
      `Metalogic.prime_exclusion`, with explicit `h_implyK`/`h_implyS`/`h_efq`/`h_orE` hypotheses
      (`h_efq` SEPARATE so minimal 495 omits it).
- [ ] Transliterate `modal_imp_witness` (the `→`-witness builder, from `int_imp_witness`).
- [ ] Add docstrings to every new declaration; run `lake build` on the file.

**Timing**: 3 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` - new file (create subtree dir)

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory` succeeds, no `sorry`.
- `grep -c "sorry\|axiom " PrimeTheory.lean` returns 0.
- `modal_prime_exclusion` typechecks with `h_efq` as an independent hypothesis (confirm by
  reading the signature — minimal case must be able to drop it).

### Phase 2: CanonicalModel.lean — worlds, order, accessibility, witnesses [IN PROGRESS]

**Goal**: Build the birelational canonical frame over prime theories: worlds, `≤` = inclusion,
valuation, the two-clause `canonicalR`, the box/diamond witness lemmas, and F1/F2.

**Tasks**:
- [ ] Read `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) and confirm exact
      `BFrame`/`BModel`/`BForces`/`IValid`/`MValid` field names, `F1`/`F2` obligations, and the
      `@[simp]` unfold lemmas before wiring anything.
- [ ] Create `CanonicalModel.lean` importing Phase 1's `PrimeTheory.lean`, the classical
      `Cslib/Logics/Modal/Metalogic/MCS.lean` (for reuse of `iteratedDeduction` /
      `derive_box_from_box_context` — import only, do NOT modify), and `Birelational.lean`.
- [ ] Define `CanonicalPrimeWorld Axioms`, the `Preorder` = inclusion instance, and
      `canonicalVal` (copy shapes from `IntStrongCompleteness.lean`) — report §6.3.
- [ ] Define `canonicalR` with box-clause `□φ∈w→φ∈v` AND diamond-clause `φ∈v→◇φ∈w` — report §6.4.
- [ ] Prove `canonical_box_witness`: from `□φ∉w` build `{ψ | □ψ∈w}`, show it cannot derive `φ`
      via reused `derive_box_from_box_context`, then apply `modal_prime_exclusion` — report §6.5.
- [ ] Prove `canonical_diamond_witness`: from `◇φ∈w` extend `{ψ | □ψ∈w} ∪ {φ}`, secure the
      diamond clause, apply prime exclusion — report §6.5 (highest-risk proof; verify goal states
      with `lean_goal` incrementally).
- [ ] Prove `canonical_f1` (diamond witness transported along inclusion) and `canonical_f2`
      (box witness) — report §6.6.
- [ ] Docstrings on all declarations; `lake build` on the file.

**Timing**: 4 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` succeeds, no `sorry`.
- `canonical_f1`/`canonical_f2` typecheck against the `BFrame.f1`/`BFrame.f2` obligation shapes
  read from `Birelational.lean`.
- The classical `MCS.lean`/`Completeness.lean` files show no diff (`git diff --stat` empty for them).

### Phase 3: TruthLemma.lean — birelational truth lemma [NOT STARTED]

**Goal**: Prove the single parametric `canonical_truth_lemma` covering all seven `Proposition`
constructors: five non-modal cases transliterated from `int_truth_lemma`, plus the two new
modal cases via the Phase 2 witnesses.

**Tasks**:
- [ ] Create `TruthLemma.lean` importing Phase 2's `CanonicalModel.lean`.
- [ ] Transliterate the `atom`/`bot`/`and`/`or`/`imp` cases line-for-line from
      `IntStrongCompleteness.lean:108-214` (`PL.Proposition`→`Modal.Proposition`,
      `IntPropAxiom`→`Axioms`), keeping `botForces` a parameter (`fun _ => False` default, not
      hard-coded) so minimal/CK fallible-world treatment is supported — report §6.7, §7.
- [ ] Prove the `.box` case using `canonical_box_witness` + heredity over `≤∘R`.
- [ ] Prove the `.diamond` case using `canonical_diamond_witness` (highest-risk case).
- [ ] Use `BForces_box`/`BForces_diamond` `@[simp]` unfolds; follow explicit `DerivationTree`
      term-mode style (no `simp`/`aesop` for the non-modal cases, per report §9 literature-fidelity).
- [ ] Docstrings; `lake build` on the file.

**Timing**: 2.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.TruthLemma` succeeds, no `sorry`.
- `canonical_truth_lemma` covers all seven constructors (no missing-case warning).
- `botForces` appears as a parameter, not a hard-coded `fun _ => False`, in the lemma signature.

### Phase 4: Completeness.lean — parametric packaging [NOT STARTED]

**Goal**: Package the canonical `BModel` and expose parametric `ivalid`/`mvalid` completeness
statements that tasks 492–495 instantiate, plus the consistency hook.

**Tasks**:
- [ ] Create `Completeness.lean` importing Phase 3's `TruthLemma.lean`.
- [ ] Assemble the canonical `BModel` from `CanonicalPrimeWorld`, `Preorder`, `canonicalR`,
      `canonicalVal`, and the `canonical_f1`/`f2` frame conditions.
- [ ] State parametric `ivalid_completeness` / `mvalid_completeness` (from `canonical_truth_lemma`
      + `modal_prime_exclusion` on the underivable formula) with the base-axiom and `h_efq`
      (IValid) / arbitrary-`botForces` (MValid) hypotheses exposed for 492–495 — report §7.
- [ ] Expose a consistency hook (parametric statement, discharged by 492/493, not here) so the
      framework does not assume any concrete `IntModalAxiom` is consistent — report §10.
- [ ] Docstrings; `lake build` on the file.
- [ ] Run the full CI pipeline and confirm ZERO-DEBT and untouched classical files.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean` - new file

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness` succeeds, no `sorry`.
- `ivalid_completeness`/`mvalid_completeness` typecheck as parametric statements (no concrete
  axiom set required to state them).
- Full CI pipeline (see Testing & Validation) passes.

## Testing & Validation

- [ ] `lake build` succeeds for all four new modules (whole-tree build green).
- [ ] `lake test` (CslibTests suite) passes.
- [ ] `lake exe checkInitImports` passes (Cslib.Init imports verified).
- [ ] `lake exe lint-style` passes (style linting; all new decls have docstrings).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused-import issues on
      the new subtree.
- [ ] ZERO-DEBT check: `grep -rn "sorry\|admit\|^axiom \| axiom " Cslib/Logics/Modal/Metalogic/Intuitionistic/`
      returns nothing.
- [ ] Untouched-classical check: `git diff --stat` shows no changes to any existing file under
      `Cslib/Logics/Modal/Metalogic/` (only new `Intuitionistic/` files added) or to the
      propositional `Int*` files.
- [ ] Parametricity check: each framework lemma carries `Axioms` + explicit `h_*` base-axiom
      hypotheses with `h_efq` separable (readable from signatures).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean`
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean`
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean`
- `specs/480_intuitionistic_modal_framework/plans/01_intuitionistic-modal-framework.md` (this plan)
- `specs/480_intuitionistic_modal_framework/summaries/01_intuitionistic-modal-framework-summary.md` (on completion)

## Rollback/Contingency

- All work is additive under a new `Intuitionistic/` subtree; no classical file is edited.
  Rollback = delete the four new files and remove any aggregator import line added to a module
  index. No regression risk to existing proofs.
- If `canonical_diamond_witness` or the `.diamond` truth-lemma case cannot be closed sorry-free
  within Phase 2/3 budget, STOP (do not introduce `sorry` — ZERO-DEBT is a hard constraint):
  mark the phase `[PARTIAL]`, commit the sorry-free portion (Phases 1–2 box side), and dispatch
  `/research 480 --hard --lit` focused narrowly on the Wijesekera diamond-accessibility
  construction before resuming.
- If `Birelational.lean` (task 490) is absent or its API diverges materially from the report
  assumptions, mark the task `[BLOCKED]` on task 490 rather than reconstructing the semantics here.
