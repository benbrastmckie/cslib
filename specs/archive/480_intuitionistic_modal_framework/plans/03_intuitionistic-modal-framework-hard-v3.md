# Implementation Plan (v3, HARD): Task #480 — Intuitionistic Modal Metalogic Framework

- **Task**: 480 - Intuitionistic modal metalogic FRAMEWORK (prime-theory machinery + birelational canonical-model construction)
- **Status**: [IN PROGRESS]
- **Effort**: ~8.5 hours remaining (Phases 1 + 2a complete; new set-exclusion infra + K◇ sub-lemma add ~2h over v2's estimate)
- **Dependencies**: Task 478 (classical Hilbert/metalogic framework, COMPLETED), Task 490 (birelational semantics `Birelational.lean`, present in-tree)
- **Research Inputs**: reports/01_intuitionistic-modal-framework.md; reports/02_set-exclusion-infra-box-witness.md (new — set-exclusion infra design + FEASIBLE verdict)
- **Artifacts**: plans/03_intuitionistic-modal-framework-hard-v3.md (this file); supersedes plans/02_intuitionistic-modal-framework-hard.md (v2, retained for history) and plans/01_intuitionistic-modal-framework.md (v1)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Plan Version**: 3 (hard-mode re-slice folding in set-exclusion infrastructure)
- **Lean Intent**: false

## Overview

This is **v3**: a hard-mode re-slice of v2 that folds in the newly-researched **set-exclusion
("Lindenbaum-pair") infrastructure** (reports/02). v2 completed Phase 1 (`PrimeTheory.lean`,
`be8f2eb0`) and Phase 2a (`CanonicalModel.lean` definitions, `4fd37213`), then **BLOCKED at Phase
2b**: the box witness needs to extend a set to a prime theory that excludes an **entire set** `Σ`,
but Cslib only has **single-formula** exclusion (`Metalogic.prime_exclusion`). Report 02 delivers
the exact generalizing lemma (`prime_set_exclusion`) and confirms the whole fix is **FEASIBLE,
zero-debt, and purely additive** (no edit to any existing declaration). It also **corrects the box
witness statement** to a PAIR `⟨w', u⟩` with `w ≤ w'` (not the old `⟨w, v⟩`), and resolves the
apparent `◇⊤`/seriality precondition as a red herring removed by seeding a fresh `w'`.

The v2→v3 delta is three new/revised phases inserted before the old Phase 2b, plus downstream
propagation of the corrected pair-shaped witness:
1. **NEW Phase 2-infra** (do FIRST after 2a): add `prime_set_exclusion` + `bigOr` + append-
   monotonicity helpers + `DerivExcludes` to `Foundations/Logic/Metalogic/PrimeExclusion.lean`
   (purely additive), plus the missing `Wijesekera1990` BibTeX entry.
2. **NEW Phase 2b-sublemma**: prove `box_witness_pair_underivable` (the K◇ modal consistency
   sub-lemma) — HIGHEST RISK, its own STOP contingency.
3. **REVISED Phase 2b**: prove `canonical_box_witness` with the corrected pair statement
   `∃ w' u, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val`, via a `modal_set_exclusion` wrapper placed in
   `CanonicalModel.lean`.
Phases 2c/2d/3a/3b/3c/4 carry over from v2 with the corrected witness shape propagated.

Definition of done (unchanged from v2): all four files under
`Cslib/Logics/Modal/Metalogic/Intuitionistic/` build under `lake build`, `PrimeExclusion.lean`'s
additive extension builds tree-wide with all existing `prime_exclusion` users still green, the full
CSLib CI pipeline passes, ZERO-DEBT is upheld (no `sorry`, no `admit`, no new `axiom`; K◇ is a
parametric hypothesis, not a global axiom), and the classical `Metalogic/` files plus the
propositional `Int*` files are left byte-for-byte untouched.

### Preserved Assets

The following work is complete, committed, and MUST NOT regress. It is **not re-sliced**; import
and build on it only.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Phase 1: `ModalSetConsistent`, `ModalPrimeTheory`, `modalDeductiveClosure` + closure laws, `modalNegPhiImpPsi_deriv`, `modal_imp_witness`, `modal_prime_exclusion`, `modal_deriv_imp_of_union` | `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (360 lines) | [COMPLETED] | commit be8f2eb0; grep shows no `sorry`/`admit`/`axiom` |
| Phase 2a: `CanonicalPrimeWorld`, `Preorder` = inclusion instance, `canonicalVal`, two-clause `canonicalR` (box clause `□φ∈w→φ∈v` AND diamond clause `φ∈v→◇φ∈w`) — definitions only, no witness proofs | `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` | [COMPLETED] | commit 4fd37213; definitions only, byte-for-byte unchanged since |

The following upstream infrastructure is reused by import/transliteration and MUST NOT be edited
(untouched-classical constraint):

| Asset | File | Reuse mode |
|-------|------|-----------|
| `Metalogic.prime_exclusion` (generic, single-formula) + its Zorn helpers (`deductivelyClosed_chain_union`, `prime_excluding_chain_union`, `prime_maximal_is_prime`, `zorn_subset_nonempty` call) | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` | **EXTENDED ADDITIVELY in Phase 2-infra** — existing decls left byte-for-byte identical; only new `def`/`theorem`s added in a new `section` |
| `Axioms.OrI1`/`OrI2`/`OrE`/`EFQ` empty-context schemas | `Cslib/Logic/Axioms.lean` (≈L85, L122-133) | import-only; supplied as `hOrI1/hOrI2/hOrE/hEFQ` hypotheses to `prime_set_exclusion` |
| `DerivationTree` / `modalDerivationSystem` / `deductionTheorem` | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`, `DeductionTheorem.lean` | import-only, verbatim |
| `iteratedDeduction`, `derive_box_from_box_context` (deductively-closed variant devised in v2) | `Cslib/Logics/Modal/Metalogic/MCS.lean` | import-only; NEVER modify MCS.lean |
| `BFrame`/`BModel`/`BForces`/`bforces_persistence`/`IValid`/`MValid`/`BForces_box`/`BForces_diamond` | `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) | import-only, codomain of truth lemma |
| `int_truth_lemma` non-modal cases (template) | `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean:108-214` | transliterate (copy), do not import |

### Research Integration

Integrated from reports/01 (v1/v2 base) and **reports/02** (new set-exclusion infra, Tier-1
literature-backed, `--lit` active). Report 02's key verdicts:
- The Phase 2b blocker is **infrastructure, not mathematics** — the `◇⊤`/seriality framing was a
  red herring caused by fixing `w' := w`; seeding a fresh `w'` removes it.
- `prime_set_exclusion` is a natural additive generalization of `prime_exclusion`'s Zorn argument;
  the generic chain machinery carries over essentially verbatim, and `OrI1/OrI2/OrE/EFQ` already
  exist. **Zero-debt: FEASIBLE.**
- The corrected `canonical_box_witness` is a PAIR `⟨w', u⟩` with `w ≤ w'`; `BForces_box` unfolds to
  `∀ w'≥w, ∀ u, r w' u → force u φ`, so the outer `∀ w'≥w` is load-bearing (consumed by Phase 3b).
- The only residual risk is `box_witness_pair_underivable` (the K◇ consistency sub-lemma), scoped
  OUT of the generic infra lemma into its own delicate ~60-120-line phase.

### Source-to-Implementation Mapping (H3, Tier 1)

| Load-bearing decision | Source (BibKey / report / in-repo) | Consumed by phase |
|-----------------------|------------------------------------|-------------------|
| Worlds = prime theories; `≤` = inclusion; `canonicalVal`; two-clause `canonicalR` | Report 01 §6.3-6.4; `Simpson1994` (references.bib:86) Ch.3; IntStrongCompleteness `Preorder` | 2a (preserved) |
| `prime_set_exclusion` generalizes single-formula exclusion via same Zorn domain; `DerivExcludes D Σ T := ∀ finite l⊆Σ, bigOr l ∉ T`; `bigOr []=⊥` | Report 02 Deliverables 1-2; `ChagrovZakharyaschev1997` (references.bib:75) Lemma 5.5; ianshil/CK `Lindenbaum_pair`/`pair_extCKH_prv` | 2-infra |
| `bigOr_append_left/right`, `or_right_mono` from `OrI1/OrI2/OrE/EFQ` (no new axiom) | Report 02 Deliverable 2 "new derivation lemmas"; `Axioms.OrI1/OrI2/OrE/EFQ` | 2-infra |
| `Wijesekera1990` = Constructive Modal Logics I, APAL 50(3):271-301, 1990 (prime filters + accessibility) | Report 02 Deliverable 5; `wijesekera_1990_constructivemodallogicsi` corpus chunks 0040-0044 (OCR-truncated) | 2-infra (bib entry) |
| Box witness = PAIR `⟨w', u⟩`, `w ≤ w'`; `u` = prime ext of `{ψ\|□ψ∈w}` excluding `φ`; `w'` = seeded prime ext of `w.val ∪ {◇A\|A∈u.val}` excluding `Σ={□B\|B∉u.val}` | Report 02 Deliverable 3; ianshil/CK `general_th_completeness.v` Box case L~140-200; `Simpson1994` Ch.3 | 2b |
| `box_witness_pair_underivable`: `DerivExcludes Σ Γ` precondition discharged by K◇ (`□(A→B)→(◇A→◇B)`) + `u` primeness; NO seriality/`◇⊤` | Report 02 Deliverable 3 "Where K◇ discharges…"; ianshil/CK `Kd`/`K_rule` | 2b-sublemma (HIGHEST RISK) |
| Diamond witness = mirror image (seed box-side, exclude a diamond-set); same `prime_set_exclusion` | Report 02 Deliverable 3 tail; Report 01 §6.5, §10; `Wijesekera1990` | 2c (HIGHEST RISK) |
| F1 via diamond witness, F2 via box witness | Report 01 §6.6; `Simpson1994` F1/F2 confluence | 2d |
| 5 non-modal truth cases (atom/bot/and/or/imp) | Report 01 §6.7, §9; IntStrongCompleteness.lean:108-214 | 3a |
| `.box` case consumes the `⟨w', u⟩` pair-shaped witness + heredity over `≤∘R`; `BForces_box` unfold | Report 01 §6.7; Report 02 Deliverable 3 (load-bearing `∀ w'≥w`); `Simpson1994` clause 3.2 | 3b |
| `.diamond` case consumes the diamond witness; `BForces_diamond` unfold | Report 01 §6.7, §10; `Wijesekera1990` | 3c (HIGHEST RISK) |
| Parametric `ivalid`/`mvalid`; `h_efq` separable; `botForces` a parameter; consistency hook | Report 01 §7, §10 | 4 |

## Goals & Non-Goals

**Goals**:
- Add `prime_set_exclusion` (+ `bigOr`, `DerivExcludes`, `SetExcludingSupersets`, `bigOr_append_*`,
  `or_right_mono`) to `PrimeExclusion.lean` as a purely additive extension; add `Wijesekera1990` to
  `references.bib`.
- Complete `CanonicalModel.lean`, `TruthLemma.lean`, `Completeness.lean` sorry-free and axiom-free
  atop preserved `PrimeTheory.lean`/`CanonicalModel.lean` (2a), each phase building independently.
- Keep every new framework declaration parametric over `Axioms : Proposition Atom → Prop` with base
  intuitionistic axioms (and K◇) as explicit `h_*` hypotheses; `h_efq` SEPARATE; `botForces` a
  truth-lemma parameter.
- Provide the corrected pair-shaped `canonical_box_witness`, `canonical_diamond_witness`,
  `canonical_f1`/`f2`, a single parametric `canonical_truth_lemma`, and parametric `ivalid`/`mvalid`
  completeness statements for 492-495 to instantiate.
- Pass the full CSLib CI pipeline; docstring every new public declaration.

**Non-Goals**:
- No refactor of `prime_exclusion` to route through `prime_set_exclusion` (report 02 §Deliverable 4:
  keep independent, zero blast radius; the corollary relationship is documented, not enforced).
- No instantiation of concrete axiom systems (IK/CK/IT/IS4/IS5/MK) — tasks 492-495.
- No soundness/consistency discharge of any concrete `IntModalAxiom` set — framework exposes the
  hook only. No new `Axioms.AxiomKDia` abbrev (K◇ stays a parametric `h_Kdia` hypothesis).
- No modification of any classical `Metalogic/` file, `MCS.lean`, the propositional `Int*` files,
  the preserved `PrimeTheory.lean`, or Phase 2a's committed `CanonicalModel.lean` definitions.

## Postmortem Constraints

Binding rules for all implementation dispatches, derived from the v2 Phase 2b blocker, reports/02,
and the failed monolithic v1 dispatch.

**Do NOT**:
- **Do NOT attempt more than one phase's deliverable per dispatch.** Each phase below is one agent
  run (H8). The v1 monolithic attempt failed to reach a sorry-free `CanonicalModel.lean` in one run.
- **Do NOT introduce `sorry`/`admit`/`axiom` to "make it build" and defer the hard part.** ZERO-DEBT
  is a hard constraint. If a HIGHEST-RISK proof (2b-sublemma, 2c) will not close, invoke its STOP
  contingency (report PARTIAL + continuation note); never commit debt. K◇ enters as a **parametric
  `h_Kdia` hypothesis** in the framework's established style, NOT as a global `axiom`.
- **Do NOT fix the box witness as `⟨w, v⟩` with `w` unchanged.** That is the v2 dead end — it forces
  a spurious `◇⊤`/seriality precondition. The witness is a PAIR `⟨w', u⟩` with `w ≤ w'`, `w'` a
  fresh SEEDED extension (report 02 Deliverable 3). This is SETTLED.
- **Do NOT modify any existing declaration in `PrimeExclusion.lean`.** Phase 2-infra is purely
  additive: only new `def`/`theorem`s in a new `section [HasBot F]` (HasBot already in scope via
  `Consistency.lean:11`; no new import). `prime_exclusion` and its helpers stay byte-for-byte
  identical. After the addition, confirm existing `prime_exclusion` users still build tree-wide.
- **Do NOT re-open Phase 1 (`PrimeTheory.lean`) or Phase 2a (`CanonicalModel.lean` definitions).**
  Both are committed and building. To respect the `PrimeTheory.lean` no-touch rule, place the
  `modal_set_exclusion` wrapper in `CanonicalModel.lean` (report 02 Deliverable 4 endorses this as
  equally valid — it only needs the public `prime_set_exclusion`), NOT in `PrimeTheory.lean`.
- **Do NOT edit `MCS.lean`, classical `Completeness.lean`, or any propositional `Int*` file.** Reuse
  by import; transliterate `int_truth_lemma` by copy.
- **Do NOT use `simp`/`aesop` for the non-modal truth-lemma cases.** Follow the explicit
  `DerivationTree` term-mode style of `int_truth_lemma`. `BForces_box`/`BForces_diamond` `@[simp]`
  unfolds are the only expected `simp` use.
- **Do NOT re-derive the classical box witness via negation + Peirce.** Peirce is not available; the
  intuitionistic construction uses `modal_prime_exclusion` (Step 1) + `modal_set_exclusion` (Step 2).

**MUST preserve**:
- `PrimeTheory.lean` (be8f2eb0) and Phase 2a `CanonicalModel.lean` definitions (4fd37213), byte-for-
  byte, plus every upstream file in Preserved Assets.
- Every existing declaration in `PrimeExclusion.lean` (extend additively only).
- Existing green builds of the classical `Metalogic/` subtree, the propositional `Int*` subtree,
  and all downstream users of `prime_exclusion` (`git diff --stat` shows only additive hunks).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- The box witness is the PAIR `⟨w', u⟩`, `w ≤ w'`; `u` = prime extension of `{ψ|□ψ∈w}` excluding
  `φ`; `w'` = seeded prime extension of `w.val ∪ {◇A|A∈u.val}` excluding `Σ={□B|B∉u.val}`. Rejected
  `⟨w, v⟩`: it demands `◇⊤ ∈ w` and is not provable from the base IK/CK axioms (report 02 resolves
  this as a red herring). Confirmed by ianshil/CK `general_th_completeness.v`.
- The set-exclusion lemma lives in Foundations `PrimeExclusion.lean` (generic, reusable by minimal/
  intuitionistic/modal layers), NOT buried in the modal layer. Rejected modal-layer placement:
  denies reuse to propositional intuitionistic completeness (report 02 Deliverable 4).
- `prime_exclusion` is NOT refactored to route through `prime_set_exclusion` (kept independent for
  zero blast radius; `bigOr [φ] = φ⊔⊥ ≠ φ`, so it is a corollary only modulo added hypotheses).
- `canonicalR` carries **both** a box clause and a diamond clause (`◇` primitive, not `□`-definable;
  Wijesekera/Simpson/ianshil-CK `cmreach`). Confirmed correct by the reference formalization — do
  not drop the diamond clause. This was validated at the Phase 2b blocker analysis.
- K◇ (`□(A→B)→(◇A→◇B)`) is a parametric `h_Kdia` hypothesis, discharged in a SEPARATE modal
  sub-lemma (`box_witness_pair_underivable`), NOT inside the generic infra lemma. Rejected folding
  it into `prime_set_exclusion`: conflates routine infra work with the delicate modal argument.
- `canonical_truth_lemma` is factored so each constructor case is a named helper taking the IH as an
  explicit hypothesis — the mechanism that lets 3a/3b/3c each build sorry-free before assembly.
- `h_efq` is SEPARATE and `botForces` is a truth-lemma parameter (not hard-coded `fun _ => False`),
  so minimal 495 / CK 493 instantiate without framework edits.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `box_witness_pair_underivable` (2b-sublemma) — the K◇ consistency argument — is delicate (disjunction property of `u` + K◇ chaining) | H | M | Isolated into its own phase with STOP contingency. Ground on ianshil/CK `Kd`/`K_rule` (`general_th_completeness.v`) and report 02 Deliverable 3. Verify goal shape with `lean_goal` before writing the body. |
| `canonical_diamond_witness` (2c) — mirror construction, primitive `◇` | H | M | Isolated into Phase 2c with STOP contingency; reuses `prime_set_exclusion` (seed box-side). Ground on report 02 Deliverable 3 tail + Wijesekera 1990. |
| `prime_set_exclusion` additive extension accidentally perturbs an existing `prime_exclusion` user (instance/notation churn) | H | L | Additive-only in a new `section [HasBot F]`; no existing signature changes (report 02 Deliverable 4 confirms). Verification runs FULL `lake build` (whole-tree) and confirms existing `prime_exclusion` users build. |
| `bigOr`/`List.append` `simp` normal forms need one or two `List.mem_append` lemmas | L | M | Routine (report 02 H4 item 2). Not a design risk; resolve with `lean_multi_attempt`. |
| Corrected pair-shaped witness not consumed correctly by `.box`/`.diamond` truth cases | M | M | 3b/3c must consume the `⟨w', u⟩` shape (outer `∀ w'≥w` from `BForces_box`). Confirm helper signatures against `BForces_*` unfolds with `lean_goal` before writing bodies. |
| Helper-factoring IH shapes (3a/3b/3c) may not match the recursion's available IH | M | M | Confirm each helper signature with `lean_multi_attempt`/`lean_goal` before writing bodies; assemble recursion (3c) only once all helpers typecheck. |
| `Birelational.lean` API drift vs report assumptions | M | L | Field names already confirmed in Phase 2a; re-confirm `BFrame.f1`/`f2` obligation shapes in 2d. |
| Lint failures (docBlame, lowerCamelCase, namespace) | M | M | Docstring every new `def`/`theorem`; run `lake exe lint-style` + `lake shake` at each phase end. |

## Implementation Phases

**Dependency Analysis (wave map)**:

| Wave | Phases | Blocked by | File(s) | Parallel-safe? |
|------|--------|-----------|---------|----------------|
| 0 | 1, 2a | -- | PrimeTheory.lean; CanonicalModel.lean (defs) | COMPLETED — preserved |
| 1 | 2-infra | -- (nothing new) | Foundations/PrimeExclusion.lean; references.bib | Yes (different file), but MUST precede 2b-sublemma/2b which depend on it |
| 2 | 2b-sublemma | 2-infra, 2a | CanonicalModel.lean | No |
| 3 | 2b | 2b-sublemma, 2-infra, 2a | CanonicalModel.lean | No (same file, sequential) |
| 4 | 2c | 2b, 2-infra | CanonicalModel.lean | No (same file, sequential) |
| 5 | 2d | 2b, 2c | CanonicalModel.lean | No (same file, sequential) |
| 6 | 3a | 2d | TruthLemma.lean | No |
| 7 | 3b | 3a | TruthLemma.lean | No (same file, sequential) |
| 8 | 3c | 3a, 3b | TruthLemma.lean | No (same file, sequential) |
| 9 | 4 | 3c | Completeness.lean | No |

**Wave structure is effectively sequential** for two structural reasons carried from v2:
(1) **Same-file phases must be applied sequentially** — 2b-sublemma/2b/2c/2d all write
`CanonicalModel.lean`, and 3a/3b/3c all write `TruthLemma.lean`; a Lean module is a single build
unit, so concurrent edits cannot each build green. (2) **Import chain** — `CanonicalModel` imports
`PrimeTheory` and (additively) uses `PrimeExclusion`; `TruthLemma` imports `CanonicalModel`;
`Completeness` imports `TruthLemma`.

The one genuine parallel opportunity is **2-infra**: it touches a *different* file
(`Foundations/PrimeExclusion.lean`) than the CanonicalModel work, so it is parallel-safe in
principle. But 2b-sublemma and 2b **depend on it** (they need `DerivExcludes`/`prime_set_exclusion`/
`modal_set_exclusion`), so it MUST be dispatched FIRST. **Dispatch order: 2-infra → 2b-sublemma →
2b → 2c → 2d → 3a → 3b → 3c → 4.**

Every phase below carries the same standing gates: **ZERO-DEBT** (`grep -nE "sorry|admit"` returns
nothing; no new `axiom`), **untouched-classical** (`git diff --stat` shows no change to `MCS.lean`,
classical `Completeness.lean`, propositional `Int*`, `PrimeTheory.lean`, Phase 2a `CanonicalModel`
definitions, or any *existing* decl in `PrimeExclusion.lean`), and **docstrings on all new public
declarations**.

### Phase 1: PrimeTheory.lean — prime-theory machinery [COMPLETED]

- **Goal:** (preserved) intuitionistic modal prime-theory layer wrapping `prime_exclusion`.
- **Deliverable:** `PrimeTheory.lean` (done — see Preserved Assets).
- **Depends on:** none. **Completed:** commit be8f2eb0. No action; do not modify.

### Phase 2a: CanonicalModel.lean — worlds, order, valuation, canonicalR [COMPLETED]

- **Goal:** (preserved) birelational canonical-frame data: worlds, `≤`=inclusion `Preorder`,
  `canonicalVal`, two-clause `canonicalR` — definitions only.
- **Deliverable:** `CanonicalModel.lean` definitions (done — see Preserved Assets).
- **Depends on:** 1. **Completed:** commit 4fd37213. No action; do not modify the committed defs.

### Phase 2-infra: prime_set_exclusion + bigOr helpers + Wijesekera1990 bib [COMPLETED]

- **Goal:** Add the generic set-exclusion (Lindenbaum-pair) infrastructure to Foundations, purely
  additively, and add the missing `Wijesekera1990` BibTeX entry. This unblocks Phase 2b.
- **Single deliverable:** `PrimeExclusion.lean` builds tree-wide with `prime_set_exclusion` (+
  helpers) added; `references.bib` has a `Wijesekera1990` entry; every existing `prime_exclusion`
  user still builds.
- **Tasks:**
  - [x] In a new `section` adding `variable [HasBot F]` in
        `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`, add (report 02 Deliverable 1):
        `bigOr : List F → F` (`bigOr [] = ⊥`; `bigOr (x::xs) = x ⊔ bigOr xs`),
        `DerivExcludes D Σ T := ∀ l, (∀ x∈l, x∈Σ) → bigOr l ∉ T`, and
        `SetExcludingSupersets D Cons S Σ`.
  - [x] Add the three NEW derivation lemmas from the `hOrI1/hOrI2/hOrE/hEFQ` empty-context schemas
        (NO new axiom): `bigOr_append_right`, `or_right_mono`, `bigOr_append_left` (report 02
        Deliverable 2). These mirror `PrimeTheory.lean`'s bespoke `DerivationTree` constructions.
        (Also added two small internal glue lemmas, `empty_imp_trans`/`empty_imp_id`, needed to
        compose empty-context implications via the generic `hCut` witness -- see Plan Deviations.)
  - [x] Add `set_excluding_base_mem`, `set_excluding_chain_union` (analogues of the existing
        `prime_excluding_*`; `deductivelyClosed_chain_union` reused UNCHANGED), and the one genuinely
        new argument `set_maximal_is_prime` (mirror of `prime_maximal_is_prime` with the fixed `φ`
        replaced by the per-branch finite disjunction `χ := bigOr (lₐ ++ l_b)`; inconsistent-`Cons`
        branch uses `lₓ := []`, `bigOr [] = ⊥`, `hEFQ`).
  - [x] State and prove `prime_set_exclusion` with the signature in report 02 Deliverable 1
        (`hS`, `h_excl : DerivExcludes D Σ S`, the `hOrI1/hOrI2/hOrE/hEFQ` schemas, the same
        `cl`/`cl_subset`/`cl_mem_imp`/`cl_admissible_of_cons`/`hCut`/`hConsChain` closure inputs
        `prime_exclusion` already takes, PLUS one additional justified hypothesis
        `bot_mem_cl_of_not_cons` -- see Plan Deviations) concluding
        `∃ T, S ⊆ T ∧ PrimeAdmissible D Cons T ∧ DerivExcludes D Σ T`.
  - [x] Add the `Wijesekera1990` entry to `references.bib`:
        `@article{Wijesekera1990, author={Wijesekera, Duminda}, title={Constructive Modal Logics I},
        journal={Annals of Pure and Applied Logic}, volume={50}, number={3}, pages={271--301},
        year={1990}}` (it is already cited textually in `CanonicalModel.lean`'s docstring).
  - [x] Docstring every new decl; do NOT touch `prime_exclusion` or any existing declaration.
- **Reference grounding:** report 02 Deliverables 1-2, 4; `ChagrovZakharyaschev1997` Lemma 5.5;
  ianshil/CK `Lindenbaum_pair`/`pair_extCKH_prv` (cite inline as URL comment).
- **Estimated output:** ~180-250 lines in `PrimeExclusion.lean` + ~6 lines in `references.bib`.
  **Actual:** 338 lines in `PrimeExclusion.lean` (incl. docstrings); 9 lines in `references.bib`.
- **Plan Deviations:**
  - Added `bot_mem_cl_of_not_cons : ∀ {X}, ¬ Cons X → HasBot.bot ∈ cl X` as an explicit hypothesis
    to `prime_set_exclusion`/`set_maximal_is_prime`, beyond report 02's literal Deliverable-1
    signature. This is the set-exclusion analogue of `prime_exclusion`'s
    `phi_mem_cl_of_not_cons` bridge, targeting the canonical `bigOr [] = ⊥` instead of a fixed
    `phi`. A fully generic `Cons : Set F → Prop` predicate cannot supply "inconsistent ⟹
    ⊥-derivable" for free; report 02's sketch ("insert X T ⊢ ⊥" in the inconsistent branch)
    implicitly needs this bridge. Trivially discharged at instantiation time exactly as
    `modal_prime_exclusion` discharges `phi_mem_cl_of_not_cons` (from the definition of
    `ModalSetConsistent`), so this does not block Phase 2b's `modal_set_exclusion` wrapper.
  - Added two small internal helper lemmas not named in the plan/report: `empty_imp_trans`
    (empty-context implication transitivity) and `empty_imp_id` (empty-context implication
    identity), both derived purely from `hCut`/`weakening`/`mp`/`assumption` -- the "small
    imp-transitivity/MP-composition glue" the report anticipated needing (Deliverable 2, final
    bullet) to compose the `bigOr` monotonicity steps.
- **Verification (targeted + full) -- all PASSED:**
  - Full `lake build` (whole-tree, 3190 jobs) succeeds.
  - Existing `prime_exclusion` users (`MinLindenbaum`, `IntLindenbaum`, `IntStrongCompleteness`,
    `Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory`) still build (whole-tree green).
  - `grep -nE "sorry|admit"` on `PrimeExclusion.lean` returns nothing; no new `axiom`.
  - `git diff --stat` on `PrimeExclusion.lean` shows only additive hunks (338 insertions,
    0 deletions; no existing declaration changed).
  - `lake exe lint-style`, `lake exe checkInitImports`, and `lake shake` (scoped) clean on the
    file/tree.
- **Done when:** `prime_set_exclusion` (+ helpers) typecheck sorry-free; whole tree builds green;
  existing decls byte-for-byte unchanged; `Wijesekera1990` in `references.bib`. **DONE.**
- **Timing:** ~2 hours. **Depends on:** none new (do FIRST after 2a; blocks 2b-sublemma/2b).

### Phase 2b-sublemma: box_witness_pair_underivable (K◇) [PARTIAL] — HIGHEST RISK

- **STOP CONTINGENCY INVOKED (dispatch `sess_1784011298_752245_480`)**: real, sustained effort was
  spent attempting a sorry-free proof of `box_witness_pair_underivable` using only the hypotheses
  scoped in this phase (`h_implyK/S`, `h_efq`, `h_orE/h_orI1/h_orI2`, `h_K`, `h_Kdia`). The proof
  genuinely resists closing with exactly these hypotheses, and — crucially — this was tracked down
  to a **concrete, citable counterexample to the report's H3 grounding claim**, not implementer
  error. Full detail in `.orchestrator-handoff.json` (`blockers[0]`) and the summary below. In
  short: the reference mechanization this phase is grounded on
  (`ianshil/CK`, `theories/Completeness_th/general_th_completeness.v`, Box case, lines ~211–249)
  proves the exact analogue of `box_witness_pair_underivable` using **not only** `Kd` (K◇, our
  `h_Kdia`) **but also** the Fischer-Servi axiom `Idb A B := (◇A → □B) → □(A → B)`
  (`theories/GHC/CKH.v:34`), invoked at line 231
  (`apply Ax ; right ; right ; eexists ; eexists ; right ; reflexivity`) to convert the derived
  fact `◇(⋀ dl') → □(list_disj l')` into `□(⋀dl' → list_disj l')` — precisely the step needed to
  then invoke `h_sub`/`{ψ|□ψ∈w}⊆u`. Report 02's claim that the sub-lemma "depends only on the
  axioms `AxiomK` and K◇" is **not supported by the very reference it cites**; the reference
  needs a THIRD hypothesis (`h_Idb`) that is absent from this phase's (and Phase 2b's) scoped
  hypothesis list. No amount of re-deriving from `h_Kdia`+`h_K`+`h_orE`+`h_efq` alone closes the
  multi-diamond-witness case (`m ≥ 1` uses of `{◇A|A∈u.val}` in a single derivation) without
  either (a) an `Idb`-shaped bridge hypothesis, or (b) conjunction (`h_andI`) to combine multiple
  diamond witnesses into one — neither of which this phase's settled design supplies.
- **Recommended next action**: re-plan (via `/revise 480` or `/research 480 --hard --lit`,
  narrowly scoped) to add `h_Idb : ∀ A B, Axioms (((◇A).imp (□B)).imp (□(A.imp B)))` as an
  explicit parametric hypothesis to `box_witness_pair_underivable`/`canonical_box_witness` (and
  check whether `canonical_diamond_witness`, Phase 2c, needs the dual `Cd A B := ◇(A∨B)→(◇A∨◇B)`
  as `h_Cd` — `Cd` did not appear in the Box case excerpt read this dispatch, but the diamond case
  was not re-read for it; verify before 2c). This is a genuine settled-design gap, not a re-litigation
  of an already-closed decision: the counterexample is the reference mechanization itself.
- **What was NOT done**: no code was written to `CanonicalModel.lean` (zero-debt: no sorry, no
  changed lines). Phase 2-infra's committed state (`PrimeExclusion.lean`, `references.bib`) is
  untouched and remains COMPLETED.

- **Goal:** Prove the modal consistency sub-lemma establishing the `DerivExcludes Σ Γ` precondition
  that Phase 2b's seeded-`w'` construction needs. This is the delicate K◇ argument.
- **Single deliverable:** `box_witness_pair_underivable` proved sorry-free in `CanonicalModel.lean`.
- **Tasks:**
  - [ ] Before writing the body, use `lean_goal`/`lean_multi_attempt` to confirm the goal shape:
        `DerivExcludes (modalDerivationSystem Axioms) Σ Γ` where `Γ = w.val ∪ {◇A | A ∈ u.val}` and
        `Σ = {□B | B ∉ u.val}`.
  - [ ] Prove it (report 02 Deliverable 3 "Where K◇ discharges…", transliterating ianshil/CK
        `Kd`/`K_rule`): suppose `Γ ⊢ □B₁ ⊔ … ⊔ □Bₙ` (each `Bᵢ ∉ u.val`); a finite subset uses
        `g₁,…,g_k ∈ w.val` and `◇A₁,…,◇A_m` with each `Aⱼ ∈ u.val`. Use `h_Kdia`
        (`□(A→B)→(◇A→◇B)`) to turn `□(Aⱼ → (B₁∨…∨Bₙ))` into `◇Aⱼ → ◇(B₁∨…∨Bₙ)`; combined with
        `{ψ|□ψ∈w} ⊆ u`, the disjunction property of the prime theory `u`, and `Bᵢ ∉ u.val`, force
        some `Bᵢ ∈ u.val` — contradiction. Depends only on `AxiomK` + K◇ + `u`'s primeness; NO
        `◇⊤`/seriality anywhere.
  - [ ] K◇ enters as the parametric hypothesis `h_Kdia : ∀ A B, Axioms ((□(A.imp B)).imp ((◇A).imp
        (◇B)))` (framework style; NO global `axiom`, NO new `Axioms.AxiomKDia` abbrev).
  - [ ] Docstring; `lake build` the module.
- **Reference grounding:** report 02 Deliverable 3; ianshil/CK `general_th_completeness.v` Box case.
- **Estimated output:** ~60-120 lines.
- **Verification:** `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` succeeds;
  `box_witness_pair_underivable` typechecks; `grep -nE "sorry|admit"` nothing; no new `axiom`;
  `git diff --stat` shows only `CanonicalModel.lean` changed (Phase 2a defs untouched above the new
  content); ZERO-DEBT + untouched-classical carried.
- **Done when:** module builds; the sub-lemma typechecks sorry-free.
- **Timing:** ~1.25 hours. **Depends on:** 2-infra (for `DerivExcludes`), 2a.
- **STOP / partial contingency:** If the K◇ argument cannot close sorry-free within the run,
  **STOP — do not introduce `sorry`.** Commit the sorry-free state (through 2-infra), mark this
  phase `[PARTIAL]`, write a continuation note (which sub-goal is stuck, exact `lean_goal` output,
  which K◇ instantiation failed) to the orchestrator handoff. Recommended next: `/research 480
  --hard --lit` narrowly on ianshil/CK `Kd`/`K_rule` transliteration before re-dispatch.

### Phase 2b: canonical_box_witness (corrected pair ⟨w', u⟩) [NOT STARTED]

- **Goal:** Prove the corrected box witness (a PAIR), plus the thin `modal_set_exclusion` wrapper it
  needs. This replaces the v2 `[BLOCKED]` Phase 2b.
- **Single deliverable:** `canonical_box_witness` proved sorry-free in `CanonicalModel.lean` with the
  corrected statement, plus `modal_set_exclusion` placed in `CanonicalModel.lean`.
- **Corrected statement (SETTLED, report 02 Deliverable 3):**
  `∃ w' u : CanonicalPrimeWorld Axioms, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val` — NOT the old
  `∃ v, canonicalR w v ∧ φ∉v.val`.
- **Tasks:**
  - [ ] Add `modal_set_exclusion` to `CanonicalModel.lean` (NOT `PrimeTheory.lean` — no-touch rule),
        mirroring `modal_prime_exclusion`: supply `Cons := ModalSetConsistent Axioms`,
        `cl := modalDeductiveClosure Axioms`, `hOrI1/hOrI2` from `Axioms.OrI1/OrI2`, `hEFQ` from
        `h_efq`, and the same `hConsChain` closure (report 02 Deliverable 4). ~40 lines.
  - [ ] **Step 1** (reuse the v2 already-`[x]` result): `u := ` prime extension via
        `modal_prime_exclusion` of `{ψ | □ψ ∈ w.val}` excluding `φ`. Requires that set admissible
        (deductive closure via the deductively-closed variant of `derive_box_from_box_context`;
        `φ ∉ closure` from `□φ ∉ w.val`). Gives `{ψ|□ψ∈w.val} ⊆ u.val`, `φ ∉ u.val`.
  - [ ] **Step 2**: `w' := ` prime extension via `modal_set_exclusion` of
        `Γ := w.val ∪ {◇A | A ∈ u.val}` **excluding** `Σ := {□B | B ∉ u.val}`. Discharge its
        `DerivExcludes Σ Γ` precondition with `box_witness_pair_underivable` (Phase 2b-sublemma).
  - [ ] Discharge the three witness obligations **by construction** (report 02 Deliverable 3):
        `w ≤ w'` (`w.val ⊆ Γ ⊆ w'.val`); diamond clause `∀ψ∈u.val, ◇ψ∈w'.val` (seeding); box clause
        `∀ψ, □ψ∈w'.val → ψ∈u.val` (contrapositive via `DerivExcludes` on `l := [□ψ]`); `φ ∉ u.val`
        (Step 1). Verify each with `lean_goal` before committing.
  - [ ] Docstring; `lake build` the module.
- **Reference grounding:** report 02 Deliverable 3; ianshil/CK Box case; `Simpson1994` Ch.3.
- **Estimated output:** ~120-180 lines (incl. the ~40-line wrapper).
- **Verification:** module builds; `canonical_box_witness` typechecks with the corrected pair
  statement; `modal_set_exclusion` typechecks; ZERO-DEBT (`grep` nothing, no new `axiom`);
  untouched-classical (`git diff --stat`: `PrimeTheory.lean` unchanged, Phase 2a defs unchanged).
- **Done when:** module builds; the pair-shaped `canonical_box_witness` typechecks sorry-free.
- **Timing:** ~1.5 hours. **Depends on:** 2b-sublemma, 2-infra, 2a.

### Phase 2c: canonical_diamond_witness (mirror construction) [NOT STARTED] — HIGHEST RISK

- **Goal:** Prove the diamond witness lemma, RE-EXAMINED in light of the set-exclusion infra: like
  the box witness, it likely ALSO needs `prime_set_exclusion` / a seeded construction (report 02
  Deliverable 3 tail: "the mirror image — seed the *box*-side and exclude a diamond-set").
- **Single deliverable:** `canonical_diamond_witness` proved sorry-free in `CanonicalModel.lean`.
- **Updated sketch (report 02 Deliverable 3 tail — supersedes v2's single-`prime_exclusion` sketch):**
  from `◇φ ∈ w`, build the mirror pair via `modal_set_exclusion`: seed the box-side and exclude a
  diamond-set, so the same `prime_set_exclusion` covers it. Expect a pair-shaped result analogous to
  the box witness (confirm exact shape with `lean_goal` against `BForces_diamond` + F1's needs in 2d
  before committing). A diamond-side analogue of `box_witness_pair_underivable` may be required for
  the seeding-consistency precondition — check with `lean_goal` first; if needed, prove it inline
  under this phase's STOP contingency.
- **Tasks:**
  - [ ] Before writing, use `lean_goal`/`lean_multi_attempt` to confirm the goal shape and whether a
        mirror consistency sub-lemma is needed for the seeded exclusion.
  - [ ] Prove `canonical_diamond_witness` via the mirror `modal_set_exclusion` construction — report
        02 Deliverable 3 tail; Report 01 §6.5, §10; Wijesekera 1990.
  - [ ] Docstring; `lake build` the module.
- **Estimated output:** ~120-200 lines.
- **Verification:** module builds; `canonical_diamond_witness` typechecks; ZERO-DEBT; untouched-
  classical carried (`git diff --stat`).
- **Done when:** module builds; the diamond witness typechecks sorry-free.
- **Timing:** ~1.5 hours. **Depends on:** 2b (same file, sequential), 2-infra.
- **STOP / partial contingency:** If the diamond witness cannot close sorry-free within the run,
  **STOP — do not introduce `sorry`.** Commit the sorry-free state (through 2b), mark `[PARTIAL]`,
  write a continuation note (stuck sub-goal, `lean_goal` output, whether the mirror consistency
  sub-lemma is the obstruction) to the handoff. Recommended next: `/research 480 --hard --lit`
  narrowly on the Wijesekera prime-filter diamond-accessibility construction / ianshil/CK diamond
  case before re-dispatch.

### Phase 2d: canonical_f1 + canonical_f2 [NOT STARTED]

- **Goal:** Prove the two frame conditions, completing `CanonicalModel.lean`.
- **Single deliverable:** `canonical_f1` and `canonical_f2` proved; `CanonicalModel.lean` final.
- **Tasks:**
  - [ ] Prove `canonical_f1` (up-confluence): transport a diamond witness (2c) along inclusion —
        Report 01 §6.6. Consume the pair-shaped diamond witness correctly.
  - [ ] Prove `canonical_f2` (down-confluence): via the box witness (2b) — Report 01 §6.6. Consume
        the pair-shaped box witness (`⟨w', u⟩`) correctly.
  - [ ] Confirm both typecheck against the `BFrame.f1`/`BFrame.f2` obligation shapes (re-read from
        `Birelational.lean` if needed).
  - [ ] Docstrings; `lake build` the module.
- **Estimated output:** ~80-140 lines.
- **Verification:** module builds; both frame conditions match `BFrame` obligations; ZERO-DEBT;
  untouched-classical carried.
- **Done when:** module builds; both frame conditions typecheck sorry-free.
- **Timing:** ~1 hour. **Depends on:** 2b, 2c.

### Phase 3a: TruthLemma.lean — 5 non-modal case helpers [NOT STARTED]

- **Goal:** Create `TruthLemma.lean` and prove the five non-modal truth-lemma cases as standalone
  helper lemmas.
- **Design note (SETTLED):** Each case is a named helper lemma. Cases needing the IH (`and`/`or`/
  `imp`) take the relevant IH as an **explicit hypothesis parameter**. This lets 3a build green
  before the full recursion exists (assembled in 3c). Confirm each signature with `lean_goal`.
- **Single deliverable:** `TruthLemma.lean` builds green containing the five helpers.
- **Tasks:**
  - [ ] Create `TruthLemma.lean` importing `CanonicalModel.lean` (Phase 2).
  - [ ] Transliterate `atom`/`bot`/`and`/`or`/`imp` line-for-line from
        `IntStrongCompleteness.lean:108-214` (`PL.Proposition`→`Modal.Proposition`,
        `IntPropAxiom`→`Axioms`) into helper lemmas; keep `botForces` a parameter (NOT hard-coded).
        Explicit `DerivationTree` term-mode style; no `simp`/`aesop`.
  - [ ] Docstrings; `lake build` the module.
- **Estimated output:** ~150-250 lines.
- **Verification:** module builds; five helpers typecheck; `botForces` a parameter; ZERO-DEBT;
  untouched-classical carried.
- **Done when:** module builds; five helpers typecheck sorry-free.
- **Timing:** ~1.25 hours. **Depends on:** 2d.

### Phase 3b: .box case helper [NOT STARTED]

- **Goal:** Prove the `.box` truth-lemma case as a helper lemma, consuming the corrected pair-shaped
  box witness.
- **Single deliverable:** `truth_box_case` (or equivalent) proved sorry-free in `TruthLemma.lean`.
- **Tasks:**
  - [ ] Prove the `.box` helper using `canonical_box_witness` (2b) — consume the `⟨w', u⟩` PAIR:
        `BForces_box` unfolds to `∀ w'≥w, ∀ u, r w' u → force u φ`, so the outer `∀ w'≥w` is
        load-bearing and matches the witness's `w ≤ w'` (report 02 Deliverable 3). Heredity over
        `≤∘R`. Take the IH as an explicit hypothesis (3a design note).
  - [ ] Docstring; `lake build` the module.
- **Estimated output:** ~60-120 lines.
- **Verification:** module builds; box helper typechecks consuming the pair witness; ZERO-DEBT;
  untouched-classical carried.
- **Done when:** module builds; box helper typechecks sorry-free.
- **Timing:** ~0.75 hour. **Depends on:** 3a.

### Phase 3c: .diamond case helper + assemble canonical_truth_lemma [NOT STARTED] — HIGHEST RISK

- **Goal:** Prove the `.diamond` truth-lemma case (consuming the pair-shaped diamond witness), then
  assemble the full parametric `canonical_truth_lemma` dispatching to all seven helpers.
- **Single deliverable:** `truth_diamond_case` proved and `canonical_truth_lemma` assembled
  sorry-free; `TruthLemma.lean` final.
- **Tasks:**
  - [ ] Before writing, confirm the diamond helper goal shape with `lean_goal` (`BForces_diamond`
        unfold; IH over `R`; consume the pair-shaped `canonical_diamond_witness`).
  - [ ] Prove the `.diamond` helper using `canonical_diamond_witness` (2c) — Report 01 §6.7, §10;
        Wijesekera 1990.
  - [ ] Assemble `canonical_truth_lemma` by induction on `Proposition`, dispatching each constructor
        to its helper (3a/3b + this). Confirm all seven constructors covered (no missing-case
        warning). Mechanical once all helpers typecheck.
  - [ ] Docstrings; `lake build` the module.
- **Estimated output:** ~100-180 lines.
- **Verification:** module builds; `canonical_truth_lemma` covers all seven constructors; `botForces`
  still a parameter; ZERO-DEBT; untouched-classical carried.
- **Done when:** module builds; `canonical_truth_lemma` typechecks sorry-free over all constructors.
- **Timing:** ~1 hour. **Depends on:** 3a, 3b.
- **STOP / partial contingency:** If the diamond case cannot close sorry-free, **STOP — do not
  introduce `sorry`.** Commit the sorry-free state (3a+3b helpers), mark `[PARTIAL]`, write a
  continuation note (stuck sub-goal, `lean_goal` output) to the handoff; the `canonical_truth_lemma`
  assembly defers with it. Recommended next: narrow `/research 480 --hard --lit` on the Wijesekera
  `.diamond` forcing clause before re-dispatch.

### Phase 4: Completeness.lean — parametric packaging [NOT STARTED]

- **Goal:** Package the canonical `BModel` and expose parametric `ivalid`/`mvalid` completeness plus
  the consistency hook for tasks 492-495.
- **Single deliverable:** `Completeness.lean` builds green; full CI pipeline passes.
- **Tasks:**
  - [ ] Create `Completeness.lean` importing `TruthLemma.lean` (Phase 3).
  - [ ] Assemble the canonical `BModel` from `CanonicalPrimeWorld`, the `Preorder`, `canonicalR`,
        `canonicalVal`, and `canonical_f1`/`f2`.
  - [ ] State parametric `ivalid_completeness` / `mvalid_completeness` (from `canonical_truth_lemma`
        + `modal_prime_exclusion` on the underivable formula) with base-axiom + `h_efq` (IValid) /
        arbitrary-`botForces` (MValid) hypotheses exposed for 492-495 — Report 01 §7. Note: the
        underivable-formula witness step now has the option of `prime_set_exclusion` too if a set is
        needed, but single-formula `modal_prime_exclusion` suffices for the standard completeness
        statement.
  - [ ] Expose a consistency hook (parametric statement, discharged by 492/493, not here) — §10.
  - [ ] Docstrings; `lake build`; run the full CI pipeline; confirm ZERO-DEBT + untouched-classical.
- **Estimated output:** ~80-150 lines.
- **Verification:** module builds; `ivalid_completeness`/`mvalid_completeness` typecheck as
  parametric statements; full CI green; ZERO-DEBT; untouched-classical carried.
- **Done when:** module builds; both completeness statements typecheck; full CI green.
- **Timing:** ~1.25 hours. **Depends on:** 3c.

## Testing & Validation

- [ ] `lake build` succeeds tree-wide (Foundations `PrimeExclusion.lean` extension + all four
      `Intuitionistic/` modules green).
- [ ] All existing `prime_exclusion` users still build (whole-tree green).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (all new decls docstringed).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused-import issues on the
      new/extended files.
- [ ] ZERO-DEBT: `grep -rnE "sorry|admit" Cslib/Logics/Modal/Metalogic/Intuitionistic/` and
      `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` return nothing; no new `axiom`
      declarations (K◇ is a parametric `h_Kdia` hypothesis, not a global axiom).
- [ ] Additive-only in Foundations: `git diff Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`
      shows only new hunks; no existing declaration modified.
- [ ] Untouched-classical: `git diff --stat` shows no changes to `MCS.lean`, classical
      `Completeness.lean`, propositional `Int*` files, `PrimeTheory.lean` (be8f2eb0), or Phase 2a
      `CanonicalModel.lean` definitions (4fd37213, other than appended witness content).
- [ ] `references.bib` contains a well-formed `Wijesekera1990` entry.
- [ ] Parametricity: each new framework lemma carries `Axioms` + explicit `h_*` base-axiom
      hypotheses (incl. `h_Kdia`) with `h_efq` separable and `botForces` a parameter.

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (Phase 2-infra, additive extension)
- `references.bib` (Phase 2-infra, `Wijesekera1990` entry)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (Phase 1, preserved)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (Phase 2a preserved; Phases
  2b-sublemma/2b/2c/2d append witnesses + `modal_set_exclusion`)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (Phases 3a-3c)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean` (Phase 4)
- `specs/480_intuitionistic_modal_framework/plans/03_intuitionistic-modal-framework-hard-v3.md` (this)
- `specs/480_intuitionistic_modal_framework/summaries/03_intuitionistic-modal-framework-summary.md`
  (on completion)

## Rollback/Contingency

- All modal work is additive under `Intuitionistic/`; the Foundations change is additive-only.
  Rollback = revert the new/appended content; no regression risk to existing proofs.
- **Per-phase STOP rule (ZERO-DEBT):** any phase that cannot reach a sorry-free build STOPS, commits
  the last green state, marks itself `[PARTIAL]`, records a continuation note. Never commit
  `sorry`/`admit`/`axiom`. The two HIGHEST-RISK phases (2b-sublemma, 2c) and the diamond truth case
  (3c) carry explicit narrow-research fallbacks (see their STOP contingencies).
- **If Phase 2-infra's additive change perturbs an existing `prime_exclusion` user** (whole-tree
  build fails on a file outside the new subtree), STOP — do not patch the perturbed user. Report the
  perturbation; the change is supposed to be purely additive (report 02 confirms), so any breakage
  is a signal the addition touched shared state and must be redesigned, not worked around.
- If `Birelational.lean` API diverges materially from report assumptions, mark the task `[BLOCKED]`
  on task 490 rather than reconstructing the semantics here.
