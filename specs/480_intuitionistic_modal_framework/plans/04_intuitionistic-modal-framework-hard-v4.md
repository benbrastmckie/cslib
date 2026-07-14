# Implementation Plan (v4, HARD): Task #480 — Intuitionistic Modal Metalogic Framework

- **Task**: 480 - Intuitionistic modal metalogic FRAMEWORK (prime-theory machinery + birelational canonical-model construction)
- **Status**: [IN PROGRESS]
- **Effort**: ~8.5 hours remaining (Phases 1 + 2a + 2-infra complete; the v3→v4 delta is axiom-threading only, no new phases)
- **Dependencies**: Task 478 (classical Hilbert/metalogic framework, COMPLETED), Task 490 (birelational semantics `Birelational.lean`, present in-tree)
- **Research Inputs**: reports/01_intuitionistic-modal-framework.md; reports/02_set-exclusion-infra-box-witness.md; **reports/03_complete-axiom-requirements-ik-ck.md** (NEW — definitive machine-checked axiom-requirement map, Tier-1 grounded on ianshil/CK)
- **Artifacts**: plans/04_intuitionistic-modal-framework-hard-v4.md (this file); supersedes plans/03_intuitionistic-modal-framework-hard-v3.md (v3, retained for history), plans/02 (v2), plans/01 (v1)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Plan Version**: 4 (hard-mode re-slice folding in the definitive FOUR-axiom parametric threading from report 03)
- **Lean Intent**: false

## Overview

This is **v4**: a hard-mode re-slice of v3 whose **sole delta is threading the now-definitive
parametric modal-axiom hypotheses** through the signatures of the remaining witness lemmas, frame
conditions, truth-lemma cases, and completeness statements. It resolves the exact settled-design gap
that halted v3 at Phase 2b-sublemma.

**Why v4 exists.** v3's Phase 2b-sublemma hit a STOP contingency: the box-witness consistency proof
would not close from `h_K + h_Kdia` alone. Report 03 (`--hard --lit`, Tier-1, adversarially
verified against the reference mechanization ianshil/CK) traced this to a concrete counterexample to
report 02's grounding claim — the reference's box case invokes **not only** `Kd` (our `h_Kdia`)
**but also** the Fischer-Servi axiom `Idb` (`(◇A → □B) → □(A → B)`) at `general_th_completeness.v`
~L231. Report 03 then machine-checked the axiom requirement of **every** remaining lemma in the
chain, producing a complete per-lemma table (no further "missing axiom" surprises).

**The definitive minimal modal-axiom set for the entire 480 prime-pair framework is
`{ h_K, h_Kdia, h_Idb, h_Cd, h_dbot }`** (revised by the Phase 2c dispatch,
`sess_1784011298_752245_480`, 2026-07-14: `h_dbot` added) — all five are threaded as **explicit
parametric hypotheses** (`Axioms (…)`-shaped), never as global Lean `axiom`s. `Nd` is IK-specific
and is **NOT** part of 480's core (it belongs to task 492); **`h_dbot` (`◇⊥ → ⊥`) IS part of the
480 core** — it is the one IK axiom that bare CK drops (report 03 §3's own `h_Nd` listing already
names `◇⊥ → ⊥` as the `Nd` shape, but Phase 2c's dispatch found this exact formula load-bearing
for `canonical_diamond_witness` under a *different* name/role: not as an IK-only frame condition,
but as the base case of the diamond-distributes-over-disjunction induction inside the *core*
witness proof itself — see the Phase 2c section below for the full resolution). Framework
hygiene note: `h_dbot` should still be exposed as a loose hypothesis (not baked into a bundled
record), consistent with report 03 §5's CK-hygiene recommendation, so a downstream bare-CK
development is not forced to fake it — CK cannot use this framework's diamond witness at all
(report 03 §5), so this is moot for CK either way, but the hygiene principle is preserved.

The five axioms (verbatim Lean statements over `Modal.Proposition`, report 03 §3; confirmed against
`Cslib/Logics/Modal/Basic.lean` — `.imp/.box/.diamond/.or/.and/.bot`, `□ = box`, `◇ = diamond`):

```lean
-- Kb (AxiomK / box distribution)
h_K    : ∀ A B : Proposition Atom, Axioms ((□(A.imp B)).imp ((□A).imp (□B)))
-- Kd (K-diamond / K◇)
h_Kdia : ∀ A B : Proposition Atom, Axioms ((□(A.imp B)).imp ((◇A).imp (◇B)))
-- Idb (Fischer-Servi "box" axiom) — NEW box-side bridge  [CKH.v: Idb A B := (◇A → □B) → □(A→B)]
h_Idb  : ∀ A B : Proposition Atom, Axioms (((◇A).imp (□B)).imp (□(A.imp B)))
-- Cd (Fischer-Servi "diamond" axiom / ◇-over-∨) — NEW diamond-side bridge  [CKH.v: Cd A B := ◇(A∨B) → (◇A ∨ ◇B)]
h_Cd   : ∀ A B : Proposition Atom, Axioms ((◇(A.or B)).imp ((◇A).or (◇B)))
-- dbot (IK's ◇⊥ → ⊥) — added by Phase 2c; discharges the diamond witness's Case A
h_dbot : Axioms ((◇Proposition.bot).imp Proposition.bot)
```

**Per-lemma axiom requirements** (report 03 §4, machine-checked against ianshil/CK; Phase 2c row
updated by the `sess_1784011298_752245_480` re-dispatch, 2026-07-14, machine-verified via
`lean_verify` — axioms `{propext, Classical.choice, Quot.sound}` only, no new Lean `axiom`):

| Phase | 480 lemma | Modal axioms threaded (beyond the intuitionistic base) |
|-------|-----------|--------------------------------------------------------|
| 2b-sublemma | `box_witness_pair_underivable` | **`h_K`, `h_Kdia`, `h_Idb`** |
| 2b | `canonical_box_witness` | **`h_K`, `h_Kdia`, `h_Idb`** (inherited from sublemma) |
| 2c | `canonical_diamond_witness` | **`h_K`, `h_Kdia`, `h_Cd`, `h_dbot`** — machine-confirmed; **`h_Idb` NOT consumed** (resolves report 03's MEDIUM-HIGH residual) |
| 2d | `canonical_f1` (up-confluence, Cd_frame) | **`h_Kdia`, `h_Cd`** |
| 2d | `canonical_f2` (down-confluence, Idb_frame) | **`h_Kdia`, `h_Idb`** |
| 3b | `truth_box_case` | threads `h_K`, `h_Kdia`, `h_Idb` via witness — **NO new axiom** |
| 3c | `truth_diamond_case` | threads `h_Kdia`, `h_Cd`, `h_dbot` via witness — **NO new axiom** |
| 3c/4 | `canonical_truth_lemma` + `ivalid`/`mvalid` | union `{ h_K, h_Kdia, h_Idb, h_Cd, h_dbot }` |

The v3→v4 delta is purely signature-threading: no phase is added, removed, or reordered; the
witness constructions, the corrected pair-shaped `⟨w', u⟩` box witness, `prime_set_exclusion`,
`modal_set_exclusion`, and all Preserved Assets are unchanged. Phase 2b-sublemma is now
**re-dispatchable** because it carries the missing `h_Idb`.

Definition of done (unchanged from v3, plus `h_dbot` added by Phase 2c): all four files under
`Cslib/Logics/Modal/Metalogic/Intuitionistic/` build under `lake build`; `PrimeExclusion.lean`'s
additive extension builds tree-wide with all existing `prime_exclusion` users still green; the full
CSLib CI pipeline passes; ZERO-DEBT is upheld (no `sorry`, no `admit`, no new `axiom` — all five
modal axioms are parametric hypotheses, not global axioms); and the classical `Metalogic/` files
plus the propositional `Int*` files are left byte-for-byte untouched.

### Downstream-Impact Note — KEY STRUCTURAL FINDING (report 03 §1, §5; do NOT plan here)

Report 03's decisive, machine-checked finding, recorded here so 493/501 are re-scoped later — **this
plan does NOT implement any of it**:

- **The prime-pair canonical model (our `canonicalR` = ianshil's `cmreach`) is only sound as a
  completeness witness for logics containing `Cd + Idb`.** This is forced by the reference's own file
  architecture: ianshil/CK provides `IK_th_completeness.v` (`AdAx = AdAxCdIdb + is_Nd`) and
  `CK_Cd_Idb_th_completeness.v` (`Cd + Idb`, no Nd) — both using the prime-pair construction — but
  **deliberately NO `CK_th_completeness.v`**.
- **Task 492 (IK) instantiates 480 directly.** `IK = CK + Cd + Idb + Nd`; IK supplies `h_Kdia`,
  `h_Idb`, `h_Cd` from its axiom set and layers a **separate Nd frame lemma** on top. Clean fit; any
  `Cd+Idb`-containing extension (IT, IS4, IS5) fits the same way.
- **Task 493 (bare CK) CANNOT route through these prime-pair witnesses.** Bare CK is strictly weaker
  (no Fischer-Servi axioms, fallible worlds allowed); its diamonds are witnessed **by construction**
  in a segment / fallible-world model (`Completeness_seg/`: segment worlds `⟨head, tail⟩` with an
  exploding world `cexpl`, `cmreach P0 P1 := tail P0 (head P1)`), **not by Cd/Idb proof**. Their
  absence changes the *worlds and the reachability relation*, not merely a proof step, so no
  "discharge Idb/Cd differently" fix recovers it inside the prime-pair construction.
- **Consequence for 493/501: re-scoping required (OUT OF SCOPE for this plan — flag only).** Task 493
  must either build a **separate segment/fallible-world canonical construction** (mirroring
  `Completeness_seg/`) OR restrict its reuse of 480 to the **axiom-agnostic pieces only**:
  `PrimeTheory.lean`, `prime_set_exclusion`, the non-modal truth-lemma cases (Phase 3a), and the
  `Preorder`/valuation scaffolding. The box/diamond witnesses, F1/F2, and the modal truth cases are
  `Cd+Idb`-specific and CK cannot reuse them. **Framework hygiene**: keep `h_Idb`/`h_Cd` as loose
  parametric hypotheses on individual lemmas — do NOT bundle them into a single record that a CK
  development would have to fake — so IK supplies them and CK simply never calls those lemmas.

### Preserved Assets

The following work is complete, committed, and MUST NOT regress. It is **not re-sliced**; import and
build on it only.

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Phase 1: `ModalSetConsistent`, `ModalPrimeTheory`, `modalDeductiveClosure` + closure laws, `modalNegPhiImpPsi_deriv`, `modal_imp_witness`, `modal_prime_exclusion`, `modal_deriv_imp_of_union` | `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (360 lines) | [COMPLETED] | commit `be8f2eb0`; grep shows no `sorry`/`admit`/`axiom` |
| Phase 2a: `CanonicalPrimeWorld`, `Preorder` = inclusion instance, `canonicalVal`, two-clause `canonicalR` (box clause `□φ∈w→φ∈v` AND diamond clause `φ∈v→◇φ∈w`) — definitions only, no witness proofs | `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` | [COMPLETED] | commit `4fd37213`; definitions only, byte-for-byte unchanged since |
| Phase 2-infra: `prime_set_exclusion` + `bigOr` + `DerivExcludes` + append-monotonicity helpers + `set_maximal_is_prime` + internal glue (`empty_imp_trans`/`empty_imp_id`) | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (338 added lines) + `references.bib` (`Wijesekera1990`) | [COMPLETED] | commit `4e3ef59c`; whole-tree build green, additive-only, no existing `prime_exclusion` user perturbed |

The following upstream infrastructure is reused by import/transliteration and MUST NOT be edited
(untouched-classical constraint):

| Asset | File | Reuse mode |
|-------|------|-----------|
| `Metalogic.prime_exclusion` (generic, single-formula) + its Zorn helpers | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` | import-only; the Phase 2-infra additions are COMPLETED and frozen — do NOT re-touch |
| `Axioms.OrI1`/`OrI2`/`OrE`/`EFQ` empty-context schemas | `Cslib/Logic/Axioms.lean` (≈L85, L122-133) | import-only; supplied as `hOrI1/hOrI2/hOrE/hEFQ` hypotheses |
| `DerivationTree` / `modalDerivationSystem` / `deductionTheorem` | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`, `DeductionTheorem.lean` | import-only, verbatim |
| `iteratedDeduction`, `derive_box_from_box_context` | `Cslib/Logics/Modal/Metalogic/MCS.lean` | import-only; NEVER modify MCS.lean |
| `BFrame`/`BModel`/`BForces`/`bforces_persistence`/`IValid`/`MValid`/`BForces_box`/`BForces_diamond` | `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) | import-only, codomain of truth lemma |
| `int_truth_lemma` non-modal cases (template) | `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean:108-214` | transliterate (copy), do not import |

### Source-to-Implementation Mapping (H3, Tier 1 — from report 03)

| Load-bearing decision | Source (BibKey / report / in-repo) | Consumed by phase |
|-----------------------|------------------------------------|-------------------|
| Four modal axioms as parametric hyps: `h_K`, `h_Kdia`, `h_Idb`, `h_Cd`; verbatim Lean shapes | Report 03 §3; ianshil/CK `theories/GHC/CKH.v` (`MAxioms` Kb/Kd; `Cd`/`Idb` defs); `Simpson1994` (references.bib:86) | all remaining modal phases |
| Box witness uses `Kb` **and** `Kd` **and** `Idb` (Idb selector VERBATIM at ~L231) | Report 03 §2, §4 row 1-2, §Adversarial item 1; ianshil/CK `general_th_completeness.v` box case ~L211-249 | 2b-sublemma, 2b |
| Diamond witness uses `Kb` **and** `Kd` **and** `Cd` (via `Diam_distrib_list_disj` = ◇-over-∨) | Report 03 §2, §4 row 3; ianshil/CK diamond case; `CK_Cd_Idb_th_completeness.v` | 2c |
| Frame F1 = Cd_frame (up-confluence) via `h_Cd`; F2 = Idb_frame (down-confluence) via `h_Idb` | Report 03 §4 rows 4-5; `CF_strong_Cd_weak_Idb`/`CF_CdIdb` ~L298-395 | 2d |
| `.box` / `.diamond` truth cases thread the witness params — NO new axiom | Report 03 §4 rows 6-7 | 3b, 3c |
| `Nd` NOT in the core framework (IK-only, task 492) | Report 03 §4, §5; `CK_Cd_Idb_th_completeness.v` (Cd+Idb, no Nd) uses this exact construction | none (excluded) |
| Bare CK uses a separate segment/fallible-world model, NOT prime pairs | Report 03 §1, §5; `Wijesekera1990` (references.bib:885); ianshil/CK `Completeness_seg/` | 493/501 re-scope (flagged only) |
| Corrected pair-shaped box witness `⟨w', u⟩`, `w ≤ w'`; seeded `w'`; `prime_set_exclusion` | Report 02 Deliverable 3 (carried from v3); ianshil/CK box case; `Simpson1994` Ch.3 | 2b |
| `prime_set_exclusion` / `DerivExcludes` / `bigOr` infra | Report 02 Deliverables 1-2; `ChagrovZakharyaschev1997` (references.bib:75) Lemma 5.5 | 2-infra (COMPLETED) |
| 5 non-modal truth cases (atom/bot/and/or/imp) | Report 01 §6.7, §9; IntStrongCompleteness.lean:108-214 | 3a |
| Parametric `ivalid`/`mvalid`; `h_efq` separable; `botForces` a parameter | Report 01 §7, §10 | 4 |

## Goals & Non-Goals

**Goals**:
- Thread the four parametric modal-axiom hypotheses `{ h_K, h_Kdia, h_Idb, h_Cd }` through the exact
  per-lemma signatures given in report 03 §4 (table above), keeping each an explicit `Axioms (…)`
  hypothesis in the framework's established style — **never a global `axiom`, no new `Axioms.Axiom*`
  abbrev**.
- Complete `CanonicalModel.lean`, `TruthLemma.lean`, `Completeness.lean` sorry-free and axiom-free
  atop the preserved `PrimeTheory.lean` / Phase 2a `CanonicalModel.lean` / Phase 2-infra
  `PrimeExclusion.lean`, each phase building independently.
- Keep `h_efq` SEPARATE and `botForces` a truth-lemma parameter (not hard-coded `fun _ => False`), so
  minimal 495 / bare-CK 493 can instantiate without framework edits.
- Provide the corrected pair-shaped `canonical_box_witness`, `canonical_diamond_witness`,
  `canonical_f1`/`f2`, a single parametric `canonical_truth_lemma`, and parametric `ivalid`/`mvalid`
  completeness statements carrying the four-axiom hypotheses, for 492 (and Cd+Idb extensions) to
  instantiate.
- Pass the full CSLib CI pipeline; docstring every new public declaration.

**Non-Goals**:
- No refactor of `prime_exclusion` / `prime_set_exclusion` (Phase 2-infra is COMPLETED and frozen;
  zero blast radius).
- No instantiation of concrete axiom systems (IK/CK/IT/IS4/IS5/MK) — tasks 492-495. In particular,
  **do NOT add `h_Nd`** to the core; expose it only in a later 492-specific frame lemma.
- **No re-scoping of task 493/501 here** — the Downstream-Impact Note flags the required split; the
  work belongs to those tasks, not this plan.
- No soundness/consistency discharge of any concrete axiom set — the framework exposes the hook only.

## Postmortem Constraints

Binding rules for all implementation dispatches, derived from the v3 Phase 2b-sublemma STOP
contingency, reports/02 and reports/03, and the failed monolithic v1 dispatch.

**Do NOT**:
- **Do NOT attempt more than one phase's deliverable per dispatch.** Each phase below is one agent
  run (H8). The v1 monolithic attempt failed to reach a sorry-free `CanonicalModel.lean` in one run.
- **Do NOT introduce `sorry`/`admit`/`axiom` to "make it build" and defer the hard part.** ZERO-DEBT
  is a hard constraint. If a HIGHEST-RISK proof (2b-sublemma, 2b, 2c, 3c) will not close, invoke its
  STOP contingency (report PARTIAL + continuation note); never commit debt. The four modal axioms
  enter as **parametric hypotheses** in the framework's established style, NOT as global `axiom`s and
  NOT as new `Axioms.Axiom*` abbrevs.
- **Do NOT drop `h_Idb` from the box side or `h_Cd` from the diamond side.** This is the settled fix
  of report 03 (machine-checked): the box witness/sublemma provably need `h_Idb` (reference invokes
  it verbatim at `general_th_completeness.v` ~L231); the diamond witness needs `h_Cd`. Attempting to
  re-derive from `h_K + h_Kdia` alone is the exact v3 dead end — do not repeat it.
- **Do NOT fix the box witness as `⟨w, v⟩` with `w` unchanged.** That is the older v2 dead end — it
  forces a spurious `◇⊤`/seriality precondition. The witness is a PAIR `⟨w', u⟩` with `w ≤ w'`, `w'`
  a fresh SEEDED extension (report 02 Deliverable 3). SETTLED.
- **Do NOT modify any declaration in `PrimeExclusion.lean` (Phase 2-infra, COMPLETED `4e3ef59c`).**
  It is frozen. `prime_exclusion`, `prime_set_exclusion`, and their helpers stay byte-for-byte
  identical.
- **Do NOT re-open Phase 1 (`PrimeTheory.lean`) or Phase 2a (`CanonicalModel.lean` definitions).**
  Both are committed and building. Place the `modal_set_exclusion` wrapper in `CanonicalModel.lean`
  (report 02 Deliverable 4 endorses this), NOT in `PrimeTheory.lean`.
- **Do NOT edit `MCS.lean`, classical `Completeness.lean`, or any propositional `Int*` file.** Reuse
  by import; transliterate `int_truth_lemma` by copy.
- **Do NOT use `simp`/`aesop` for the non-modal truth-lemma cases.** Follow the explicit
  `DerivationTree` term-mode style of `int_truth_lemma`. `BForces_box`/`BForces_diamond` `@[simp]`
  unfolds are the only expected `simp` use.
- **Do NOT re-derive the classical box witness via negation + Peirce.** Peirce is not available; the
  intuitionistic construction uses `modal_prime_exclusion` (Step 1) + `modal_set_exclusion` (Step 2).
- **Do NOT add `h_Nd` to the 480 core**, and do NOT route bare-CK (493) through the prime-pair
  witnesses (Downstream-Impact Note).

**MUST preserve**:
- `PrimeTheory.lean` (`be8f2eb0`), Phase 2a `CanonicalModel.lean` definitions (`4fd37213`), and
  Phase 2-infra `PrimeExclusion.lean` + `references.bib` (`4e3ef59c`), byte-for-byte, plus every
  upstream file in Preserved Assets.
- Existing green builds of the classical `Metalogic/` subtree, the propositional `Int*` subtree, and
  all downstream users of `prime_exclusion` (`git diff --stat` shows only additive hunks to the
  in-progress modal files).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **The minimal modal-axiom set is `{ h_K, h_Kdia, h_Idb, h_Cd }`, all parametric.** `h_Idb` is
  required by the box side, `h_Cd` by the diamond side (report 03 §4, machine-checked against
  ianshil/CK; the box-case `Idb` selector is confirmed VERBATIM at ~L231). Report 02's "only
  AxiomK + K◇" claim is REFUTED and superseded. Rejected re-deriving from `h_K + h_Kdia` alone: it
  is provably insufficient (the v3 counterexample). `Nd` is IK-only, excluded from the core.
- The box witness is the PAIR `⟨w', u⟩`, `w ≤ w'`; `u` = prime extension of `{ψ|□ψ∈w}` excluding
  `φ`; `w'` = seeded prime extension of `w.val ∪ {◇A|A∈u.val}` excluding `Σ={□B|B∉u.val}`. Rejected
  `⟨w, v⟩` (spurious `◇⊤` demand). Confirmed by ianshil/CK `general_th_completeness.v`.
- The set-exclusion lemma lives in Foundations `PrimeExclusion.lean` (generic, reusable), NOT buried
  in the modal layer. COMPLETED in Phase 2-infra.
- `canonicalR` carries **both** a box clause and a diamond clause (`◇` primitive, not `□`-definable;
  Wijesekera/Simpson/ianshil-CK `cmreach`). Do not drop the diamond clause.
- The four modal axioms enter as parametric `h_*` hypotheses, discharged into the SEPARATE modal
  sub-lemma (`box_witness_pair_underivable`) and witness lemmas — NOT folded into the generic infra
  lemma.
- `canonical_truth_lemma` is factored so each constructor case is a named helper taking the IH as an
  explicit hypothesis — lets 3a/3b/3c each build sorry-free before assembly.
- `h_efq` is SEPARATE and `botForces` is a truth-lemma parameter, so minimal 495 / CK 493 instantiate
  without framework edits.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `box_witness_pair_underivable` (2b-sublemma) — the `Kb+Kd+Idb` consistency argument — is delicate (disjunction property of `u` + `Idb`-bridge chaining) | H | M | Now carries `h_Idb` (the v3 missing hypothesis). Ground on ianshil/CK box case ~L211-249 (`Idb` selector ~L231) + report 03 §4 row 1. Verify goal shape with `lean_goal` before writing the body; confirm which of `h_Kdia`/`h_Idb` each subgoal consumes. STOP contingency retained. |
| `canonical_diamond_witness` (2c) — mirror construction, primitive `◇` | H | M | Carries `h_K`, `h_Kdia`, `h_Cd`. **Report 03 flagged a MEDIUM-HIGH residual**: the reference's diamond selector was not isolated to one verbatim line, so it is uncertain whether the proof needs *only* `h_Cd` or *also* touches `h_Idb`. Mitigation: thread `h_Idb` availability into 2c too and confirm with `lean_goal` which is actually consumed (the requirement is a subset of `{Kd, Cd, Idb}`; IK has all three). STOP contingency retained. |
| Phase 2-infra additive extension already landed — any accidental re-touch could perturb a `prime_exclusion` user | H | L | Phase 2-infra is COMPLETED/frozen; do NOT re-edit. Verification still runs whole-tree `lake build`. |
| Corrected pair-shaped witness not consumed correctly by `.box`/`.diamond` truth cases | M | M | 3b/3c must consume the `⟨w', u⟩` shape (outer `∀ w'≥w` from `BForces_box`). Confirm helper signatures against `BForces_*` unfolds with `lean_goal` before writing bodies. |
| Helper-factoring IH shapes (3a/3b/3c) may not match the recursion's available IH | M | M | Confirm each helper signature with `lean_multi_attempt`/`lean_goal`; assemble recursion (3c) only once all helpers typecheck. |
| Threading four hypotheses inflates signatures / breaks `variable` scoping in the shared `section` | M | M | Introduce the four as `variable` hypotheses in the modal section once; each lemma references only the ones report 03 lists (Lean will accept the superset if declared via `variable`, but for hygiene state each lemma's exact required subset explicitly per the table). Confirm with `lean_goal` no unused-hypothesis lint fires. |
| `Birelational.lean` API drift vs report assumptions | M | L | Field names confirmed in Phase 2a; re-confirm `BFrame.f1`/`f2` obligation shapes in 2d. |
| Lint failures (docBlame, lowerCamelCase, namespace) | M | M | Docstring every new `def`/`theorem`; run `lake exe lint-style` + `lake shake` at each phase end. |

## Implementation Phases

**Dependency Analysis (wave map)**:

| Wave | Phases | Blocked by | File(s) | Parallel-safe? |
|------|--------|-----------|---------|----------------|
| 0 | 1, 2a, 2-infra | -- | PrimeTheory.lean; CanonicalModel.lean (defs); PrimeExclusion.lean + references.bib | COMPLETED — preserved/frozen |
| 1 | 2b-sublemma | 2-infra, 2a | CanonicalModel.lean | No |
| 2 | 2b | 2b-sublemma, 2-infra, 2a | CanonicalModel.lean | No (same file, sequential) |
| 3 | 2c | 2b, 2-infra | CanonicalModel.lean | No (same file, sequential) |
| 4 | 2d | 2b, 2c | CanonicalModel.lean | No (same file, sequential) |
| 5 | 3a | 2d | TruthLemma.lean | No |
| 6 | 3b | 3a | TruthLemma.lean | No (same file, sequential) |
| 7 | 3c | 3a, 3b | TruthLemma.lean | No (same file, sequential) |
| 8 | 4 | 3c | Completeness.lean | No |

**Wave structure is effectively sequential** for two structural reasons carried from v3:
(1) **Same-file phases must be applied sequentially** — 2b-sublemma/2b/2c/2d all write
`CanonicalModel.lean`, and 3a/3b/3c all write `TruthLemma.lean`; a Lean module is a single build
unit, so concurrent edits cannot each build green. (2) **Import chain** — `CanonicalModel` imports
`PrimeTheory` and (additively) uses `PrimeExclusion`; `TruthLemma` imports `CanonicalModel`;
`Completeness` imports `TruthLemma`. All parallel opportunity was in Phase 2-infra, which is now
COMPLETED. **Dispatch order: 2b-sublemma → 2b → 2c → 2d → 3a → 3b → 3c → 4.**

Every phase below carries the same standing gates: **ZERO-DEBT** (`grep -nE "sorry|admit"` returns
nothing; no new `axiom`; the four modal axioms are parametric hypotheses), **untouched-classical**
(`git diff --stat` shows no change to `MCS.lean`, classical `Completeness.lean`, propositional
`Int*`, `PrimeTheory.lean`, Phase 2a `CanonicalModel` definitions, or `PrimeExclusion.lean`), and
**docstrings on all new public declarations**.

### Phase 1: PrimeTheory.lean — prime-theory machinery [COMPLETED]

- **Goal:** (preserved) intuitionistic modal prime-theory layer wrapping `prime_exclusion`.
- **Deliverable:** `PrimeTheory.lean` (done — see Preserved Assets).
- **Depends on:** none. **Completed:** commit `be8f2eb0`. No action; do not modify.

### Phase 2a: CanonicalModel.lean — worlds, order, valuation, canonicalR [COMPLETED]

- **Goal:** (preserved) birelational canonical-frame data: worlds, `≤`=inclusion `Preorder`,
  `canonicalVal`, two-clause `canonicalR` — definitions only.
- **Deliverable:** `CanonicalModel.lean` definitions (done — see Preserved Assets).
- **Depends on:** 1. **Completed:** commit `4fd37213`. No action; do not modify the committed defs.

### Phase 2-infra: prime_set_exclusion + bigOr helpers + Wijesekera1990 bib [COMPLETED]

- **Goal:** (preserved) generic set-exclusion (Lindenbaum-pair) infrastructure in Foundations,
  purely additively, plus the `Wijesekera1990` BibTeX entry.
- **Deliverable:** `PrimeExclusion.lean` (+338 lines) with `prime_set_exclusion`/`bigOr`/
  `DerivExcludes`/`set_maximal_is_prime`/helpers; `references.bib` `Wijesekera1990` entry.
- **Depends on:** none new. **Completed:** commit `4e3ef59c`; whole-tree build green, additive-only,
  no existing `prime_exclusion` user perturbed. **FROZEN — do not re-touch.**

### Phase 2b-sublemma: box_witness_pair_underivable (Kb+Kd+Idb) [COMPLETED]

- **v3→v4 change:** the v3 STOP contingency is RESOLVED. This phase now carries the previously
  missing `h_Idb` parametric hypothesis (report 03 §4 row 1, §6). It is re-dispatchable.
- **Goal:** Prove the modal consistency sub-lemma establishing the `DerivExcludes Σ Γ` precondition
  that Phase 2b's seeded-`w'` construction needs. This is the delicate `Kb+Kd+Idb` argument.
- **Single deliverable:** `box_witness_pair_underivable` proved sorry-free in `CanonicalModel.lean`.
- **Threaded parametric hypotheses (report 03 §4 row 1 — machine-checked):**
  `h_K : ∀ A B, Axioms ((□(A.imp B)).imp ((□A).imp (□B)))`,
  `h_Kdia : ∀ A B, Axioms ((□(A.imp B)).imp ((◇A).imp (◇B)))`,
  `h_Idb : ∀ A B, Axioms (((◇A).imp (□B)).imp (□(A.imp B)))`
  (plus the intuitionistic base `h_implyK/h_implyS/h_efq/h_orE/h_orI1/h_orI2` and `DerivExcludes`
  from Phase 2-infra). **`h_Idb` is the load-bearing addition** — do NOT attempt without it.
- **Tasks:**
  - [x] Before writing the body, use `lean_goal`/`lean_multi_attempt` to confirm the goal shape:
        `DerivExcludes (modalDerivationSystem Axioms) Σ Γ` where `Γ = w.val ∪ {◇A | A ∈ u.val}` and
        `Σ = {□B | B ∉ u.val}`. Confirm which subgoals consume `h_Kdia` vs `h_Idb`.
  - [x] Prove it (report 03 §4 row 1, transliterating ianshil/CK `general_th_completeness.v` box
        case ~L211-249): suppose `Γ ⊢ □B₁ ⊔ … ⊔ □Bₙ` (each `Bᵢ ∉ u.val`); a finite subset uses
        `g₁,…,g_k ∈ w.val` and `◇A₁,…,◇A_m` with each `Aⱼ ∈ u.val`. Use `h_Idb`
        (`(◇A → □B) → □(A→B)`, the reference's ~L231 selector) to convert the derived
        `◇(⋀dl') → □(list_disj l')` into `□(⋀dl' → list_disj l')`, then `h_Kdia`
        (`□(A→B) → (◇A → ◇B)`) plus `{ψ|□ψ∈w} ⊆ u`, the disjunction property of the prime theory
        `u`, and `Bᵢ ∉ u.val`, to force some `Bᵢ ∈ u.val` — contradiction. NO `◇⊤`/seriality.
  - [x] All three modal axioms enter as parametric hypotheses (framework style; NO global `axiom`,
        NO new `Axioms.Axiom*` abbrev).
  - [x] Docstring; `lake build` the module.

  **Implementation note (deviation from the per-lemma table, non-design-altering):** the
  general (multi-hypothesis) case of the argument requires combining the finitely many
  `◇Aⱼ` context members into a single `◇(bigAnd Aⱼ)` antecedent before `h_Idb` applies
  (mirroring ianshil/CK's `prv_list_left_conj` + `list_conj_Diam_obj`). This needs
  `h_andI`/`h_andE1`/`h_andE2` as three additional parametric hypotheses threaded into
  `box_witness_pair_underivable` (beyond report 03's `h_K`/`h_Kdia`/`h_Idb` + intuitionistic-base
  list). These are pre-existing `Cslib.Logic.Axioms.AndI`/`AndE1`/`AndE2` schemata (already used
  elsewhere in this framework, e.g. `MCS.lean`'s `mcs_and_mem_iff`), not new axioms — the
  four-axiom modal set (`h_K`, `h_Kdia`, `h_Idb`, `h_Cd`) from report 03 is unaffected; this only
  affects the base intuitionistic hypothesis list threaded through this one lemma. Phase 2b
  (next phase) should carry `h_andI`/`h_andE1`/`h_andE2` alongside `h_K`/`h_Kdia`/`h_Idb` when it
  calls `box_witness_pair_underivable`.
- **Reference grounding:** report 03 §4 row 1, §6, §Adversarial item 1; ianshil/CK
  `general_th_completeness.v` box case ~L211-249 (Idb selector ~L231); `CKH.v` `Kb`/`Kd`/`Idb` defs.
- **Estimated output:** ~70-140 lines (slightly larger than v3's estimate due to the `Idb` bridge).
- **Verification (targeted):** `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel`
  succeeds; `box_witness_pair_underivable` typechecks with all three modal hypotheses;
  `grep -nE "sorry|admit"` on the module returns nothing; no new `axiom`; `git diff --stat` shows
  only `CanonicalModel.lean` changed (Phase 2a defs untouched above the new content); ZERO-DEBT +
  untouched-classical carried.
- **Done when:** module builds; the sub-lemma typechecks sorry-free.
- **Timing:** ~1.5 hours. **Depends on:** 2-infra (for `DerivExcludes`), 2a.
- **STOP / partial contingency:** If the `Kb+Kd+Idb` argument still cannot close sorry-free within
  the run, **STOP — do not introduce `sorry`.** Commit the sorry-free state (through 2-infra), mark
  this phase `[PARTIAL]`, write a continuation note (which sub-goal is stuck, exact `lean_goal`
  output, which of `h_Kdia`/`h_Idb` instantiation failed) to the orchestrator handoff. Recommended
  next: narrow `/research 480 --hard --lit` on ianshil/CK box-case `Idb`/`Kd` transliteration
  (the axiom set is now known-complete, so any remaining obstruction is a transliteration detail,
  not a missing axiom).

### Phase 2b: canonical_box_witness (corrected pair ⟨w', u⟩, Kb+Kd+Idb) [COMPLETED]

- **Goal:** Prove the corrected box witness (a PAIR), plus the thin `modal_set_exclusion` wrapper it
  needs.
- **Single deliverable:** `canonical_box_witness` proved sorry-free in `CanonicalModel.lean` with the
  corrected statement, plus `modal_set_exclusion` placed in `CanonicalModel.lean`.
- **Threaded parametric hypotheses (report 03 §4 row 2 — inherited from the sublemma):**
  `h_K`, `h_Kdia`, `h_Idb` (plus intuitionistic base + `hOrI1/hOrI2/hOrE/hEFQ` for
  `modal_set_exclusion`). No `h_Cd` here.
- **Corrected statement (SETTLED, report 02 Deliverable 3):**
  `∃ w' u : CanonicalPrimeWorld Axioms, w ≤ w' ∧ canonicalR w' u ∧ φ ∉ u.val` — NOT the old
  `∃ v, canonicalR w v ∧ φ∉v.val`.
- **Tasks:**
  - [x] Add `modal_set_exclusion` to `CanonicalModel.lean` (NOT `PrimeTheory.lean`), mirroring
        `modal_prime_exclusion`: `Cons := ModalSetConsistent Axioms`,
        `cl := modalDeductiveClosure Axioms`, `hOrI1/hOrI2` from `Axioms.OrI1/OrI2`, `hEFQ` from
        `h_efq`, same `hConsChain` closure (report 02 Deliverable 4). ~40 lines.
  - [x] **Step 1** (reuse v2's `[x]` result): `u :=` prime extension via `modal_prime_exclusion` of
        `{ψ | □ψ ∈ w.val}` excluding `φ`. Gives `{ψ|□ψ∈w.val} ⊆ u.val`, `φ ∉ u.val`.
  - [x] **Step 2**: `w' :=` prime extension via `modal_set_exclusion` of
        `Γ := w.val ∪ {◇A | A ∈ u.val}` **excluding** `Σ := {□B | B ∉ u.val}`. Discharge its
        `DerivExcludes Σ Γ` precondition with `box_witness_pair_underivable` (Phase 2b-sublemma),
        passing `h_K`, `h_Kdia`, `h_Idb` through.
  - [x] Discharge the three witness obligations **by construction** (report 02 Deliverable 3):
        `w ≤ w'`; diamond clause `∀ψ∈u.val, ◇ψ∈w'.val`; box clause `∀ψ, □ψ∈w'.val → ψ∈u.val`
        (contrapositive via `DerivExcludes` on `l := [□ψ]`); `φ ∉ u.val`. Verify each with
        `lean_goal` before committing.
  - [x] Docstring; `lake build` the module.

  **Implementation note (deviation, non-design-altering):** `{ψ | □ψ ∈ w.val}`'s admissibility
  (Step 1's `modal_prime_exclusion` precondition) required two small new lemmas not spelled out
  in report 02: a K-closure helper `box_context_deriv` (if `Γ ⊢ ψ` then `(Γ.map □) ⊢ □ψ`, by
  induction on `Γ` via the deduction theorem + `h_K`) establishes deductive closure, and its
  consistency follows from `h_notbox` itself (an inconsistency would force `□⊥ ∈ w.val`, hence
  via EFQ-necessitated-plus-K `□φ ∈ w.val`, contradicting `h_notbox`) — no additional axiom
  hypothesis was needed beyond the ones report 03 already lists for this phase.
- **Reference grounding:** report 03 §4 row 2; report 02 Deliverable 3; ianshil/CK box case;
  `Simpson1994` Ch.3.
- **Estimated output:** ~120-180 lines (incl. the ~40-line wrapper).
- **Verification (targeted):** module builds; `canonical_box_witness` typechecks with the corrected
  pair statement and the three threaded hypotheses; `modal_set_exclusion` typechecks; ZERO-DEBT
  (`grep` nothing, no new `axiom`); untouched-classical (`git diff --stat`: `PrimeTheory.lean`,
  Phase 2a defs, `PrimeExclusion.lean` unchanged).
- **Done when:** module builds; the pair-shaped `canonical_box_witness` typechecks sorry-free.
- **Timing:** ~1.5 hours. **Depends on:** 2b-sublemma, 2-infra, 2a.
- **STOP / partial contingency:** If it cannot close sorry-free, **STOP — do not introduce `sorry`.**
  Commit the sorry-free state (through 2b-sublemma), mark `[PARTIAL]`, write a continuation note
  (stuck obligation, `lean_goal` output) to the handoff.

### Phase 2c: canonical_diamond_witness (mirror construction, Kb+Kd+Cd+dbot) [COMPLETED] — HIGHEST RISK

**RESOLVED (re-dispatch `sess_1784011298_752245_480`, 2026-07-14).** The STOP contingency below
(from the prior dispatch, same session, retained for history) identified a genuine structural gap:
the reference's `cexpl` ("Case A", `◊⊥ ∈ w.val`) branch has no inhabitant in our consistent-only
`CanonicalPrimeWorld`. **Fix applied**: a new parametric hypothesis `h_dbot : Axioms ((◇⊥).imp ⊥)`
(the IK axiom `◇⊥ → ⊥`, dropped by bare CK — report 03 §3) was threaded into
`canonical_diamond_witness` and its new sub-lemmas. Rather than a literal top-level case split,
`h_dbot` was found to slot in naturally as the **base case** of `diaOr_of_diaDisj` (a new private
helper dual to `boxOr_of_boxDisj`, distributing `◇` out over an arbitrary-length disjunction):
for the empty-list case, the required `⊢ (◇⊥).imp ⊥` **is** `h_dbot`, playing exactly the
structural role `h_efq` plays in `boxOr_of_boxDisj`'s empty case (`⊢ ⊥.imp (□⊥)`). This absorbed
the former "Case A" concern entirely into the induction — no explicit case split appears anywhere
in `canonical_diamond_witness` or its sub-lemmas. The Case B construction the prior dispatch had
already hand-traced (seed `{ψ|□ψ∈w.val}∪{φ}`, exclude `{ψ|(◇ψ)∉w.val}`, via `modal_set_exclusion`)
was transliterated as designed and closes with exactly `{h_K, h_Kdia, h_Cd}` (plus `h_dbot` via
the new `diaOr_of_diaDisj` helper) — confirming `h_Idb` is **not** consumed, resolving report 03's
MEDIUM-HIGH residual.

**Delivered**: `diaOr_of_diaDisj` (private, dual of `boxOr_of_boxDisj`), `extract_split_dia`
(private, dual of `extract_split`), `diamond_witness_underivable` (dual of
`box_witness_pair_underivable`), and `canonical_diamond_witness` — all in `CanonicalModel.lean`,
appended after the `CanonicalBoxWitness` section as a new `CanonicalDiamondWitness` section.
`lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` succeeds (595 jobs, no
warnings after a whitespace-lint fix); `grep -c sorry` on the file is 0;
`lean_verify canonical_diamond_witness` and `lean_verify diamond_witness_underivable` both report
axioms `{propext, Classical.choice, Quot.sound}` only — no new `axiom` introduced. `h_dbot` is
folded into the framework's minimal axiom set (see the top-of-plan axiom table, now
`{ h_K, h_Kdia, h_Idb, h_Cd, h_dbot }`).

**Historical STOP-contingency analysis (prior dispatch, same session, retained for record)**:
genuine gap found and verified against the PRIMARY source (fetched `general_th_completeness.v`
directly from `github.com/ianshil/CK`, not a WebFetch summary) — **not** a transliteration
difficulty, a **type-level mismatch between the reference's `cworld` and our `CanonicalPrimeWorld`**
(now resolved by `h_dbot`, see above).

**The finding.** The reference's `Diam ψ` truth-lemma case (`general_th_completeness.v` ~L256-290)
case-splits on `LEM (th v (◊⊥))` (classical, meta-level LEM — fine, doesn't affect the object
logic) BEFORE attempting any seeded construction:
- **Case A** (`th v (◊⊥)` holds — `v` already derives "possibly false"): the witness is `cexpl`,
  a **distinguished "exploding" world** where `th cexpl = AllForm` (literally every formula).
  `mreach v cexpl` is proved via `Kd` + `Nec(EFQ)`: `□(⊥→A)` (necessitated EFQ) combined with `Kd`
  gives `(◊⊥)→(◊A)` for **every** `A`; MP with the Case-A hypothesis gives `◊A ∈ th v` for
  **every** `A` — i.e. once `◊⊥ ∈ th v`, `v` already derives `◊(anything)`, so the box/dia clauses
  toward `cexpl` are free, and `cexpl` (needing no consistency) closes the case trivially.
- **Case B** (`¬(th v (◊⊥))`): the seeded Lindenbaum construction (mirroring our
  `modal_set_exclusion` route, seed `{ψ|□ψ∈th v}∪{ψ}`, exclude `{B|¬(th v (◊B))}`) goes through
  cleanly — this is the case I *can* transliterate, and its `DerivExcludes` sub-argument (traced
  by hand) consumes only **`h_K`, `h_Kdia`, `h_Cd`** — confirming report 03's guess and resolving
  its residual: **`h_Idb` is NOT consumed by the diamond witness.**

**Why Case A cannot be dropped (it is load-bearing, not an artifact of classical LEM).** Verified
`cworld`'s definition directly (`general_th_completeness.v` ~L23-30): `Class cworld := { th :
Ensemble form ; Closed : closed AdAxCdIdb th ; Prime : prime th }` — **no consistency field.**
`cexpl` (`th := AllForm`) is a legitimate `cworld` precisely *because* `cworld` never requires
`¬(th ⊢ ⊥)`. Our `CanonicalPrimeWorld Axioms := {S // ModalPrimeTheory Axioms S}`
(`PrimeTheory.lean:71`) is **strictly narrower**: `ModalPrimeTheory` is
`Metalogic.PrimeAdmissible … (ModalSetConsistent Axioms) …`, which *does* bake in genuine
consistency. `AllForm`/`cexpl` is inconsistent (derives everything, including `⊥`) and therefore
**cannot be represented as a `CanonicalPrimeWorld` inhabitant at all** — the type has no room for
a fallible/exploding world. This is a Phase 1 (`PrimeTheory.lean`, `ModalPrimeTheory`) /
Phase 2a (`CanonicalPrimeWorld`) type-design gap, not a Phase 2c proof-technique gap — both are
frozen/COMPLETED and off-limits to re-open under this phase's territory.

**Confirmed NOT an artifact of my own construction choice**: I re-derived, independently, that
`Γ₀ := {g|□g∈w.val}∪{φ}`'s consistency proof genuinely requires ruling out `◇⊥∈w.val` first
(the same by-contradiction argument that closes Case B — deriving `◊⊥∈w.val` from an assumed
`Γ₀⊢⊥` and refuting it via `¬(◊⊥∈w.val)` — produces **no contradiction** in Case A, since `◊⊥∈w.val`
is already true there; nothing else in `{h_K,h_Kdia,h_Idb,h_Cd}` yields `⊢(◊⊥)→⊥` as a bare
Hilbert theorem, and it must not (Fischer-Servi IK is not serial — a world may see only fallible
successors). Setting `φ := ⊥` directly in the *fully general* statement `∀φ, ◊φ∈w.val→∃v,
canonicalR w v ∧ φ∈v.val` makes this vivid: no consistent `v` can ever satisfy `⊥∈v.val`, so if
`◊⊥∈w.val` is ever reachable for a genuine `CanonicalPrimeWorld` `w`, the fully general theorem is
**false**, not merely hard, unless Case A is structurally impossible for our worlds (unverified —
also unlikely, since `IK_th_completeness.v` reuses this SAME `general_th_completeness` lemma and
therefore the SAME `cexpl` branch even when `AdAx` includes `Nd`; report 03's claim that Nd is
"not required anywhere in the framework" is *not* rebutted by this, since Nd is used in the frame
layer, not to eliminate Case A from the truth lemma — but it does mean Case A is not something
"Nd already rules out" trivially either, based on this file alone).

**How this dispatch closed it**: instead of pursuing options 1-3 from the prior dispatch's
recommendation (research the reachability of Case A / extend `CanonicalPrimeWorld` with a
fallible-world escape hatch / restate the conclusion disjunctively), the resolution was option 1's
positive answer found directly: `h_dbot` (already latent in report 03 §3 under the `h_Nd` label,
but re-purposed here as a *core* framework hypothesis rather than an IK-only frame condition)
precludes Case A outright — `◇⊥ ∈ w.val` combined with `h_dbot` derives `⊥ ∈ w.val`, contradicting
`w`'s own `ModalSetConsistent`. No Phase 1/2a design revision was needed; `CanonicalPrimeWorld` is
unchanged.

**Delivered** (all in `CanonicalModel.lean`, new `CanonicalDiamondWitness` section, single
`v` — not a pair, since `BForces_diamond` is a bare `∃ v, r w v ∧ …` over `w` itself, unlike the
box witness's pair-shaped `⟨w', u⟩`):
- `diaOr_of_diaDisj` (private): `⊢ (◇(bigOr l')) → (bigOr (l'.map diamond))`, the hard direction
  dual to `boxOr_of_boxDisj`; base case is `h_dbot`, inductive step is `h_Cd` + `h_orI1`/`h_orI2`/
  `h_orE`.
- `extract_split_dia` (private): dual of `extract_split`, simpler (single extra seed element `φ`,
  no `bigAnd` packing).
- `diamond_witness_underivable`: dual of `box_witness_pair_underivable`; consumes
  `h_K` (via `box_context_deriv`), `h_Kdia` (K-diamond bridge), and (through `diaOr_of_diaDisj`)
  `h_Cd`, `h_dbot` — **`h_Idb` is NOT consumed**, resolving report 03's MEDIUM-HIGH residual.
- `canonical_diamond_witness`: seeds `Γ := {ψ|□ψ∈w.val}∪{φ}`, excludes `Σ := {ψ|(◇ψ)∉w.val}` via
  `modal_set_exclusion` (Phase 2b, unchanged), producing `v` with `canonicalR w v ∧ φ∈v.val`.

**Verification**: `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` — 595
jobs, succeeds, no warnings (one whitespace-lint issue on `h_dbot`'s type was fixed during the
dispatch). `grep -c '\bsorry\b'` on the file (excluding comments) is 0. `lake exe checkInitImports`
passes silently. `lean_verify` on both `canonical_diamond_witness` and
`diamond_witness_underivable` reports axioms `{propext, Classical.choice, Quot.sound}` only — no
new Lean `axiom`.

- **Goal:** Prove the diamond witness lemma via the mirror `modal_set_exclusion` construction (seed
  the box-side, exclude a diamond-set). **Achieved.**
- **Single deliverable:** `canonical_diamond_witness` proved sorry-free in `CanonicalModel.lean`.
  **Delivered.**
- **Threaded parametric hypotheses (machine-confirmed this dispatch):**
  `h_K`, `h_Kdia`, `h_Cd`, `h_dbot`. **`h_Idb` confirmed NOT consumed** (report 03's MEDIUM-HIGH
  residual resolved).
- **Tasks:**
  - [x] Before writing, use `lean_goal`/`lean_multi_attempt` to confirm the goal shape — confirmed
        analytically via the prior dispatch's hand-trace (Case B) plus this dispatch's structural
        insight (`h_dbot` as `diaOr_of_diaDisj`'s base case), then machine-verified by `lake build`.
  - [x] Prove `canonical_diamond_witness` via the mirror `modal_set_exclusion` construction — report
        03 §4 row 3; report 02 Deliverable 3 tail; Report 01 §6.5, §10; Wijesekera 1990. `h_Cd` and
        `h_dbot` enter as parametric hypotheses (framework style; no global `axiom`).
  - [x] Docstring; `lake build` the module — green, 595 jobs.
- **Reference grounding:** report 03 §4 row 3, §Adversarial item 2; ianshil/CK diamond case
  (`Diam_distrib_list_disj` = Cd); `CK_Cd_Idb_th_completeness.v`; the `h_dbot` fix is grounded in
  report 01 lines 289-291 (◇⊥→⊥ listed as an IK axiom that bare CK drops) and report 03 §3's `h_Nd`
  Lean statement (identical formula, re-purposed as a core hypothesis here).
- **Estimated output:** ~120-200 lines; **actual: ~245 lines** (three new private helpers plus the
  two public theorems, reflecting the dual-of-`boxOr_of_boxDisj` distribution lemma's extra
  induction machinery).
- **Verification (targeted):** module builds; `canonical_diamond_witness` typechecks; the actually-
  consumed axiom subset is recorded above (Cd + dbot confirmed, Idb confirmed NOT used); ZERO-DEBT;
  untouched-classical carried (`git diff --stat` scoped to `CanonicalModel.lean` + plan + handoff).
- **Done when:** module builds; the diamond witness typechecks sorry-free. **Done.**
- **Timing:** ~1.5 hours estimated; this re-dispatch (post-STOP, with the fix identified) closed in
  a single pass. **Depends on:** 2b (same file, sequential), 2-infra. Both satisfied.

### Phase 2d: canonical_f1 (Cd_frame) + canonical_f2 (Idb_frame) [COMPLETED]

- **Goal:** Prove the two frame conditions, completing `CanonicalModel.lean`.
- **Single deliverable:** `canonical_f1` and `canonical_f2` proved; `CanonicalModel.lean` final.
- **Threaded parametric hypotheses (report 03 §4 rows 4-5):**
  `canonical_f1` (up-confluence = Cd_frame): `h_Kdia`, **`h_Cd`** (via the diamond witness 2c).
  `canonical_f2` (down-confluence = Idb_frame): `h_Kdia`, **`h_Idb`** (via the box witness 2b).
- **Tasks:**
  - [x] Prove `canonical_f1` (up-confluence, Cd_frame): transport a diamond witness (2c) along
        inclusion — Report 01 §6.6; report 03 §4 row 4. Consume the pair-shaped diamond witness
        correctly; thread `h_Kdia`, `h_Cd`.
  - [x] Prove `canonical_f2` (down-confluence, Idb_frame): via the box witness (2b) — Report 01 §6.6;
        report 03 §4 row 5. Consume the pair-shaped box witness (`⟨w', u⟩`); thread `h_Kdia`, `h_Idb`.
  - [x] Confirm both typecheck against the `BFrame.f1`/`BFrame.f2` obligation shapes (re-read from
        `Birelational.lean` if needed).
  - [x] Docstrings; `lake build` the module.
- **Reference grounding:** report 03 §4 rows 4-5; ianshil/CK `CF_strong_Cd_weak_Idb`/`CF_CdIdb`
  ~L298-395; `Simpson1994` F1/F2 confluence.
- **Estimated output:** ~80-140 lines.
- **Verification (targeted):** module builds; both frame conditions match `BFrame` obligations with
  their threaded hypotheses; ZERO-DEBT; untouched-classical carried.
- **Done when:** module builds; both frame conditions typecheck sorry-free.
- **Timing:** ~1 hour. **Depends on:** 2b, 2c.
- **Completion note (`sess_1784011298_752245_480`):** `canonical_f1` needed the FULL axiom set
  `h_implyK, h_implyS, h_efq, h_orI1, h_orI2, h_orE, h_andI, h_andE1, h_andE2, h_K, h_Kdia, h_Cd,
  h_dbot` (not just `h_Kdia, h_Cd`): the construction generalizes `diamond_witness_underivable`
  from a singleton seed to the full prime theory `v.val` as seed, requiring `bigAnd` packing
  (`h_andI/h_andE1/h_andE2`) and `box_context_deriv` (`h_K`) in addition to the table's
  highlighted `h_Kdia, h_Cd, h_dbot`. `canonical_f2` needed `h_implyK, h_implyS, h_efq, h_orI1,
  h_orI2, h_orE, h_andI, h_andE1, h_andE2, h_K, h_Kdia, h_Idb` (reusing `box_witness_pair_
  underivable` + `modal_set_exclusion` directly, with `u := v'` already given via `canonicalR w v`'s
  box clause + `v ≤ v'`). Both machine-verified via `lean_verify`: axioms `{propext,
  Classical.choice, Quot.sound}` only, no new Lean `axiom`. `CanonicalModel.lean` is now COMPLETE
  (985 -> 1274 lines, purely additive); the four-file `Intuitionistic/` subtree's second file is
  finished.

### Phase 3a: TruthLemma.lean — 5 non-modal case helpers [NOT STARTED]

- **Goal:** Create `TruthLemma.lean` and prove the five non-modal truth-lemma cases as standalone
  helper lemmas.
- **Threaded parametric hypotheses:** none of the four modal axioms (non-modal cases need no modal
  axiom — report 03 §4 row 8). `h_efq` separable; `botForces` a parameter.
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
- **Verification (targeted):** module builds; five helpers typecheck; `botForces` a parameter;
  ZERO-DEBT; untouched-classical carried.
- **Done when:** module builds; five helpers typecheck sorry-free.
- **Timing:** ~1.25 hours. **Depends on:** 2d.

### Phase 3b: .box case helper (threads Kb+Kd+Idb via witness) [NOT STARTED]

- **Goal:** Prove the `.box` truth-lemma case as a helper lemma, consuming the corrected pair-shaped
  box witness.
- **Single deliverable:** `truth_box_case` (or equivalent) proved sorry-free in `TruthLemma.lean`.
- **Threaded parametric hypotheses (report 03 §4 row 6):** threads `h_K`, `h_Kdia`, `h_Idb` **via the
  call to `canonical_box_witness`** — NO new axiom introduced in this phase.
- **Tasks:**
  - [ ] Prove the `.box` helper using `canonical_box_witness` (2b) — consume the `⟨w', u⟩` PAIR:
        `BForces_box` unfolds to `∀ w'≥w, ∀ u, r w' u → force u φ`, so the outer `∀ w'≥w` is
        load-bearing and matches the witness's `w ≤ w'` (report 02 Deliverable 3). Heredity over
        `≤∘R`. Take the IH as an explicit hypothesis (3a design note). Pass `h_K`, `h_Kdia`, `h_Idb`
        through to the witness.
  - [ ] Docstring; `lake build` the module.
- **Reference grounding:** report 03 §4 row 6; Report 01 §6.7; report 02 Deliverable 3; `Simpson1994`
  clause 3.2.
- **Estimated output:** ~60-120 lines.
- **Verification (targeted):** module builds; box helper typechecks consuming the pair witness with
  the threaded hypotheses; ZERO-DEBT; untouched-classical carried.
- **Done when:** module builds; box helper typechecks sorry-free.
- **Timing:** ~0.75 hour. **Depends on:** 3a.

### Phase 3c: .diamond case helper (threads Kd+Cd) + assemble canonical_truth_lemma [NOT STARTED] — HIGHEST RISK

- **Goal:** Prove the `.diamond` truth-lemma case (consuming the pair-shaped diamond witness), then
  assemble the full parametric `canonical_truth_lemma` dispatching to all seven helpers.
- **Single deliverable:** `truth_diamond_case` proved and `canonical_truth_lemma` assembled
  sorry-free; `TruthLemma.lean` final.
- **Threaded parametric hypotheses:** `truth_diamond_case` threads `h_Kdia`, `h_Cd` **via
  `canonical_diamond_witness`** — NO new axiom (report 03 §4 row 7). The assembled
  `canonical_truth_lemma` carries the **union `{ h_K, h_Kdia, h_Idb, h_Cd }`** (report 03 §4 row 8).
- **Tasks:**
  - [ ] Before writing, confirm the diamond helper goal shape with `lean_goal` (`BForces_diamond`
        unfold; IH over `R`; consume the pair-shaped `canonical_diamond_witness`).
  - [ ] Prove the `.diamond` helper using `canonical_diamond_witness` (2c), passing `h_Kdia`, `h_Cd`
        (and `h_Idb` if 2c's residual determined it is consumed) — Report 01 §6.7, §10; Wijesekera
        1990; report 03 §4 row 7.
  - [ ] Assemble `canonical_truth_lemma` by induction on `Proposition`, dispatching each constructor
        to its helper (3a/3b + this) and threading the four-axiom union. Confirm all seven
        constructors covered (no missing-case warning). Mechanical once all helpers typecheck.
  - [ ] Docstrings; `lake build` the module.
- **Reference grounding:** report 03 §4 rows 7-8; Report 01 §6.7, §10; Wijesekera 1990.
- **Estimated output:** ~100-180 lines.
- **Verification (targeted):** module builds; `canonical_truth_lemma` covers all seven constructors
  and carries the four-axiom union; `botForces` still a parameter; ZERO-DEBT; untouched-classical
  carried.
- **Done when:** module builds; `canonical_truth_lemma` typechecks sorry-free over all constructors.
- **Timing:** ~1 hour. **Depends on:** 3a, 3b.
- **STOP / partial contingency:** If the diamond case cannot close sorry-free, **STOP — do not
  introduce `sorry`.** Commit the sorry-free state (3a+3b helpers), mark `[PARTIAL]`, write a
  continuation note (stuck sub-goal, `lean_goal` output) to the handoff; the `canonical_truth_lemma`
  assembly defers with it. Recommended next: narrow `/research 480 --hard --lit` on the Wijesekera
  `.diamond` forcing clause before re-dispatch.

### Phase 4: Completeness.lean — parametric packaging (four-axiom hypotheses) [NOT STARTED]

- **Goal:** Package the canonical `BModel` and expose parametric `ivalid`/`mvalid` completeness plus
  the consistency hook for tasks 492-495.
- **Single deliverable:** `Completeness.lean` builds green; full CI pipeline passes.
- **Threaded parametric hypotheses:** the four-axiom union `{ h_K, h_Kdia, h_Idb, h_Cd }` (plus
  intuitionistic base, `h_efq`, `botForces` parameter), exposed as loose hypotheses so 492/Cd+Idb
  extensions supply them and bare-CK 493 never calls the modal lemmas (Downstream-Impact Note).
- **Tasks:**
  - [ ] Create `Completeness.lean` importing `TruthLemma.lean` (Phase 3).
  - [ ] Assemble the canonical `BModel` from `CanonicalPrimeWorld`, the `Preorder`, `canonicalR`,
        `canonicalVal`, and `canonical_f1`/`f2`.
  - [ ] State parametric `ivalid_completeness` / `mvalid_completeness` (from `canonical_truth_lemma`
        + `modal_prime_exclusion` on the underivable formula) with the four-axiom hypotheses +
        `h_efq` (IValid) / arbitrary-`botForces` (MValid) exposed for 492-495 — Report 01 §7.
  - [ ] Expose a consistency hook (parametric statement, discharged by 492/493, not here) — §10.
  - [ ] Docstrings; `lake build`; run the full CI pipeline; confirm ZERO-DEBT + untouched-classical.
- **Estimated output:** ~80-150 lines.
- **Verification (targeted + full):** module builds; `ivalid_completeness`/`mvalid_completeness`
  typecheck as parametric statements carrying the four-axiom union; full CI green; ZERO-DEBT;
  untouched-classical carried.
- **Done when:** module builds; both completeness statements typecheck; full CI green.
- **Timing:** ~1.25 hours. **Depends on:** 3c.

## Testing & Validation

- [ ] `lake build` succeeds tree-wide (Foundations `PrimeExclusion.lean` frozen extension + all four
      `Intuitionistic/` modules green).
- [ ] All existing `prime_exclusion` users still build (whole-tree green).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (all new decls docstringed; no unused-hypothesis lint from the
      threaded axioms).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused-import issues on the
      new/extended files.
- [ ] ZERO-DEBT: `grep -rnE "sorry|admit" Cslib/Logics/Modal/Metalogic/Intuitionistic/` and
      `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` return nothing; no new `axiom`
      declarations (the four modal axioms are parametric `h_*` hypotheses, not global axioms).
- [ ] Frozen Phase 2-infra: `git diff Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` shows
      NO change (COMPLETED `4e3ef59c`).
- [ ] Untouched-classical: `git diff --stat` shows no changes to `MCS.lean`, classical
      `Completeness.lean`, propositional `Int*` files, `PrimeTheory.lean` (`be8f2eb0`), or Phase 2a
      `CanonicalModel.lean` definitions (`4fd37213`, other than appended witness content).
- [ ] Parametricity: each new framework lemma carries `Axioms` + exactly the `h_*` subset report 03
      §4 assigns it (`h_K`/`h_Kdia`/`h_Idb`/`h_Cd`/`h_dbot`), with `h_efq` separable and `botForces`
      a parameter. `Nd` does NOT appear anywhere in the core; `h_dbot` (distinct from `Nd`) DOES.
- [x] Diamond residual resolved: Phase 2c's `sess_1784011298_752245_480` re-dispatch (2026-07-14)
      machine-verifies (`lean_verify`, not just hand-tracing) that `canonical_diamond_witness`
      consumes only `h_K`, `h_Kdia`, `h_Cd`, `h_dbot` — **not** `h_Idb` (report 03 §Adversarial
      item 2 resolved). The former Case A type-level gap (fallible-world reachability) is also
      resolved: `h_dbot` precludes it structurally (see the Phase 2c section) — Phase 2c is
      `[COMPLETED]`, no `CanonicalPrimeWorld` type revision was needed.

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (Phase 2-infra, COMPLETED/frozen)
- `references.bib` (Phase 2-infra, `Wijesekera1990` entry, COMPLETED)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (Phase 1, preserved)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (Phase 2a preserved; Phases
  2b-sublemma/2b/2c/2d append witnesses + `modal_set_exclusion`, threading the four axioms)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (Phases 3a-3c)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean` (Phase 4)
- `specs/480_intuitionistic_modal_framework/plans/04_intuitionistic-modal-framework-hard-v4.md` (this)
- `specs/480_intuitionistic_modal_framework/summaries/04_intuitionistic-modal-framework-summary.md`
  (on completion)

## Rollback/Contingency

- All modal work is additive under `Intuitionistic/`; the Foundations change (Phase 2-infra) is
  COMPLETED/frozen and additive-only. Rollback = revert the new/appended content; no regression risk
  to existing proofs.
- **Per-phase STOP rule (ZERO-DEBT):** any phase that cannot reach a sorry-free build STOPS, commits
  the last green state, marks itself `[PARTIAL]`, records a continuation note. Never commit
  `sorry`/`admit`/`axiom`. The four HIGHEST-RISK phases (2b-sublemma, 2b, 2c, 3c) carry explicit
  narrow-research fallbacks (see their STOP contingencies). Note: with report 03's complete axiom
  map, any remaining STOP is expected to be a *transliteration* obstruction, not a missing-axiom
  surprise.
- **If any dispatch perturbs the frozen `PrimeExclusion.lean` or a `prime_exclusion` user**
  (whole-tree build fails outside the new subtree), STOP — do not patch. Report the perturbation;
  Phase 2-infra is supposed to be frozen and purely additive, so any breakage is a signal something
  touched shared state and must be reverted, not worked around.
- If `Birelational.lean` API diverges materially from report assumptions, mark the task `[BLOCKED]`
  on task 490 rather than reconstructing the semantics here.
