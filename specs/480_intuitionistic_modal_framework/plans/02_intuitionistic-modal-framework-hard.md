# Implementation Plan (v2, HARD): Task #480 — Intuitionistic Modal Metalogic Framework

- **Task**: 480 - Intuitionistic modal metalogic FRAMEWORK (prime-theory machinery + birelational canonical-model construction)
- **Status**: [IN PROGRESS]
- **Effort**: 6.5 hours remaining (Phase 1 already complete; ~4.5h of original 11h consumed)
- **Dependencies**: Task 478 (classical Hilbert/metalogic framework, COMPLETED), Task 490 (birelational semantics `Birelational.lean`, present in-tree)
- **Research Inputs**: specs/480_intuitionistic_modal_framework/reports/01_intuitionistic-modal-framework.md
- **Artifacts**: plans/02_intuitionistic-modal-framework-hard.md (this file); supersedes plans/01_intuitionistic-modal-framework.md (v1, retained for history)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Plan Version**: 2 (hard-mode re-slice)
- **Lean Intent**: false

## Overview

This is a **hard-mode re-slice** of the v1 plan. The v1 plan had 4 large phases (~11h). A
standard monolithic implementation dispatch **completed Phase 1 only** (`PrimeTheory.lean`,
committed as `be8f2eb0`) and then **failed to complete `CanonicalModel.lean`** in a single run —
the module never reached a sorry-free build. Per user direction, the remaining work
(`CanonicalModel.lean`, `TruthLemma.lean`, `Completeness.lean`) is decomposed into **smaller
phases, each bounded to ONE agent run** (H8: ~100-500 lines output, one clear deliverable, its own
`lake build` + no-`sorry` gate), so each can be dispatched independently in hard mode with
per-phase adversarial verification. The two highest-risk proofs
(`canonical_diamond_witness` and the `.diamond` truth-lemma case) are **isolated into their own
phases** with explicit STOP/partial contingencies.

Definition of done (unchanged from v1): all four files under
`Cslib/Logics/Modal/Metalogic/Intuitionistic/` build under `lake build`, the full CSLib CI
pipeline passes, ZERO-DEBT is upheld (no `sorry`, no `admit`, no new `axiom`), and the classical
`Metalogic/` files plus the propositional `Int*` files are left byte-for-byte untouched.

### Preserved Assets

The following work is complete, committed, and MUST NOT regress. It is **not re-sliced** in this
plan (the v1→v2 note offered a 1a/1b split of Phase 1; that is moot — Phase 1 is already done):

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Phase 1: `ModalSetConsistent`, `ModalPrimeTheory`, `modalDeductiveClosure` + closure laws (`modal_subset_deductive_closure`, `modal_deriv_from_closure_to_S`, `modalDeductiveClosure_closed`, `modalDeductiveClosure_consistent`, `modalDeductiveClosure_is_admissible`, `modal_deriv_imp_of_union`), `modalNegPhiImpPsi_deriv`, `modal_imp_witness`, `modal_prime_exclusion` | `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (360 lines) | [COMPLETED] | commit be8f2eb0; grep shows no `sorry`/`admit`/`axiom` (all `axiom` hits are docstring words) |

The following upstream infrastructure is reused by import/transliteration and MUST NOT be edited
(untouched-classical constraint):

| Asset | File | Reuse mode |
|-------|------|-----------|
| `Metalogic.prime_exclusion` (generic) | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` | already wrapped by Phase 1 `modal_prime_exclusion` |
| `DerivationTree` / `modalDerivationSystem` / `deductionTheorem` | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`, `DeductionTheorem.lean` | import-only, verbatim |
| `iteratedDeduction`, `derive_box_from_box_context` | `Cslib/Logics/Modal/Metalogic/MCS.lean` | import-only (needed for box witness); NEVER modify MCS.lean |
| `BFrame`/`BModel`/`BForces`/`bforces_persistence`/`IValid`/`MValid`/`BForces_box`/`BForces_diamond` | `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) | import-only, codomain of truth lemma |
| `int_truth_lemma` non-modal cases (template) | `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean:108-214` | transliterate (copy), do not import |

### Research Integration

Integrated from `reports/01_intuitionistic-modal-framework.md` (Tier-1 literature task; `--lit`
active). See the Source-to-Implementation Mapping below. Key verdicts carried from v1: reuse is
strong; the genuinely new work is `canonicalR` (box + diamond clauses), the two witness lemmas,
F1/F2, and the two modal truth-lemma cases. Highest risk is the primitive-`◇` diamond witness and
`.diamond` truth-lemma case (Wijesekera 1990 chunk 0111 / chunk 0002; Simpson 1994 Ch.3).

### Source-to-Implementation Mapping (H3)

| Load-bearing decision | Source (report / literature / in-repo) | Consumed by phase |
|-----------------------|----------------------------------------|-------------------|
| Worlds = prime theories; `≤` = set inclusion; `canonicalVal` | Report §6.3; IntStrongCompleteness `Preorder` instance | 2a |
| `canonicalR` = box clause `□φ∈w→φ∈v` AND diamond clause `φ∈v→◇φ∈w` | Report §6.4; Simpson 1994 clauses 3.2/3.5; Wijesekera 1990 chunk 0111 (box condition); chunk 0002 (◇ primitive, non-dual) | 2a |
| Box witness: build `{ψ\|□ψ∈w}`, non-derivation via `derive_box_from_box_context`, then `modal_prime_exclusion` | Report §6.5; MCS.lean K-helpers; §4 (Peirce-free) | 2b |
| Diamond witness: extend `{ψ\|□ψ∈w}∪{φ}`, secure diamond clause, prime-exclude | Report §6.5, §10; **Wijesekera 1990 chunk 0111** (prime-filter accessibility); Simpson 1994 canonical birelation | 2c (HIGHEST RISK) |
| F1 via diamond witness, F2 via box witness | Report §6.6; Simpson 1994 F1/F2 confluence | 2d |
| 5 non-modal truth cases (atom/bot/and/or/imp) | Report §6.7, §9; IntStrongCompleteness.lean:108-214 | 3a |
| `.box` case: `canonical_box_witness` + heredity over `≤∘R`; `BForces_box` unfold | Report §6.7; Simpson 1994 clause 3.2 | 3b |
| `.diamond` case: `canonical_diamond_witness`; `BForces_diamond` unfold | Report §6.7, §10; **Wijesekera 1990** | 3c (HIGHEST RISK) |
| Parametric `ivalid`/`mvalid` completeness; `h_efq` separable; `botForces` a parameter; consistency hook | Report §7, §10 | 4 |

## Goals & Non-Goals

**Goals**:
- Complete `CanonicalModel.lean`, `TruthLemma.lean`, `Completeness.lean` sorry-free and axiom-free
  atop the preserved `PrimeTheory.lean`, each phase building independently under `lake build`.
- Keep every new framework declaration parametric over `Axioms : Proposition Atom → Prop` with base
  intuitionistic axioms as explicit `h_*` hypotheses and `h_efq` a SEPARATE hypothesis (minimal 495
  omits it); keep `botForces` a parameter of the truth lemma (CK 493 fallible-world / `MValid`).
- Provide `canonicalR` (box + diamond), the two witness lemmas, `canonical_f1`/`f2`, a single
  parametric `canonical_truth_lemma`, and parametric `ivalid`/`mvalid` completeness statements for
  492-495 to instantiate.
- Pass the full CSLib CI pipeline; docstring every new public declaration.

**Non-Goals**:
- No instantiation of concrete axiom systems (IK/CK/IT/IS4/IS5/MK) — tasks 492-495.
- No soundness/consistency discharge of any concrete `IntModalAxiom` set — framework exposes the
  hook only.
- No modification of any classical `Metalogic/` file, `MCS.lean`, the propositional `Int*` files, or
  the preserved `PrimeTheory.lean`. No new notation, typeclass, or `axiom`.

## Postmortem Constraints

Binding rules for all implementation dispatches, derived from the failed monolithic dispatch and
the research risk factors.

**Do NOT**:
- **Do NOT attempt more than one file (or, within `CanonicalModel.lean`, more than one phase's
  deliverable) per dispatch.** The prior monolithic attempt tried to land the whole of
  `CanonicalModel.lean` in one run and failed to reach a sorry-free build. Each phase below is one
  agent run.
- **Do NOT introduce `sorry`/`admit`/`axiom` to "make the module build" and defer the hard part.**
  ZERO-DEBT is a hard constraint. If a highest-risk proof (2c, 3c) will not close, invoke the STOP
  contingency below (report PARTIAL with a continuation note); never commit debt.
- **Do NOT re-open Phase 1 (`PrimeTheory.lean`).** It is committed and building. Import it; do not
  edit it. If a Phase-1 lemma signature seems wrong, report it — do not silently patch.
- **Do NOT edit `MCS.lean`, `Completeness.lean` (classical), or any propositional `Int*` file.**
  Reuse `iteratedDeduction`/`derive_box_from_box_context` by import; transliterate `int_truth_lemma`
  by copy into the new file.
- **Do NOT use `simp`/`aesop` for the non-modal truth-lemma cases.** Follow the explicit
  `DerivationTree` term-mode style of `int_truth_lemma` (report §9, literature-fidelity). `BForces_box`/
  `BForces_diamond` `@[simp]` unfolds are the only expected `simp` use, for forcing unfolds.
- **Do NOT re-derive the classical box witness via negation + Peirce.** The intuitionistic box
  witness uses `modal_prime_exclusion` (report §4). Peirce is not available.

**MUST preserve**:
- `PrimeTheory.lean` (committed, sorry-free) and every upstream file listed in Preserved Assets.
- Existing green builds of the classical `Metalogic/` subtree and the propositional `Int*` subtree
  (`git diff --stat` must show no changes to them).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- Worlds are **prime theories** (`ModalPrimeTheory`), not MCS; `≤` = set inclusion. Rejected MCS
  because intuitionistic completeness needs the disjunction property, not negation-completeness
  (report §4).
- `canonicalR` carries **both** a box clause and a diamond clause because `◇` is primitive and not
  `□`-definable (Wijesekera; report §6.4). Do not drop the diamond clause to mirror the classical
  single-clause `r`.
- `canonical_truth_lemma` is factored so each constructor case is discharged by a **named helper
  lemma taking the induction hypothesis as an explicit hypothesis** (see Phase 3a note). This is the
  mechanism that lets 3a/3b/3c each build sorry-free before the full recursion is assembled.
  Rejected the single monolithic recursion because it cannot be split across per-run phases without
  incurring `sorry`.
- `h_efq` is a SEPARATE hypothesis and `botForces` is a truth-lemma parameter (not hard-coded
  `fun _ => False`), so minimal 495 / CK 493 instantiate without framework edits (report §7).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `canonical_diamond_witness` (2c) has no classical analogue (primitive `◇`) | H | M | Isolated into Phase 2c with STOP contingency. Ground on Wijesekera 1990 chunk 0111 and report §6.4-6.5; `--lit` active. Verify the witness set `{ψ\|□ψ∈w}∪{φ}` goal shape with `lean_goal` before committing the proof. |
| `.diamond` truth-lemma case (3c) likewise | H | M | Isolated into Phase 3c with STOP contingency; depends on 2c. Use `BForces_diamond` unfold; keep the helper-lemma IH shape verified with `lean_goal`. |
| Helper-factoring IH shapes (3a/3b/3c) may not match the recursion's available IH | M | M | In each of 3a/3b/3c, confirm the helper signature against `BForces_*` unfolds and the intended recursion IH with `lean_multi_attempt`/`lean_goal` before writing the body. Assemble the recursion (3c final task) only once all helpers typecheck. |
| `canonicalR`'s two clauses must be mutually consistent with F1/F2 on prime worlds | H | M | F1 via diamond witness (2c), F2 via box witness (2b); check `BFrame.f1`/`f2` obligation shapes read from `Birelational.lean` in 2d. |
| `Birelational.lean` API drift vs report assumptions | M | L | Phase 2a first task: read `Birelational.lean`, confirm exact `BFrame`/`BModel`/`BForces`/`IValid`/`MValid` field names and `@[simp]` unfolds before wiring `canonicalR`. |
| Lint failures (docBlame, lowerCamelCase, namespace) | M | M | Docstring every new `def`/`theorem`; follow `IntStrongCompleteness.lean` conventions; run `lake exe lint-style` + `lake shake` at each phase end. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 0 | 1 | -- (COMPLETED — preserved) |
| 1 | 2a | 1 |
| 2 | 2b | 2a |
| 3 | 2c | 2a (logical); applied after 2b (same file) |
| 4 | 2d | 2b, 2c |
| 5 | 3a | 2d |
| 6 | 3b | 3a (same file) |
| 7 | 3c | 3a, 3b (same file; assembly needs all helpers) |
| 8 | 4 | 3c |

**This plan is fully sequential — each wave contains one phase.** Two structural reasons:
(1) **Same-file phases must be applied sequentially, never in parallel** — 2a/2b/2c/2d all write
`CanonicalModel.lean`, and 3a/3b/3c all write `TruthLemma.lean`; a Lean module is a single build
unit, so concurrent edits to one file cannot each build green. (2) **Import chain** — `CanonicalModel`
imports `PrimeTheory`, `TruthLemma` imports `CanonicalModel`, `Completeness` imports `TruthLemma`;
a downstream file cannot build until its upstream file builds as a whole. (Note: the 3a non-modal
truth cases do not logically use the 2b/2c witnesses, but 3a is still blocked because `TruthLemma`
cannot build until `CanonicalModel.lean` is complete — no genuine parallel opportunity exists.)

Every phase below carries the same standing gates: **ZERO-DEBT** (`grep -nE "sorry|admit"` returns
nothing; no new `axiom`), **untouched-classical** (`git diff --stat` shows no change to
`MCS.lean`, classical `Completeness.lean`, propositional `Int*`, or `PrimeTheory.lean`), and
**docstrings on all new public declarations**.

### Phase 1: PrimeTheory.lean — prime-theory machinery [COMPLETED]

- **Goal:** (preserved) intuitionistic modal prime-theory layer wrapping `prime_exclusion`.
- **Deliverable:** `PrimeTheory.lean` (done — see Preserved Assets).
- **Depends on:** none
- **Completed:** commit be8f2eb0. No action; do not modify.

### Phase 2a: CanonicalModel.lean — worlds, order, valuation, canonicalR [COMPLETED]

- **Goal:** Create `CanonicalModel.lean` and lay down the birelational canonical-frame data:
  worlds, the `≤` = inclusion `Preorder`, the valuation, and the two-clause `canonicalR` — all as
  definitions/instances, no witness proofs yet.
- **Single deliverable:** `CanonicalModel.lean` builds green containing `CanonicalPrimeWorld`, the
  `Preorder` instance, `canonicalVal`, and `canonicalR` (definitions only).
- **Tasks:**
  - [x] First: read `Cslib/Logics/Modal/Semantics/Birelational.lean`; confirm exact
        `BFrame`/`BModel`/`BForces`/`IValid`/`MValid` field names, `F1`/`F2` obligation shapes, and
        the `@[simp]` unfold lemmas (`BForces_box`/`BForces_diamond`). Record the confirmed field
        names in a comment for downstream phases.
  - [x] Create `CanonicalModel.lean` importing `PrimeTheory.lean` (Phase 1), `MCS.lean` (import-only,
        for `iteratedDeduction`/`derive_box_from_box_context` used in 2b), and `Birelational.lean`.
  - [x] Define `CanonicalPrimeWorld Axioms`, the `Preorder` = inclusion instance, and `canonicalVal`
        (copy shapes from `IntStrongCompleteness.lean`) — report §6.3.
  - [x] Define `canonicalR` with box clause `□φ∈w→φ∈v` AND diamond clause `φ∈v→◇φ∈w` — report §6.4.
  - [x] Docstrings; `lake build` the module.
- **Estimated output:** ~60-100 lines. **Done when:** `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.CanonicalModel` succeeds; `canonicalR` has both clauses; no `sorry`.
- **Timing:** ~1 hour
- **Depends on:** 1

### Phase 2b: canonical_box_witness [BLOCKED]

- **Goal:** Prove the box witness lemma.
- **Single deliverable:** `canonical_box_witness` proved sorry-free in `CanonicalModel.lean`.
- **Tasks:**
  - [x] Prove `ModalSetConsistent Axioms {ψ | □ψ ∈ w.val}` from `□φ ∉ w.val`: this direction closes
        cleanly. A deductively-closed (not MCS-based) variant of `derive_box_from_box_context` was
        devised (`derive_box_from_box_context` itself needs `SetMaximalConsistent`, unavailable for
        prime theories; the deductively-closed variant only needs `Metalogic.DeductivelyClosed`,
        which `ModalPrimeTheory`/`Admissible` already provides) plus a K-distribution + EFQ argument
        that `□⊥ ∈ w.val → □χ ∈ w.val` for every `χ`, giving `□⊥ ∉ w.val` (hence `⊥ ∉ W`) from the
        `□φ ∉ w.val` hypothesis.
  - [ ] **BLOCKED**: apply `modal_prime_exclusion` to `W = {ψ|□ψ∈w.val}` and verify the resulting
        prime `v ⊇ W` (excluding `φ`) satisfies **both** clauses of `canonicalR w v` — not just the
        box clause. See blocker note below; this blocks the remainder of Phase 2b and all of
        2c/2d/3b/3c/4.
  - [ ] Docstring; `lake build` the module.
- **Estimated output:** ~80-140 lines. **Done when:** module builds; `canonical_box_witness` typechecks; no `sorry`.
- **Timing:** ~1 hour
- **Depends on:** 2a

**BLOCKER** (Phase 2b):
- **What failed**: `modal_prime_exclusion` applied to `modalDeductiveClosure Axioms W` (or any prime
  extension of it) only secures the **box clause** of `canonicalR w v`
  (`∀ψ, □ψ ∈ w.val → ψ ∈ v.val`, by construction of `W`). It does **not** secure the **diamond
  clause** (`∀ψ, ψ ∈ v.val → ◇ψ ∈ w.val`), which `canonicalR`'s definition (Simpson 1994, Ch. 3,
  p. 53: `X R Y iff {□A|A∈Y}⊆X and {◇A|A∈Y}⊆X`, i.e. box-clause AND diamond-clause) requires
  simultaneously for the SAME pair `(w, v)`.
- **What was tried**:
  1. Confirmed the exact two-clause `canonicalR` definition against literature (Simpson 1994,
     `~/Projects/Literature/simpson_1994_intuitionisticmodallogic/chunk_0223.md`, the canonical
     birelational model `B=(W,≤,R,V)` for IK), resolving OCR ambiguity (□ vs ◇ glyphs) via
     cross-checking against the box truth-lemma's well-known standard direction.
  2. Analyzed the truth lemma dependency: both directions of the `.box` case and both directions of
     the `.diamond` case require a witness world `v` satisfying the *full* `canonicalR w v` (both
     clauses simultaneously) — there is no way to discharge either truth-lemma direction using only
     one clause.
  3. Identified the specific obstruction: since `v.val` is deductively closed, it always contains
     `⊤` (`⊥→⊥`, a bare `implyK`/`implyS` theorem, `S K K`-style, independent of any world). The
     diamond clause therefore always demands `◇⊤ ∈ w.val` as a precondition of `canonicalR w v`
     holding for *any* `v`. `◇⊤` is not a bare `implyK`/`implyS`/`efq`/`orE` theorem, nor (as far as
     could be established) a consequence of the reported IK axiom set (`K-□`, `K-◇`
     (`□(A→B)→(◇A→◇B)`), `◇⊥→⊥`, `◇(A∨B)→◇A∨◇B`) without an explicit seriality-style axiom
     (`□φ→◇φ`), which the report does not list as part of IK's base and which CK explicitly does
     not have (CK is reported to be weaker than IK, admitting fallible/exploding worlds).
  4. Showed `◇⊤ ∉ w.val → ∀φ, ◇φ ∉ w.val` follows from `K-◇` (instantiating `A:=φ,B:=⊤` against the
     bare theorem `⊢φ→⊤`), i.e. a world lacking `◇⊤` lacks *every* diamond fact — consistent, but
     does not resolve whether such a world can simultaneously have `□φ ∉ w.val` for some `φ` (which
     is exactly the scenario `canonical_box_witness` must handle, and for which it would need to
     produce a witness it cannot semantically produce without `◇⊤ ∈ w.val`).
  5. Considered moving the witness to some `w' ⊋ w` (rather than `w' := w`) where `◇⊤` might hold,
     but could not establish, from the base axioms alone, that such an extension is always
     available whenever `□φ ∉ w.val`, nor rule out a prime theory `w` with `□φ ∉ w.val` for some
     `φ` for which **no** extension secures `◇⊤` (which would make the birelational truth lemma
     false as stated for such `w`, not merely hard to formalize).
- **Why it's stuck**: this is a genuine mathematical question about the IK/CK axiomatization (not a
  Lean tactic/API problem): whether the reported axiom set forces every prime theory with
  `□φ ∉ w.val` (for some `φ`) to also satisfy `◇⊤ ∈ w.val`, and if not, what the correct
  (axiom-parametric) precondition or alternative `canonicalR` formulation is. Simpson's own proof
  of the analogous fact for **F2** (down-confluence; chunk_0223-0227) invokes "axiom 5 of IK" in a
  multi-step, OCR-garbled derivation (ambiguous `□`/`◇`/`Q`/`O` glyphs, uncertain premise counts)
  that could not be reconstructed with confidence sufficient for a zero-debt Lean proof.
- **What is needed**: a literature-grounded resolution of one of:
  (a) an explicit derivation, from IK's/CK's stated axioms, that `◇⊤` (or an equivalent
      seriality-like fact) is always available when needed by `canonical_box_witness`/
      `canonical_diamond_witness`/`canonical_f1`/`canonical_f2`; or
  (b) a corrected `canonicalR` definition (still matching [Simpson1994]/[Wijesekera1990]) under
      which the witness constructions do not require this precondition; or
  (c) confirmation (with a cleaner, non-OCR source if available — e.g. a secondary paper
      reproducing Simpson's Definition/Lemma 3.3.x verbatim, or Wolter & Zakharyaschev's survey of
      IK-style canonical models) of the exact multi-step argument Simpson uses for `(F2)` (and by
      analogy the box/diamond witnesses), so it can be transliterated faithfully.
  Recommended: `/research 480 --hard --lit` focused narrowly on this specific question (not the
  general "diamond witness has no classical analogue" framing from the v1/v2 plans — the finding
  above is more precise: **whether/how the IK-◇ axiom set discharges a seriality-style precondition
  needed by *both* witnesses**), consulting `wijesekera_1990_constructivemodallogicsi` chunks
  around 0040-0045 (prime-filter accessibility) and any secondary IK-canonical-model source with
  cleaner OCR/typesetting than the current `simpson_1994_intuitionisticmodallogic` scan.
- **Prohibited workarounds**: did NOT use `sorry`, `def X := True`, or any vacuous placeholder to
  paper over this. `CanonicalModel.lean` remains exactly as committed at Phase 2a (`4fd37213`):
  definitions only, no witness proofs attempted in the file itself.

**UPDATE (second Phase 2b dispatch) — root cause identified, concrete fix known, still BLOCKED
on missing infrastructure**:

- **The `◇⊤` framing above was a red herring caused by an unnecessary assumption.** The prior
  dispatch implicitly assumed the witness pair must be `(w, v)` with `w` **unchanged** (`w' := w`).
  That assumption is false and is exactly why the `◇⊤`-precondition seemed unavoidable: with `w`
  fixed, `v`'s content (beyond `{ψ|□ψ∈w.val}`) is uncontrolled, so nothing forces `∀χ∈v, ◇χ∈w.val`.
- **Verified fix, cross-checked against a working reference formalization**
  (`github.com/ianshil/CK`, Coq mechanization of CK/IK completeness for exactly this birelational,
  prime-theory canonical model; file `theories/Completeness_th/general_th_completeness.v`, the
  `cmreach`/`truth_lemma` "Box ψ" case, lines ~140-200). Its `cmreach` relation is *definitionally
  identical* to our `canonicalR` (`(∀A,□A∈th P0→A∈th P1) ∧ (∀A,A∈th P1→◇A∈th P0)`), confirming
  Phase 2a's `canonicalR` is correct. Its box-witness construction, transliterated to our setting:
  1. **Step 1** (this is exactly the already-`[x]`-checked task above): build `u` via
     `modal_prime_exclusion` on `{ψ|□ψ∈w.val}` excluding `φ`, giving `{ψ|□ψ∈w.val} ⊆ u.val` and
     `φ ∉ u.val`. (Matches Coq's `Lindenbaum_cworld` call producing `w` there.)
  2. **Step 2 (the missing piece)**: build a **second, SEEDED world `w'`** extending `w` — i.e.
     `w' ≥ w` in the canonical `Preorder`, **not `w' = w`** — as a prime extension of
     `w.val ∪ {◇A | A ∈ u.val}` (seeding `w'` with the diamond-image of `u`'s content *directly
     secures the diamond clause of `canonicalR w' u` by construction*, since every `A ∈ u.val` then
     has `◇A ∈ w'.val` trivially), **while simultaneously excluding the whole set**
     `Σ := {□B | B ∉ u.val}` (so that `w'`'s box-context stays bounded by `u.val`, securing the
     *box* clause of `canonicalR w' u`). Consistency of `w.val ∪ {◇A|A∈u.val}` relative to
     excluding `Σ` is where axiom `K◇` (`□(A→B)→(◇A→◇B)`) is used (Coq's proof, same file, uses the
     analogous `Kd`/`K_rule` lemmas).
  3. The final witness is `⟨w', u⟩` with `w ≤ w'` and `canonicalR w' u ∧ φ ∉ u.val` — **not**
     `⟨w, v⟩` as the v1/v2 plan sketch and report §6.5 assumed. This is consistent with `BForces_box`
     unfolding to `∀w'≥w, ∀u, r w' u → force u φ` (already documented in the Phase 2a docstring) —
     the outer `∀w'≥w` is not vacuous/decorative, it is *load-bearing* and is exactly what the truth
     lemma's box case (Phase 3b) will consume.
  4. **This resolves the `◇⊤` framing entirely**: `w'` is built fresh with whatever diamond content
     `u` needs; `w`'s own pre-existing content is never required to already contain `◇⊤` or any
     other diamond fact.
- **The genuine remaining gap is infrastructure, not mathematics**: step 2's "exclude the whole set
  `Σ = {□B|B∉u.val}`" cannot be done with `modal_prime_exclusion` (`PrimeTheory.lean`) or
  `Metalogic.prime_exclusion` (`Foundations/Logic/Metalogic/PrimeExclusion.lean`) as they exist
  today — both exclude a **single** formula `phi`, not an arbitrary set `Σ`. The Coq reference uses
  a strictly more general "Lindenbaum pair" lemma (`Lindenbaum_pair` / `pair_extCKH_prv`: given
  `Γ ⊬ Σ` — no finite subset of `Γ` derives any finite disjunction of `Σ` — produce a prime
  `T ⊇ Γ` with `T ∩ Σ = ∅`). **No such lemma currently exists anywhere in Cslib.** Adding it is a
  natural, self-contained generalization of `Metalogic.prime_exclusion`'s existing Zorn's-lemma
  argument (swap the domain `{T|S⊆T∧Admissible D Cons T∧phi∉T}` for
  `{T|S⊆T∧Admissible D Cons T∧Σ∩T=∅}` and adapt the cut/EFQ-bridge lemmas from single-formula to
  finite-disjunction form), but it is foundational, shared (`Foundations/Logic/Metalogic/`), and
  estimated at 150+ lines — well beyond one bounded phase, and out of the single-file scope this
  dispatch was territory-bounded to (`CanonicalModel.lean` only; `PrimeExclusion.lean` is
  load-bearing shared infrastructure used by every other Metalogic file in the repo, so extending it
  needs its own reviewed phase).
- **Recommended concrete next steps** (supersedes the "narrow `/research`" recommendation above,
  which is no longer necessary — the literature question is resolved):
  1. New phase (or new task, e.g. via `/spawn 480 "need Lindenbaum-pair prime exclusion"`): add
     `Metalogic.prime_pair_exclusion` (name illustrative) to `PrimeExclusion.lean`:
     `Admissible D Cons S → S ∩ Σ = ∅ → (∀ Σ' : List F, (∀x∈Σ',x∈Σ) → ¬ D.Deriv (S-as-context) (list_disj Σ')) → ∃ T, S⊆T ∧ PrimeAdmissible D Cons T ∧ T∩Σ=∅`
     (exact non-derivability hypothesis shape TBD by whoever implements it; mirror
     `Lindenbaum_pair`/`pair_extCKH_prv` from `ianshil/CK` for the precise formulation that composes
     cleanly with Zorn's lemma).
  2. Re-dispatch Phase 2b (and, by the same construction, 2c) using the seeded-`w'` technique above
     plus the new lemma. Expect `canonical_box_witness`'s corrected signature to be
     `∃ w' v : CanonicalPrimeWorld Axioms, w ≤ w' ∧ canonicalR w' v ∧ φ ∉ v.val` (not
     `∃ v, canonicalR w v ∧ φ∉v.val` as originally sketched) — Phase 3b's "`canonical_box_witness` +
     heredity over `≤∘R`" note already anticipated needing a `≤`-step, so this is a **refinement of
     the plan, not a re-opening**: no design decision listed in Postmortem Constraints is
     contradicted; `canonicalR`'s two-clause definition (Phase 2a) is unchanged and confirmed correct
     by the reference formalization.
  3. `canonical_diamond_witness` (2c) will need the mirror-image construction (seed the *box*-side
     instead of the diamond-side); the same new pair-exclusion lemma covers it.
- Still **no `sorry`/`admit`/`axiom` introduced**; `CanonicalModel.lean` is still byte-for-byte
  unchanged from Phase 2a (`4fd37213`).

### Phase 2c: canonical_diamond_witness [NOT STARTED] — HIGHEST RISK

- **Goal:** Prove the diamond witness lemma (primitive `◇`, no classical analogue).
- **Single deliverable:** `canonical_diamond_witness` proved sorry-free in `CanonicalModel.lean`.
- **Tasks:**
  - [ ] Before writing the body, use `lean_goal`/`lean_multi_attempt` to confirm the goal shape for
        the witness set `{ψ | □ψ ∈ w} ∪ {φ}` and the diamond-clause obligation.
  - [ ] Prove `canonical_diamond_witness`: from `◇φ ∈ w` extend `{ψ | □ψ ∈ w} ∪ {φ}`, secure the
        diamond clause `(∀χ, χ∈v → ◇χ∈w)`, apply `modal_prime_exclusion` — report §6.5, §10;
        Wijesekera 1990 chunk 0111.
  - [ ] Docstring; `lake build` the module.
- **Estimated output:** ~120-200 lines. **Done when:** module builds; `canonical_diamond_witness` typechecks; no `sorry`.
- **Timing:** ~1.25 hours
- **Depends on:** 2a (logical); apply after 2b (same file)
- **STOP / partial contingency:** If the diamond witness cannot be closed sorry-free within the run,
  **STOP — do not introduce `sorry`.** Commit the sorry-free state (Phases 2a+2b), mark this phase
  `[PARTIAL]`, and write a continuation note (which sub-goal is stuck, the exact `lean_goal` output)
  to the orchestrator handoff. Recommended next: `/research 480 --hard --lit` focused narrowly on
  the Wijesekera prime-filter diamond-accessibility construction (chunk 0111) before re-dispatch.

### Phase 2d: canonical_f1 + canonical_f2 [NOT STARTED]

- **Goal:** Prove the two frame conditions, completing `CanonicalModel.lean`.
- **Single deliverable:** `canonical_f1` and `canonical_f2` proved; `CanonicalModel.lean` final.
- **Tasks:**
  - [ ] Prove `canonical_f1` (up-confluence): transport a diamond witness (2c) along inclusion —
        report §6.6.
  - [ ] Prove `canonical_f2` (down-confluence): via the box witness (2b) — report §6.6.
  - [ ] Confirm both typecheck against the `BFrame.f1`/`BFrame.f2` obligation shapes read in 2a.
  - [ ] Docstrings; `lake build` the module.
- **Estimated output:** ~80-140 lines. **Done when:** module builds; both frame conditions match `BFrame` obligations; no `sorry`.
- **Timing:** ~1 hour
- **Depends on:** 2b, 2c

### Phase 3a: TruthLemma.lean — 5 non-modal case helpers [NOT STARTED]

- **Goal:** Create `TruthLemma.lean` and prove the five non-modal truth-lemma cases as standalone
  helper lemmas.
- **Design note (SETTLED):** Each case is a named helper lemma. Cases whose proof needs the
  induction hypothesis (`and`/`or`/`imp`) take the relevant IH (truth-lemma equivalence at the
  subformula(s), over the appropriate worlds) as an **explicit hypothesis parameter**. This lets 3a
  build green before the full `canonical_truth_lemma` recursion exists (assembled in 3c). Confirm
  each helper signature with `lean_goal` against the `BForces` unfolds before writing bodies.
- **Single deliverable:** `TruthLemma.lean` builds green containing the five helpers
  (`atom`/`bot`/`and`/`or`/`imp`).
- **Tasks:**
  - [ ] Create `TruthLemma.lean` importing `CanonicalModel.lean` (Phase 2).
  - [ ] Transliterate the `atom`/`bot`/`and`/`or`/`imp` cases line-for-line from
        `IntStrongCompleteness.lean:108-214` (`PL.Proposition`→`Modal.Proposition`,
        `IntPropAxiom`→`Axioms`) into helper lemmas; keep `botForces` a parameter (default
        `fun _ => False`, NOT hard-coded) — report §6.7, §7. Explicit `DerivationTree` term-mode
        style; no `simp`/`aesop`.
  - [ ] Docstrings; `lake build` the module.
- **Estimated output:** ~150-250 lines. **Done when:** module builds; five helpers typecheck; `botForces` is a parameter; no `sorry`.
- **Timing:** ~1.25 hours
- **Depends on:** 2d

### Phase 3b: .box case helper [NOT STARTED]

- **Goal:** Prove the `.box` truth-lemma case as a helper lemma.
- **Single deliverable:** `truth_box_case` (or equivalent) proved sorry-free in `TruthLemma.lean`.
- **Tasks:**
  - [ ] Prove the `.box` helper using `canonical_box_witness` (2b) + heredity over `≤∘R`; unfold with
        `BForces_box` — report §6.7. Take the IH as an explicit hypothesis (see 3a design note).
  - [ ] Docstring; `lake build` the module.
- **Estimated output:** ~60-120 lines. **Done when:** module builds; box helper typechecks; no `sorry`.
- **Timing:** ~0.75 hour
- **Depends on:** 3a

### Phase 3c: .diamond case helper + assemble canonical_truth_lemma [NOT STARTED] — HIGHEST RISK

- **Goal:** Prove the `.diamond` truth-lemma case, then assemble the full parametric
  `canonical_truth_lemma` recursion dispatching to all seven helpers.
- **Single deliverable:** `truth_diamond_case` proved and `canonical_truth_lemma` assembled
  sorry-free; `TruthLemma.lean` final.
- **Tasks:**
  - [ ] Before writing, confirm the diamond helper goal shape with `lean_goal` (`BForces_diamond`
        unfold; IH over `R`).
  - [ ] Prove the `.diamond` helper using `canonical_diamond_witness` (2c) — report §6.7, §10;
        Wijesekera 1990.
  - [ ] Assemble `canonical_truth_lemma` by induction on `Proposition`, dispatching each constructor
        to its helper (3a/3b + this). Confirm all seven constructors are covered (no missing-case
        warning). This assembly is mechanical once all helpers typecheck.
  - [ ] Docstrings; `lake build` the module.
- **Estimated output:** ~100-180 lines. **Done when:** module builds; `canonical_truth_lemma` covers all seven constructors; `botForces` still a parameter; no `sorry`.
- **Timing:** ~1 hour
- **Depends on:** 3a, 3b
- **STOP / partial contingency:** If the diamond case cannot be closed sorry-free, **STOP — do not
  introduce `sorry`.** Commit the sorry-free state (3a+3b helpers), mark `[PARTIAL]`, and write a
  continuation note (stuck sub-goal, `lean_goal` output) to the handoff. The `canonical_truth_lemma`
  assembly is deferred with it (it needs the diamond helper). Recommended next: narrow
  `/research 480 --hard --lit` on the Wijesekera `.diamond` forcing clause before re-dispatch.

### Phase 4: Completeness.lean — parametric packaging [NOT STARTED]

- **Goal:** Package the canonical `BModel` and expose parametric `ivalid`/`mvalid` completeness plus
  the consistency hook for tasks 492-495.
- **Single deliverable:** `Completeness.lean` builds green; full CI pipeline passes.
- **Tasks:**
  - [ ] Create `Completeness.lean` importing `TruthLemma.lean` (Phase 3).
  - [ ] Assemble the canonical `BModel` from `CanonicalPrimeWorld`, the `Preorder`, `canonicalR`,
        `canonicalVal`, and `canonical_f1`/`f2`.
  - [ ] State parametric `ivalid_completeness` / `mvalid_completeness` (from `canonical_truth_lemma`
        + `modal_prime_exclusion` on the underivable formula) with base-axiom and `h_efq` (IValid) /
        arbitrary-`botForces` (MValid) hypotheses exposed for 492-495 — report §7.
  - [ ] Expose a consistency hook (parametric statement, discharged by 492/493, not here) — §10.
  - [ ] Docstrings; `lake build`; run the full CI pipeline; confirm ZERO-DEBT + untouched-classical.
- **Estimated output:** ~80-150 lines. **Done when:** module builds; `ivalid_completeness`/`mvalid_completeness` typecheck as parametric statements; full CI green; no `sorry`.
- **Timing:** ~1.25 hours
- **Depends on:** 3c

## Testing & Validation

- [ ] `lake build` succeeds for all four modules (whole-tree build green).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes (all new decls docstringed).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused-import issues on the
      new subtree.
- [ ] ZERO-DEBT: `grep -rnE "sorry|admit" Cslib/Logics/Modal/Metalogic/Intuitionistic/` returns
      nothing; no new `axiom` declarations.
- [ ] Untouched-classical: `git diff --stat` shows no changes to any existing file under
      `Cslib/Logics/Modal/Metalogic/` (except the new `Intuitionistic/` files), to `MCS.lean`, or to
      the propositional `Int*` files; `PrimeTheory.lean` unchanged from be8f2eb0.
- [ ] Parametricity: each new framework lemma carries `Axioms` + explicit `h_*` base-axiom
      hypotheses with `h_efq` separable and `botForces` a parameter (readable from signatures).

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` (Phase 1, preserved)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` (Phases 2a-2d)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean` (Phases 3a-3c)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean` (Phase 4)
- `specs/480_intuitionistic_modal_framework/plans/02_intuitionistic-modal-framework-hard.md` (this plan)
- `specs/480_intuitionistic_modal_framework/summaries/02_intuitionistic-modal-framework-summary.md` (on completion)

## Rollback/Contingency

- All work is additive under `Intuitionistic/`; no classical file is edited. Rollback = revert the
  new files after Phase 1; no regression risk to existing proofs.
- **Per-phase STOP rule (ZERO-DEBT):** any phase that cannot reach a sorry-free build STOPS, commits
  the last green state, marks itself `[PARTIAL]`, and records a continuation note. Never commit
  `sorry`/`admit`/`axiom`. The two highest-risk phases (2c, 2d/3c chain) carry explicit narrow-research
  fallbacks (see their STOP contingencies).
- If `Birelational.lean` API diverges materially from report assumptions (discovered in Phase 2a),
  mark the task `[BLOCKED]` on task 490 rather than reconstructing the semantics here.
