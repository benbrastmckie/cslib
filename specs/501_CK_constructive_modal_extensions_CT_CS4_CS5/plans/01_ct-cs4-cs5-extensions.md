# Implementation Plan: Task #501 — CK Constructive Modal Extensions CT / CS4 / CS5

- **Task**: 501 - CK constructive modal extensions CT / CS4 / CS5 (sound + complete axiomatizations of constructive T/S4/S5 as modular extensions of CK, task 493)
- **Status**: [IMPLEMENTING]
- **Effort**: 13.5 hours
- **Dependencies**: Task 493 (CK segment core — merged, files present under `Cslib/Logics/Modal/Metalogic/Constructive/`)
- **Research Inputs**: specs/501_CK_constructive_modal_extensions_CT_CS4_CS5/reports/01_ct-cs4-cs5-segment-extensions.md
- **Artifacts**: plans/01_ct-cs4-cs5-extensions.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Formalize sound-and-complete axiomatizations of the constructive analogues of T, S4, and S5
(CT / CS4 / CS5) as modular extensions of task 493's CK, over the Wijesekera-style
fallible-world SEGMENT semantics (`CKForces`: ∀∃ diamond, no F1/F2 confluence, plus the three
explosion conditions restricted to FC-frames). Each system adds a box-form and a diamond-form
axiom to `CKModalAxiom`, a frame-condition predicate stated in **≤-composed (order-saturated)
form**, a soundness proof over `CKForces`, and a completeness proof whose canonical model is
built over a **restricted world subtype** carrying the frame condition as an invariant (the
primary challenge — the FC does NOT hold globally on the raw `CKSegment` type). Four new files
under `Cslib/Logics/Modal/Metalogic/Constructive/`: `CKExtension.lean` (scaffold), `CT.lean`,
`CS4.lean`, `CS5.lean`, wired into `Cslib.lean`. Definition of done: `lake build` +
`checkInitImports` + `lint-style` + `shake` + `test` all green, zero `sorry`, zero new axioms,
zero warnings.

### Research Integration

This plan integrates report `01_ct-cs4-cs5-segment-extensions.md` in full. Load-bearing findings
that constrain every phase:

- **Segment reuse, NOT birelational (report §Executive Summary, D1).** Extend task 493's
  `Constructive/` segment core (`CKSegment`, `cmreach`, `cval`, `cbotForces`, `ck_truth_lemma`,
  `segment_realization`, all Lindenbaum/refuting lemmas — all already `{Axioms}`-parametric). Do
  NOT import or reuse task 494's birelational `IValidFC`/`Intuitionistic/Extension.lean`
  scaffold; it is a STRUCTURAL template only (bare CK is incomplete for `BForces` — Cd/Idb are
  birelationally valid but not derivable, and adding T/4/B does not derive them).
- **≤-composed frame conditions (report D3.2).** Box-form axioms need the order-saturated FC
  clause; diamond-form axioms need only the plain clause (which the ≤-composed one implies via
  `le_refl`). One predicate serves both soundness directions. Define FC predicates **locally**;
  do NOT use Mathlib `Reflexive`/`Transitive`/`Symmetric` (deprecated in the pinned Mathlib —
  would break the zero-warnings gate).
- **World-subtype completeness (report D3.4, PRIMARY CHALLENGE).** The FC fails globally on raw
  `CKSegment` (a consistent-head segment with tail `{Set.univ}` is well-formed but not
  `cmreach`-reflexive). Build each canonical model over a restricted subtype (e.g. `CTSegment`
  carrying `seg.head ∈ seg.tail`) and transport the truth lemma along the `.seg` projection.
- **CS5 via B/symmetry, NOT euclidean-5 (report D3.1, Risk 5).** Symmetry closure is fully
  positive (MP-only); euclidean-5 closure needs negation-completeness unavailable to quasi-prime
  theories. Refl+trans+symm = equivalence = Simpson's constructive S5 frame class.
- **No new Mathlib API required (report D4).** Everything is set-theoretic + `Preorder`
  (`Preorder.lift` for the subtype instance).

### Prior Plan Reference

No prior plan. This is the first plan for task 501.

### Roadmap Alignment

No `roadmap_path` supplied in delegation context and `roadmap_flag` not set. Task 501 completes
the CK column of the constructive modal cube (CK analogue of task 494 for IK, task 496 for
minimal) per the task description, but no ROADMAP.md consultation was requested for this plan.

## Goals & Non-Goals

**Goals**:
- `CKExtension.lean`: `CKValidFC (FC) φ`, the FC predicates `ctFC`/`cs4FC`/`cs5FC` (≤-composed),
  a parametric `ckvalidFC_completeness`, and `axiom_mem_head : Axioms φ → φ ∈ s.head`.
- `CT.lean`: `CTModalAxiom` (+ `tBox`, `tDia`), `ct_axiom_sound`/`ct_soundness`/
  `ct_soundness_derivable`, `CTSegment` world subtype + invariant discharge, `ct_completeness`,
  `ct_consistent`, `ct_soundness_completeness`.
- `CS4.lean`: `CS4ModalAxiom` (+ `fourBox`, `fourDia`), soundness, transitivity-invariant
  subtype + completeness/consistency/biconditional.
- `CS5.lean`: `CS5ModalAxiom` (+ `bBox`, `bDia`; B, not euclidean-5), soundness, symmetry-invariant
  subtype + completeness/consistency/biconditional.
- Barrel wiring into `Cslib.lean`; full CI pipeline green; zero `sorry`, zero new axioms, zero
  warnings.

**Non-Goals**:
- Re-deriving any part of the task 493 segment core (it is reused verbatim at each extension's
  `Axioms`).
- Importing or depending on task 494's birelational `Intuitionistic/` scaffold.
- Axiomatizing CS5 via the euclidean/5 axiom `◇A→□◇A` (B/symmetry is used instead).
- Adding any new Mathlib API or using deprecated `Reflexive`/`Transitive`/`Symmetric`.
- Proving with `sorry` or introducing an axiom to force a closure through (blocked closures are
  marked [BLOCKED] with goal state).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| CS5 symmetry invariant on `cmreach` (tail membership) does not close positively (report Risk 1, HIGH) | H | M | Phase 7 carries an explicit STOP/[BLOCKED] contingency: if the ≤-composed symmetry clause cannot be discharged positively over the restricted tail, mark Phase 7 [BLOCKED] with the exact goal state — NO `sorry`, NO axiom. Phases 1-6 + CT/CS4 remain fully green and committable. |
| CS4/CS5 `diamRefutingSegment` restricted-tail FC-closure (report Risk 2, MED) | M | M | The maximal `ofHead` tail is straightforwardly FC-closed; if the restricted (witness-omitting) tail resists transitive/symmetric closure, the truth-lemma diamond-backward case may need a frame-condition-aware refuting segment. Isolate this in the CS4 completeness phase and reuse the pattern for CS5. |
| Truth-lemma transport to world subtype introduces rewrite friction (report Risk 3, MED) | M | L | Use `Preorder.lift (·.seg)` so subtype `≤` agrees definitionally with head inclusion; keep `ck_truth_lemma` on `CKSegment` and wrap only the completeness application over the subtype (transport along `.seg`). |
| Frame condition stated in plain (non-≤-composed) form fails box-form soundness | H | L | Follow report D3.2/D3.3 exactly: box-form axioms use the ≤-composed clause; verify each soundness case against the hand-derived clauses in D3.3 before moving on. |
| Deprecated Mathlib `Reflexive`/`Transitive`/`Symmetric` breaks zero-warnings gate | M | L | Define all FC predicates locally as `def`s over `[Preorder World]`, exactly as IT/IS4/IS5 do. |
| Missing docstring / lowerCamelCase violation fails `lake lint` | L | M | Every new declaration gets a docstring (docBlame); keep the established `ck_`/`it_` underscore convention for theorem names; run lint per phase. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |
| 8 | 8 | 1, 2, 3, 4, 5, 6, 7 |

Phases within the same wave can execute in parallel. This plan is strictly sequential: the
import chain `CK ← CKExtension ← CT ← CS4 ← CS5` and the shared-file territory (axioms and
completeness for each system live in one file) force one phase per wave until the final barrel
phase. Phase 8 depends on all prior phases. If Phase 7 is [BLOCKED], Phase 8 wires and CI-checks
Phases 1-6 (CKExtension + CT + CS4 + CS5 axioms/soundness) and records CS5 completeness as the
open item.

### Phase 1: `CKExtension.lean` scaffold [COMPLETED]

**Goal**: Create the segment analogue of task 494's `Extension.lean`: the FC-restricted validity
predicate, the three ≤-composed frame-condition predicates, the parametric completeness lemma
skeleton, and the segment `axiom_mem` analogue. No axioms/soundness yet.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean`; begin `import Cslib.Init`
      and import the task 493 segment modules (`Forcing`, `Segment`, `SegmentLindenbaum`,
      `CKTruthLemma`, `CK` as needed). Namespace `Cslib.Logic.Modal`.
- [ ] Define `CKValidFC {World} [Preorder World] (FC) (r) (val) (botForces) φ` as a copy of
      `CKValid` (`Forcing.lean:159`) with one extra hypothesis `FC r` threaded alongside the three
      explosion conditions. Ensure `CKValid = CKValidFC (fun _ => True)` holds definitionally
      (report D3.3).
- [ ] Define the ≤-composed FC predicates over `[Preorder World]` (report D3.2), each a local
      `def` (NOT Mathlib `Reflexive`/`Transitive`/`Symmetric`):
      `ctFC r := ∀ w, r w w`;
      `cs4FC r := (∀ w, r w w) ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)`;
      `cs5FC r := ctFC-clause ∧ cs4FC-trans-clause ∧ (∀ {w u u'}, r w u → u ≤ u' → r u' w)`.
- [ ] State the parametric `ckvalidFC_completeness` (segment analogue of `ivalidFC_completeness`):
      generalize `ck_completeness` (`CK.lean:240`) to take `h_canonFC : FC (canonical cmreach)` and
      thread it into the `CKValidFC` application; reuse `segment_realization` + `ck_truth_lemma`
      machinery unchanged. Keep the model quantification abstract enough to be instantiated over a
      world subtype in later phases (report D3.4).
- [ ] Add `axiom_mem_head {Axioms} (s : CKSegment Axioms) : Axioms φ → φ ∈ s.head` (segment analogue
      of task 494's `axiom_mem`; the one-liner every per-extension canonical-closure proof uses),
      built from `mem_of_axiom`/`mem_head_mp` (`CKTruthLemma.lean`).
- [ ] Docstring every declaration; keep declaration names in the established convention.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` (create) — `CKValidFC`,
  `ctFC`/`cs4FC`/`cs5FC`, `ckvalidFC_completeness`, `axiom_mem_head`.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CKExtension` compiles with zero errors,
  zero warnings, zero `sorry`.
- `CKValid = CKValidFC (fun _ => True)` checks (definitional or one-line proof).
- `lean_diagnostic_messages` on the file shows no issues; docstrings present (no docBlame).

### Phase 2: CT axioms + soundness [COMPLETED]

**Goal**: Define `CTModalAxiom` and prove soundness over `CKForces` for the two new T cases.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CT.lean`; `import Cslib.Init` + import
      `CKExtension`. Namespace `Cslib.Logic.Modal`.
- [ ] Define `inductive CTModalAxiom : Proposition Atom → Prop` = the 11 bare-CK constructors
      verbatim (`implyK`, `implyS`, `efq`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `k`,
      `kdia`) + `tBox (φ) : (□φ).imp φ` + `tDia (φ) : φ.imp (◇φ)` (report D3.1).
- [ ] Prove `ct_axiom_sound`: the 11 shared cases verbatim from `ck_axiom_sound`
      (`CK.lean:149–183`) with the `ctFC r` hypothesis threaded (unused in shared cases); plus:
      - `tBox`: `intro w' _ hbox; exact hbox w' (le_refl w') w' (hrefl w')` (plain reflexivity).
      - `tDia`: `intro w' _ hφ w'' hw''; exact ⟨w'', hrefl w'', ckforces_persistence … hw'' hφ⟩`
        (reflexivity + persistence), per report D3.3.
- [ ] Prove `ct_soundness` (structural recursion over `DerivationTree`, copy `ck_soundness`
      `CK.lean:189` threading the FC hypothesis) and `ct_soundness_derivable`.
- [ ] Docstring all new declarations.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CT.lean` (create) — `CTModalAxiom`, `ct_axiom_sound`,
  `ct_soundness`, `ct_soundness_derivable`.

**Verification**:
- `lake build …Constructive.CT` compiles; the two new soundness cases discharge exactly as in
  report D3.3 (verify goal states with `lean_goal` if needed).
- Zero errors/warnings/`sorry`; docstrings present.

### Phase 3: CT world subtype + completeness [COMPLETED]

**Goal**: Build the CT canonical model over a restricted world subtype carrying the T-invariant,
transport the truth lemma, and prove completeness/consistency/biconditional.

**Tasks**:
- [ ] Define the CT world subtype in `CT.lean` (report D3.4):
      `structure CTSegment where seg : CKSegment CTModalAxiom; refl : seg.head ∈ seg.tail`
      (`refl ≡ cmreach seg seg`); `instance : Preorder CTSegment := Preorder.lift (·.seg)`;
      `ctMreach`/`ctVal`/`ctBot` as `cmreach`/`cval`/`cbotForces` on `.seg`.
- [ ] Prove `ctFC ctMreach` (immediate from the `refl` field: `∀ P, P.seg.head ∈ P.seg.tail`).
- [ ] Discharge the invariant for every constructed segment (report D3.4 obligations 1a–1c): show
      `boxInv H ⊆ H` for every quasi-prime `H` (deductively closed + `tBox`-closed via MP,
      `mem_head_mp`/`axiom_mem_head`), giving `refl` for `CKSegment.ofHead`; show
      `diamRefutingSegment` satisfies `refl` using `boxInv s.head ⊆ s.head` (T) plus `A ∉ s.head`
      (from `◇A ∉ s.head` + `tDia`); show `cexpl` satisfies `refl` (`Set.univ ∈ {Set.univ}`).
- [ ] Transport `ck_truth_lemma` to `CTSegment` (report D3.4 obligation 2; report Risk 3): keep the
      truth lemma on `CKSegment CTModalAxiom` and wrap the completeness application over the
      subtype along `.seg`; verify `Preorder.lift` `≤` agrees definitionally with head inclusion.
- [ ] Prove `ct_completeness` by instantiating `ckvalidFC_completeness ctFC (dischargers…)` with
      the `ctFC ctMreach` proof; prove `ct_consistent` via the trivial one-point infallible model
      (copy `ck_consistent` `CK.lean:262`; FC holds trivially on a one-point reflexive frame); prove
      `ct_soundness_completeness` biconditional.
- [ ] Docstring all new declarations.

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CT.lean` (extend) — `CTSegment`, `Preorder` instance,
  `ctMreach`/`ctVal`/`ctBot`, invariant discharge lemmas, truth-lemma transport, `ct_completeness`,
  `ct_consistent`, `ct_soundness_completeness`.

**Verification**:
- `lake build …Constructive.CT` green; `ct_soundness_completeness` type-checks as a biconditional.
- Zero errors/warnings/`sorry`; no deprecated-API warnings; docstrings present.

### Phase 4: CS4 axioms + soundness [COMPLETED]

**Goal**: Define `CS4ModalAxiom` and prove soundness over `CKForces` for the two new 4 cases,
using ≤-composed transitivity for the box-form.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean`; `import Cslib.Init` + import
      `CT` (chain `CT ← CS4`). Namespace `Cslib.Logic.Modal`.
- [ ] Define `CS4ModalAxiom` = `CTModalAxiom`'s constructors verbatim + `fourBox (φ) : (□φ).imp (□□φ)`
      + `fourDia (φ) : (◇◇φ).imp (◇φ)` (report D3.1).
- [ ] Prove `cs4_axiom_sound`: inherited cases verbatim (threading `cs4FC r`) + :
      - `fourDia`: from `◇◇A@w'` get `u` with `r w'' u ∧ ◇A@u`, instantiate at `u` (`le_refl`) to
        get `t` with `r u t ∧ A@t`; witness `t` via **plain** transitivity (`u'=u`), report D3.3.
      - `fourBox`: nested-box goal introduces `w''≥w'`, `r w'' u`, `u'≥u`, `r u' t`; supply `A@t`
        from `□A@w'` at `w''` and `t` using **≤-composed transitivity**
        `r w'' u → u ≤ u' → r u' t → r w'' t` (the FC clause absorbs IS4's F2), report D3.3.
- [ ] Prove `cs4_soundness` (structural recursion, copy shape) and `cs4_soundness_derivable`.
- [ ] Docstring all new declarations.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` (create) — `CS4ModalAxiom`,
  `cs4_axiom_sound`, `cs4_soundness`, `cs4_soundness_derivable`.

**Verification**:
- `lake build …Constructive.CS4` green; `fourBox` case uses the ≤-composed clause (verify with
  `lean_goal`); `fourDia` uses the plain specialization.
- Zero errors/warnings/`sorry`; docstrings present.

### Phase 5: CS4 transitivity invariant + completeness [BLOCKED]

**BLOCKER**:
- **What failed**: No per-segment invariant makes `cs4FC cs4Mreach` (≤-composed transitivity of
  the canonical accessibility) hold globally on any world-subtype construction that also admits
  the `diamRefutingSegment` witness the truth lemma's diamond-backward case requires.
- **What was tried**:
  1. Derived (and mechanically verified via a standalone probe file, `lake env lean`, zero
     errors) the general fact `cs4_boxInv_mreach_subset`: for **any** `P U : CKSegment
     CS4ModalAxiom` with `cmreach P U`, `boxInv P.head ⊆ boxInv U.head` (using only `P`'s
     `box_reflect` field plus `fourBox`-closure of `P.head`, no invariant needed).
  2. Identified the natural per-segment invariant that would make ≤-composed transitivity hold:
     `P` is "maximal" — `∀ t, QuasiPrime CS4ModalAxiom t → boxInv P.head ⊆ t → t ∈ P.tail` (`P`'s
     tail contains *every* quasi-prime superset of `boxInv P.head`, i.e. `P` is `.ofHead`-shaped).
     Mechanically verified (`probe_maximal_suffices_for_transitivity`, zero errors) that this
     invariant, combined with (1) and `U.box_reflect`, DOES suffice: `cmreach P U → U ≤ U' →
     cmreach U' T → cmreach P T`.
  3. Mechanically verified (`probe_diamRefuting_not_maximal`, zero errors) that
     `diamRefutingSegment s h_not` — the restricted-tail witness `CKTruthLemma.lean` builds for
     the truth lemma's diamond-backward case (`¬((◇A) ∈ s.head)` from `CKForces (.diamond A)@s`)
     — **cannot** satisfy "maximal": its tail is `{t | QuasiPrime t ∧ boxInv s.head ⊆ t ∧ A ∉ t}`,
     which structurally excludes `t := Set.univ` (quasi-prime, `boxInv s.head ⊆ Set.univ`
     trivially, but `A ∈ Set.univ`) — a counterexample to maximality that exists for *every*
     choice of `s`/`A`.
  4. Explored weaker/alternative invariants (tail-closure under further `boxInv`-successors,
     "hereditary" `A`-exclusion propagated through 4-closure, an intensional
     `boxInv`-inclusion-based accessibility relation mirroring `canonicalR`) — all either (a)
     still fail to admit `diamRefutingSegment`, or (b) make the diamond clause degenerate
     (`Set.univ` is always a valid `boxInv`-superset extension containing any formula, so an
     intensional relation trivially forces every `◇A` everywhere, breaking the discriminating
     power needed for completeness).
- **Why it's stuck**: `cs4FC` (`CKExtension.lean`) is a *blanket* hypothesis
  (`CKValidFC`/`ckvalidFC_completeness` require `FC r` to hold for the *whole* relation on the
  *whole* chosen world type, not per-world). The restricted-tail diamond-refuting witness is
  structurally necessary (an unrestricted/maximal-tail witness always contains `Set.univ` in its
  tail and therefore trivially forces every diamond, which would make the canonical model
  degenerate and break completeness for diamond-containing formulas). But the restricted witness's
  `A`-exclusion is a *one-step* property that does not propagate through further ≤-composed
  transitive successors (nothing prevents a later successor from being, or extending to,
  `Set.univ`, which always contains `A`). These two requirements are in direct tension: whatever
  makes the diamond-refutation witness admissible into the world type breaks the transitivity
  invariant, and whatever restores transitivity breaks diamond-refutation. Resolving this would
  require a substantially more sophisticated ("hereditary"/generated-submodel) diamond-refuting
  construction — new Lindenbaum-style machinery beyond `dia_refuting_theory`/`diamRefutingSegment`
  as provided by task 493 — which is a research-scale extension, not a single-lemma fix.
- **What is needed**: Either (a) a hereditary diamond-refuting theory construction that propagates
  `A`-exclusion through the full ≤-composed-transitive closure of the restricted tail (extending
  `SegmentLindenbaum.lean`'s `dia_refuting_theory` with a stronger invariant baked in from the
  start), or (b) an entirely different canonical-model technique for `S4`-style fallible-world
  segment completeness (e.g. filtration, or a generated/unraveled countermodel) not present in the
  task 493/494 asset base. Flagged as a follow-up research item.
- **Prohibited workarounds**: No `sorry`, no `def X := True`/vacuous placeholder, no new axiom —
  none introduced. `CS4.lean` contains only `CS4ModalAxiom`/`cs4_axiom_sound`/`cs4_soundness`/
  `cs4_soundness_derivable` (Phase 4, complete and committed); no `CS4Segment`/completeness
  declarations were added.

**Goal**: Build the CS4 canonical model over a subtype carrying the ≤-composed transitivity
invariant, handle the restricted-tail closure, and prove completeness/consistency/biconditional.

**Tasks**:
- [ ] Define the CS4 world subtype in `CS4.lean` carrying the ≤-composed transitivity of the
      canonical `cmreach` as its invariant (report D3.4): the `ofHead` maximal tail
      `{t | QuasiPrime t ∧ boxInv H ⊆ t}` is transitively closed because `fourBox`/`fourDia` give
      `□B ∈ H ⇒ □□B ∈ H`, so `boxInv (boxInv H) ⊆ boxInv H` (mirrors `is4_canonical_transitive`'s
      `hwu.1 ∘ hwv.1`). Reuse the CT `Preorder.lift`/projection pattern.
- [ ] Discharge the invariant for `ofHead`, `cexpl`, and — the MED risk (report Risk 2) — the
      `diamRefutingSegment` restricted (witness-omitting) tail: show it is transitively compatible;
      if it is not, introduce a frame-condition-aware refuting segment for the truth-lemma
      diamond-backward case and thread it through.
- [ ] Prove `cs4FC cs4Mreach` (reflexivity from the CT-style `refl` field + the transitivity
      invariant); prove `cs4_completeness` via `ckvalidFC_completeness cs4FC (dischargers…)`;
      prove `cs4_consistent` (one-point reflexive+transitive frame) and `cs4_soundness_completeness`.
- [ ] Docstring all new declarations.

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` (extend) — CS4 world subtype + `Preorder`
  instance, transitivity-invariant discharge (incl. restricted-tail closure), `cs4_completeness`,
  `cs4_consistent`, `cs4_soundness_completeness`.

**Verification**:
- `lake build …Constructive.CS4` green; `cs4_soundness_completeness` is a biconditional.
- Zero errors/warnings/`sorry`; docstrings present. If a frame-condition-aware refuting segment was
  needed, note it in the phase status line for reuse in Phase 7.

### Phase 6: CS5 axioms + soundness [COMPLETED]

**Goal**: Define `CS5ModalAxiom` via **B (symmetry)** and prove soundness over `CKForces` for the
two new B cases, using ≤-composed symmetry for the box-form.

**Tasks**:
- [ ] Create `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean`; `import Cslib.Init` + import
      `CS4` (chain `CS4 ← CS5`). Namespace `Cslib.Logic.Modal`.
- [ ] Define `CS5ModalAxiom` = `CS4ModalAxiom`'s constructors verbatim + `bBox (φ) : φ.imp (□◇φ)`
      + `bDia (φ) : (◇□φ).imp φ` (B, NOT euclidean-5; report D3.1 + Risk 5).
- [ ] Prove `cs5_axiom_sound`: inherited cases verbatim (threading `cs5FC r`) + :
      - `bDia`: at `w'` (`le_refl`) get `u` with `r w' u ∧ □A@u`; instantiate `□A@u` at `u`
        (`le_refl`) and `w'` via **plain** symmetry `r w' u → r u w'`; yields `A@w'`, report D3.3.
      - `bBox`: goal `∀ w''≥w', ∀ u, r w'' u → ◇A@u`; unfold `◇A@u` at `u'≥u`; witness `w''` via
        **≤-composed symmetry** `r w'' u → u ≤ u' → r u' w''`, with `A@w''` by persistence from
        `w' ≤ w''`, report D3.3.
- [ ] Prove `cs5_soundness` (structural recursion) and `cs5_soundness_derivable`.
- [ ] Docstring all new declarations.

**Timing**: 1.5 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (create) — `CS5ModalAxiom`,
  `cs5_axiom_sound`, `cs5_soundness`, `cs5_soundness_derivable`.

**Verification**:
- `lake build …Constructive.CS5` green; `bBox` uses ≤-composed symmetry, `bDia` plain symmetry.
- Zero errors/warnings/`sorry`; docstrings present.

### Phase 7: CS5 symmetry invariant + completeness (HIGHEST RISK — STOP/[BLOCKED] contingency) [BLOCKED]

**BLOCKER**:
- **What failed**: Same underlying obstruction as Phase 5 (CS4 transitivity), now confirmed to
  also block CS5's ≤-composed symmetry clause — not separately re-attempted with fresh
  construction effort once Phase 5 confirmed the shared root cause (see Phase 5's Blocker entry
  for the full mechanically-verified analysis).
- **What was tried**: Phase 5's analysis generalizes directly: `cs5FC` requires `∀ w, r w w` (holds,
  same as `ctFC`/reflexivity — this part is not the issue) **and** the ≤-composed transitivity
  clause (Phase 5's blocker) **and** the ≤-composed symmetry clause `r w u → u ≤ u' → r u' w`.
  Any world-subtype invariant strong enough to make transitivity hold globally (i.e. "maximal"
  tails) structurally excludes `diamRefutingSegment`-shaped worlds (Phase 5, mechanically
  verified); since `cs5FC` is a strict conjunction that *includes* the transitivity clause, `cs5FC`
  inherits the exact same non-satisfiability by any world type admitting the required
  diamond-refuting witness. The symmetry clause specifically would face an analogous "one-step
  exclusion vs. relational closure" tension: `is5_canonical_symmetric`'s positive
  `bDia`/`bBox`-routed argument (`IS5.lean:341`) relies on `canonicalR` being *intensional*
  (defined directly by box/dia membership conditions over the *whole* `CanonicalPrimeWorld` type,
  no subtype), which is unavailable here because `cmreach` is *extensional* (tail membership) and
  an intensional substitute was shown (Phase 5, point 4) to make the diamond clause degenerate.
- **Why it's stuck**: `cs5FC` is strictly stronger than `cs4FC` (same transitivity conjunct plus
  symmetry), so it cannot be satisfied by any world type that already fails to satisfy `cs4FC`
  (Phase 5). Fixing Phase 5's blocker (a hereditary diamond-refuting construction or a different
  canonical-model technique) is a precondition for even attempting Phase 7's symmetry-specific
  closure.
- **What is needed**: Resolution of Phase 5's blocker first (a hereditary diamond-refuting theory
  construction, or a different completeness technique for `S4`-style fallible-world segment
  models); Phase 7's symmetry closure would then need its own additional positive argument
  (routing box membership through the diamond clause via `bDia`/`bBox`, per
  `is5_canonical_symmetric`'s pattern) built on top of that resolution.
- **Prohibited workarounds**: No `sorry`, no `def X := True`/vacuous placeholder, no new axiom —
  none introduced. `CS5.lean` contains only `CS5ModalAxiom`/`cs5_axiom_sound`/`cs5_soundness`/
  `cs5_soundness_derivable` (Phase 6, complete and committed); no `CS5Segment`/completeness
  declarations were added.

**Goal**: Build the CS5 canonical model over a subtype carrying the ≤-composed symmetry invariant
(plus reflexivity + transitivity) and prove completeness/consistency/biconditional — OR mark
[BLOCKED] with the exact goal state if the symmetry closure does not go through positively.

**Tasks**:
- [ ] Define the CS5 world subtype in `CS5.lean` carrying reflexivity + ≤-composed transitivity +
      ≤-composed symmetry of the canonical `cmreach` (report D3.4). Reuse the CT/CS4 subtype pattern.
- [ ] Prove the symmetry invariant positively (report Risk 1, HIGH), mirroring
      `is5_canonical_symmetric` (`IS5.lean:341`): route a box membership back through the diamond
      clause via `bDia`, and a value forward through `bBox` — both MP-only, no `by_contra`, no
      negation. Adapt from `canonicalR`'s two clauses to `cmreach = tail membership`.
- [ ] Handle the restricted-tail symmetry compatibility for `diamRefutingSegment` (report Risk 2);
      reuse any frame-condition-aware refuting segment introduced in Phase 5.
- [ ] Prove `cs5FC cs5Mreach`; prove `cs5_completeness` via `ckvalidFC_completeness cs5FC
      (dischargers…)`; prove `cs5_consistent` (one-point equivalence frame) and
      `cs5_soundness_completeness`.
- [ ] **STOP/[BLOCKED] contingency**: if the ≤-composed symmetry clause cannot be discharged
      positively over the restricted tail after focused effort, DO NOT introduce a `sorry` or an
      axiom. Set this phase's status to `[BLOCKED]`, record the exact unmet goal state (from
      `lean_goal`) and the specific tail-membership obstruction in the phase's Blocked line, and
      hand off. Phases 1-6 (CKExtension + CT + CS4 complete; CS5 axioms/soundness complete) remain
      green and committable; only CS5 completeness is deferred.
- [ ] Docstring all new declarations.

**Timing**: 2.5 hours

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (extend) — CS5 world subtype + `Preorder`
  instance, symmetry-invariant discharge (+ transitivity/reflexivity), `cs5_completeness`,
  `cs5_consistent`, `cs5_soundness_completeness`.

**Verification**:
- SUCCESS: `lake build …Constructive.CS5` green; `cs5_soundness_completeness` is a biconditional;
  zero errors/warnings/`sorry`; docstrings present.
- BLOCKED: file compiles for everything except the deferred CS5 completeness; the exact goal state
  is recorded; no `sorry`/axiom introduced (if compilation requires it, leave the completeness
  declarations out and mark the phase [BLOCKED] rather than committing a `sorry`).

### Phase 8: Barrel wiring + full CI [NOT STARTED]

**Goal**: Wire the new files into `Cslib.lean` and run the full CI pipeline to green.

**Tasks**:
- [ ] Regenerate the barrel: `lake exe mk_all --module` (or add the four imports to `Cslib.lean`
      after `Cslib.lean:353–357` where the task 493 `Constructive/` modules are wired). Confirm
      `CKExtension`, `CT`, `CS4`, `CS5` all appear.
- [ ] Run the full CSLib CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe
      lint-style`, `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.
- [ ] Resolve any `shake` import-minimization findings and any `lint-style`/`checkInitImports`
      issues across the four new files.
- [ ] If Phase 7 is [BLOCKED]: wire and CI-check Phases 1-6 deliverables (CKExtension + CT + CS4
      full; CS5 axioms/soundness), leave CS5 completeness out of the barrel-facing surface as
      appropriate, and record CS5 completeness as the single open item in the summary.
- [ ] Confirm zero `sorry` and zero new axioms across all four files (spot-check with
      `lean_verify` on the top-level theorems).

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 4, 5, 6, 7

**Files to modify**:
- `Cslib.lean` (extend) — add the four `Constructive/` module imports (or via `mk_all`).

**Verification**:
- Full pipeline green: `lake build` && `lake exe checkInitImports` && `lake exe lint-style` &&
  `lake shake --add-public --keep-implied --keep-prefix` && `lake test`.
- Zero `sorry`, zero new axioms, zero warnings.

## Testing & Validation

- [ ] `lake build` (whole library) succeeds with zero errors and zero warnings.
- [ ] `lake exe checkInitImports` passes for all four new files.
- [ ] `lake exe lint-style` passes (style + docstring/docBlame).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no import-minimization issues.
- [ ] `lake test` (CslibTests) passes.
- [ ] Each system's `x_soundness_completeness` type-checks as a biconditional (soundness ∧
      completeness), except CS5 if Phase 7 is [BLOCKED].
- [ ] No `sorry`, no new `axiom`, no use of deprecated Mathlib `Reflexive`/`Transitive`/`Symmetric`.
- [ ] Every new declaration has a docstring; declaration names follow the existing `ck_`/`it_`
      convention.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — scaffold (`CKValidFC`,
  `ctFC`/`cs4FC`/`cs5FC`, `ckvalidFC_completeness`, `axiom_mem_head`).
- `Cslib/Logics/Modal/Metalogic/Constructive/CT.lean` — CT axioms, soundness, world-subtype
  completeness.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` — CS4 axioms, soundness, completeness.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — CS5 axioms (B), soundness, completeness
  (or [BLOCKED] CS5 completeness with recorded goal state).
- `Cslib.lean` — barrel imports for the four new modules.
- `specs/501_CK_constructive_modal_extensions_CT_CS4_CS5/summaries/01_ct-cs4-cs5-extensions-summary.md`
  — execution summary (produced by /implement).

## Rollback/Contingency

- The four new files are additive; task 493's `Constructive/` core and task 494's
  `Intuitionistic/` files are untouched. To revert, remove the four new files and their `Cslib.lean`
  barrel imports (`git checkout Cslib.lean` + `git rm` the new files) — no existing declaration
  changes to unwind.
- Commit at every green milestone (per phase) so a failed later phase never forces re-doing earlier
  green work. Each of CKExtension, CT (soundness), CT (completeness), CS4, CS5 (soundness) is an
  independent green commit point.
- If Phase 7 CS5 completeness is [BLOCKED]: land Phases 1-6 + 8 (CKExtension + CT + CS4 fully
  complete, CS5 axioms/soundness complete), mark the task [PARTIAL] or [BLOCKED] with the recorded
  goal state, and spawn a focused follow-up for the CS5 symmetry-invariant closure. Do NOT paper
  over the gap with a `sorry` or axiom.
