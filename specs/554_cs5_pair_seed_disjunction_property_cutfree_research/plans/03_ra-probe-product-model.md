# Implementation Plan: Task #554 (Round 3, hard mode)

- **Task**: 554 - CS5 pair-seed obligation: (R-a) probe and conditional product-model route
- **Status**: [IMPLEMENTING]
- **Effort**: 13.5 hours worst case (probe-kill path: ~4 hours — Phases 1-2 only)
- **Dependencies**: None
- **Research Inputs**:
  - `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md`
    (adversarially verified: 22 claims VERIFIED, 1 REFUTED — constructor names, 1 UNCERTAIN — §5.2)
  - `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/handoffs/phase-14-handoff-20260726.md`
    (prior-route blocker record, reference only)
- **Artifacts**: plans/03_ra-probe-product-model.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md, plan-compliance.md, no-task-references-in-deliverables.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The task was **rescoped by explicit user decision (2026-07-26)**, adopting report 02 §8: the
§8.1 land-now items plus the single §8.2 probe are the entire remaining scope. "NOTHING ELSE IS
IN SCOPE." The nested-sequent formalisation (plan 02 Stages B–G) is **explicitly not adopted —
do not re-propose** (user's words), which supersedes plan 02's route recommendation. This plan
therefore does exactly two things:

1. **Phase 1-2 (unconditional)**: run the (R-a) probe — *can a total-`r` `is5FC` model refute an
   `IS5` non-theorem?* — with an explicit kill-criterion, and land its verdict as
   machine-checked repository theorems either way.
2. **Phases 3-6 (conditional on (R-a) surviving)**: build report 02 §5.2's product model over
   `IS5` and discharge the exclusion theorem up to the (R-b) interface, then STOP — (R-b) is
   machine-checked-equivalent to the `CS5 = IS5` collapse
   (`CS5ToIS5.lean:103 is5_derivable_of_boxNotMem_transport`), whose adoption requires explicit
   user authorisation.

**Kill-criterion (verbatim from the rescoped task description)**: "If R-a fails, the route is
dead and this task closes [BLOCKED] with the section 5.4 cost table as justification — a
negative result is a valid deliverable."

### Current-State Verification (performed at plan time, not assumed from the report)

Report 02's authoring-time line numbers have drifted; all §8.1 land-now items are confirmed
landed at HEAD:

| Report item | Current location | Verified |
|---|---|---|
| `CS5PairSeedRightExclusion` (corrected obligation) | `CS5Completeness.lean:507` | 2026-07-28 |
| `cs5PairSeedDisjunctionProperty_false` (regression refutation) | `CS5Completeness.lean:543` | 2026-07-28 |
| `cs5PairSeedDisjunctionProperty_false_of_boxMem` | `CS5Completeness.lean:574` | 2026-07-28 |
| `cs5Axiom_to_is5Axiom` / `cs5_deriv_to_is5` / `cs5_closure_subset_is5_closure` | `InterSystem/CS5ToIS5.lean:60/81/90` | 2026-07-28 |
| Route-closure `is5_derivable_of_boxNotMem_transport` (+ `_iff_`) | `CS5ToIS5.lean:103/128` | 2026-07-28 |
| `is5FC` / `is5_axiom_sound` / `is5_soundness_derivable` / `is5_completeness` / `is5_consistent` | `Intuitionistic/IS5.lean:155/172/~292/363/377` | 2026-07-28 |
| `IS5ModalAxiom`-only constructors are `cd`/`idb`/`dbot` (NOT `kdisj`/`kfs`/`kbot`) | `IS5.lean:119/122/125` | per report's own adversarial correction |

`Cslib/Logics/Modal/Metalogic/Constructive/Nested/` (5 modules, plan 02 phases 6-13) is landed,
sorry-free (repo grep confirms zero `sorry` tokens outside prose comments), and builds green. It
is a preserved asset, not a work area.

### Preserved Assets

The following work is complete and must not regress:

| Component | File | Status | Verified |
|-----------|------|--------|----------|
| Corrected obligation + refutation regressions (plan 02 Ph. 1-2) | `Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean` | [COMPLETED] | 2026-07-28 |
| Caller-side bridge + retraction/docstrings (plan 02 Ph. 3-4) | `CS5Completeness.lean` | [COMPLETED] | 2026-07-28 |
| `CS5 → IS5` transport + R-b route-closure (plan 02 Ph. 5) | `Cslib/Logics/Modal/Metalogic/InterSystem/CS5ToIS5.lean` | [COMPLETED] | 2026-07-28 |
| Nested-sequent syntax/contexts/translation/rules/soundness (plan 02 Ph. 6-13) | `Cslib/.../Constructive/Nested/{Syntax,Context,Translation,Rules,Soundness}.lean` | [COMPLETED] | 2026-07-28 |
| Round-1/2 probes | `specs/554_.../probes/*.lean` | [COMPLETED] | 2026-07-28 |

No phase of this plan edits any `Nested/` file. The phase-14 goal (nested derivations of the 17
axioms) is **abandoned per the user rescope**, not resumed — its blocker record stays in the
handoff file as documentation.

### Source-to-Implementation Mapping (H3, Tier 1 literature + Tier 3 code)

| Plan element | Source | Tier |
|---|---|---|
| (R-a) statement and its gating role | report 02 §5.3, §8.2 | report (verified) |
| Product construction (frame, projection, cross-axiom forcing) | report 02 §5.2 — **UNCERTAIN per adversarial verification; gated behind Phase 1** | report |
| `is5FC` box/dia forcing clauses used by the probe | `IS5.lean` `is5_axiom_sound` cases (box: `∀ w' ≥ w, ∀ u, r w' u → …`; dia: `∃ u, r w u ∧ …`) | code |
| ≤-mediated frame-condition delicacy (why (R-a) is credible either way) | [MarinMoralesStrassburger2021] §7-8; `cs5Incest_*_false` precedent (`CS5Canonical.lean:447+`) | literature/code |
| (R-b) ⟹ collapse; collapse's published basis unsound | `CS5ToIS5.lean:103`; [Pacheco2024] Lemma 16/18 critique, report §6 | code/literature |
| Cost table justifying [BLOCKED] on kill | report 02 §5.4 | report |

**BibKey hygiene (binding)**: any new prose citation in `Cslib/` docstrings uses the verified
`references.bib` keys `Pacheco2024`, `ArisakaDasStrassburger2015`,
`MarinMoralesStrassburger2021` — never the report's shorthand tags `[Pacheco24]`/`[ADS15]`/
`[MMS21]`.

### The Probe, Made Concrete (plan-time sharpening)

Report 02 leaves (R-a) as an open question. Plan-time analysis of CSLib's actual forcing
clauses yields a **concrete decision procedure** the probe must attempt first:

With total `r`, the box clause `w ⊩ □φ ↔ ∀ w' ≥ w, ∀ u, r w' u → u ⊩ φ` degenerates to
`∀ u ∈ W, u ⊩ φ` — world-independent. Meta-level classical case-split (Lean's `Classical.em`)
then makes `□a ∨ ¬□a` **forced at every world of every total-`r` model**: if `∀u, u ⊩ a` the
left disjunct holds; otherwise no world forces `□a`, so `¬□a` (`= □a → ⊥`) holds vacuously at
every ≤-successor. But `□a ∨ ¬□a` is **not** `IS5`-derivable: the two-world chain `w₀ ≤ w₁`,
`r := Eq`, `a` true at `w₁` only, is an `is5FC` model (identity is an equivalence; `f1`/`f2`
hold with witnesses `w'`/`u'`) refuting both disjuncts at `w₀`, and `is5_soundness_derivable`
converts that countermodel into underivability.

Since the product-model route needs, for **arbitrary** `(H, A)` with `A ∉ cl_IS5`-side
conditions, a total model with `u ⊩ H` and `v ⊮ A` (report §5.2: "with `u ⊩ H` and `v ⊮ A` and
`r u v`"), the instance `H := ∅`, `A := □a ∨ ¬□a` would refute the route outright. **This is a
scope hypothesis, not a fact** — the two displayed arguments must be machine-checked in Phase 1
before any conclusion is drawn. If they check, the kill-criterion fires and the task closes per
the user's own instruction. If the total-validity lemma fails against the real semantics, the
probe falls back to the positive direction with a fixed budget (see Phase 1).

### Prior Plan Reference

Plan 02 (`plans/02_cutfree-pair-conservativity.md`) remains the record of phases 1-13
([COMPLETED]) and the phase-14 blocker. Its Stages E-G ([NOT STARTED]/[BLOCKED]) are superseded
by the user rescope and will not be executed. This plan does not renumber or rewrite plan 02.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context; no roadmap phases are included.

## Postmortem Constraints

Binding rules for all implementation dispatches. Derived from the user rescope, the phase-14
handoff, plan 02's machine-checked route closures, and the report's adversarial verification.

**Do NOT**:
- Do not re-open the nested-sequent or labelled-calculus formalisation, and do not edit any file
  under `Cslib/.../Constructive/Nested/`. The user rescope says "do not re-propose"; the
  phase-14 wall (InputCtx-shaped rules produce unconditionally `.box`-shaped RHS, machine-
  verified) is documented in the handoff and is not this plan's problem.
- Do not pursue, prove, or assume (R-b) (`H` `CS5`-closed, `□A ∉ H ⟹ □A ∉ cl_IS5(H)`) — it is
  machine-checked to imply the `CS5 = IS5` collapse (`is5_derivable_of_boxNotMem_transport`),
  which requires explicit user authorisation and whose only published basis ([Pacheco2024]
  Lemmas 16/18) is unsound. Reaching the (R-b) interface and stopping IS the Phase 6 endpoint.
- Do not attempt `□(A ∨ B) → (□A ∨ □B)` or any route needing it — invalid even in classical
  `S5` (report §4, VERIFIED).
- Do not attempt to prove the unconditioned `CS5PairSeedDisjunctionProperty` — machine-refuted;
  regression theorems at `CS5Completeness.lean:543/574` must not be weakened or removed.
- Do not restrict the product carrier to `{(u,v) | r u v}` — that set is not `≤'`-closed under
  `f2` (report §5.3, VERIFIED against `IS5.lean:266`). Totality of the base `r` is the only
  admissible fix, which is exactly why Phase 1 gates everything.
- Do not write `kdisj`/`kfs`/`kbot` in any Lean code — the `IS5ModalAxiom`-only constructors
  are `cd`/`idb`/`dbot` (`IS5.lean:119/122/125`; the report's one REFUTED claim).
- Do not run unbounded proof attempts: Phase 1 has a fixed attempt list and stopping condition;
  every other phase's target is a fixed, named lemma set.
- Do not cite task numbers in `Cslib/` docstrings (durable anchors only, per
  no-task-references-in-deliverables.md); do not cite report shorthand BibTags (see BibKey
  hygiene above).
- Do not create a PR or push (pr-prohibition.md).

**MUST preserve**:
- Every row of the Preserved Assets table, byte-for-byte where not explicitly extended by a
  phase below (docstring cross-references in `CS5Completeness.lean` are the only sanctioned
  touch to a preserved file, in Phase 2).
- Repo-wide bare-`sorry` count in `Cslib/`: currently 5 (`TemporalConservativity.lean:269`,
  `Tableau/Minimal/Completeness.lean:125`, `Tableau/Intuitionistic/Completeness.lean:133`,
  `Tableau/Intuitionistic/Scheme.lean:592`, `:1498`). No phase may add a `sorry`; no strategic
  sorries are planned in this plan.

**Design decisions are SETTLED** (do not re-open without concrete counterexample):
- The corrected obligation is `CS5PairSeedRightExclusion` with hypothesis
  `A ∉ cl_CS5(boxInv H)` — landed; hypothesis (ii) `□A ∉ H` alone is insufficient (report §1.1,
  VERIFIED).
- The task's remaining scope is the (R-a) probe and, conditionally, the product-model
  construction — settled by explicit user rescope. A fired kill-criterion closes the task
  [BLOCKED] with the §5.4 cost table; that outcome is a deliverable, not a failure.
- (R-b) is the collapse; escalation to the user is the only continuation past Phase 6.

## Goals & Non-Goals

**Goals**:
- Decide (R-a) by machine-checked probe, with the kill-criterion executable as stated by the
  user.
- Land the probe verdict as sorry-free, library-grade theorems in
  `Cslib/Logics/Modal/Metalogic/Intuitionistic/` either way (negative: total-model validity of
  `□a ∨ ¬□a` + underivability + route-refutation corollary; positive: the total-model
  construction lemma that survived).
- If (R-a) survives: formalise the §5.2 product model (product frame, projection lemma,
  `CS5PairAxiom` validity, seed forcing) and the exclusion theorem
  `cs5Pair_rightExclusion_of_totalCountermodel`, reducing the named obligation to the (R-b)
  interface, then stop and report both consumers' status.

**Non-Goals**:
- No `sorry`, no `axiom`, no vacuous definition, no weakened or restated landed theorem.
- No nested-sequent work of any kind (user rescope).
- No (R-b) proof, no collapse route, no `idb`-derivation attempt (mandate + machine-checked
  closure).
- No modification of `Labelled/Soundness.lean` or the `sigAt` fold (second consumer's answer is
  already settled by report §7: "never", classical countermodel).
- No PR creation or push.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Plan-time sharpening of the probe is wrong (total-validity lemma fails against real `BForces` semantics) | M | L | Phase 1 attempt list has an explicit fallback: re-derive the box clause from `BForces`'s definition, re-evaluate, and if total models CAN refute `□a ∨ ¬□a`, switch to the positive-direction attempt with a 2-strategy budget; stopping condition is explicit either way |
| Universe/encoding friction formalising "∃ total model" for the route-refutation corollary | M | M | Mirror `IValidFC`'s existing quantification pattern (`intro World _ r …`); state the corollary against an explicit `∃ (World : Type) (_ : Preorder World) …` telescope; if the telescope fights the elaborator, land P1+P2 (which carry the mathematical content) and state the corollary against a named `structure` bundling the model data |
| Projection lemma's `→`/`□`/`◇` cases need other-coordinate witnesses the frame can't supply | H | M | This is precisely the §5.2 UNCERTAIN claim; Phase 1's surviving branch guarantees totality of `r`, which supplies every witness the report's design names; if a case still fails, the failing goal state is itself a (R-a)-adjacent negative result — record it and fire the kill-criterion disposition |
| Phase estimates overrun a dispatch | M | M | Phases are H8-bounded (each one lemma-cluster, ≤ ~300 lines); each ends at a green committable checkpoint; kill path ends the task after Phase 2 |
| Docstring edits reintroduce task numbers or wrong BibKeys | L | M | Postmortem constraint + Phase 2/6 verification includes the lint gate and a grep for `kdisj\|kfs\|kbot\|\[ADS15\]\|\[MMS21\]\|\[Pacheco24\]` |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | Phase 1 | -- |
| 2 | Phase 2 | 1 |
| 3 | Phase 3 (conditional) | 1 (verdict: survive), 2 |
| 4 | Phase 4 (conditional) | 3 |
| 5 | Phase 5 (conditional) | 4 |
| 6 | Phase 6 (conditional) | 5 |

No parallel opportunities: the plan is a single decision spine; Phase 2 consumes Phase 1's
verdict, and Phases 3-6 exist only on the survive branch. If Phase 1's kill-criterion fires,
Phases 3-6 are NOT executed and are marked `[BLOCKED]` with a one-line pointer to the Phase 1
verdict; the task closes per the disposition in Phase 2.

---

### Phase 1: The (R-a) probe — total-model refutation capacity of `is5FC` [COMPLETED]

**Goal**: Decide, machine-checked, whether the product-model route's required form of (R-a)
holds: *for arbitrary `(H, A)` with the route's side conditions, does a total-`r` `is5FC` model
with `u ⊩ H` and `v ⊮ A` exist?*

**Verification Tier**: local (probe file lives under `specs/`, outside the `Cslib` barrel)

**Scope Hypothesis**: ~150-250 lines in one probe file; the separating-formula argument (P1/P2
below) is a plan-time hypothesis requiring machine confirmation — the phase's whole point is to
confirm or refute it.

**Tasks** (fixed attempt list, in order):
- [x] Write `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/probes/ra_total_probe.lean`.
- [x] **P1 (total-validity)**: `∀ {World} [Preorder World] (r) (total : ∀ u v, r u v) (val)`
      (val ≤-monotone not required for this lemma) `(w)`, `BForces r val (fun _ => False) w
      ((Proposition.box (.atom a)).or ((Proposition.box (.atom a)).imp .bot))` — by
      `Classical.em (∀ u, BForces … u (.atom a))`-style case split, using the degenerate box
      clause under totality. Atom type generic with one distinguished `a : Atom`.
- [x] **P2 (underivability)**: `¬ Derivable IS5ModalAxiom ((□ a).or ((□ a).imp ⊥))` via
      `is5_soundness_derivable` and the two-world chain countermodel (`World` := a two-element
      order `w₀ ≤ w₁`; `r := Eq` — equivalence trivially; `f1`/`f2` discharged with witnesses
      `w'`/`u'`; `val` := true at `w₁` only, monotone). State over a concrete or `Nonempty`
      atom type as convenient.
- [x] **P3 (route refutation)**: formalise the route-required statement (∃-telescope over
      `World`, `Preorder`, total `r`, monotone `val`, worlds `u v` with `∀ φ ∈ H, u ⊩ φ` and
      `¬ v ⊩ A`, existence for every `(H, A)` with `A ∉ modalDeductiveClosure IS5ModalAxiom H`)
      and refute it at `H := ∅`, `A := □a ∨ ¬□a`, combining P1 (no total model refutes `A`
      anywhere) and P2 (`A ∉ cl_IS5(∅)`, bridging `modalDeductiveClosure` at `∅` to
      `Derivable` via `PrimeTheory.lean:76-88`'s definition with witness list `[]`).
- [ ] ~~**Fallback (only if P1's proof does not close)**~~ — NOT TRIGGERED: P1 closed on the
      first attempt against the real `BForces` semantics (`Birelational.lean:118` box clause
      degenerates under totality exactly as the plan-time sharpening predicted).

**Phase 1 verdict (recorded 2026-07-28)**: stopping condition (a) — P1+P2+P3 sorry-free,
**kill-criterion FIRED, (R-a) REFUTED**. `lake env lean` exit 0; `#print axioms`:
`total_validates_boxEm`/`ra_route_refuted` use only `propext, Classical.choice, Quot.sound`;
`boxEm_not_derivable` is axiom-free (fully constructive). Verdict sentence at top of probe
file. Per the dependency table, Phases 3-6 are not executable ((R-a) refuted); Phase 2's kill
branch (land verdict in `Cslib`, execute the user's [BLOCKED] disposition) is next.

**Stopping condition (bounded-unit guarantee)**: the phase ends when exactly one of
(a) P1+P2+P3 are sorry-free — **kill-criterion FIRED**; (b) a machine-checked counterexample to
P1's statement is produced and the fallback's positive construction lands — **(R-a) survives**;
(c) both P1 and its fallback fail within budget — phase marked `[BLOCKED]` with recorded goal
states and `requires_user_review`. No further attempts past (c) in this dispatch.

**Estimated output**: ~200 lines. **Timing**: 2.5 hours.

**Done when**: the probe file compiles clean under the repo toolchain (`lake env lean` on the
file), contains zero `sorry`, and its header states the verdict in one sentence.

**Verification**:
- `lake env lean specs/554_cs5_pair_seed_disjunction_property_cutfree_research/probes/ra_total_probe.lean` exits 0
- `#print axioms` on P1-P3 (or the fallback lemmas): no `sorryAx`
- Verdict sentence present at top of file

---

### Phase 2: Land the probe verdict in `Cslib` and execute the disposition [COMPLETED]

**Goal**: Promote Phase 1's mathematical content to a library-grade module and put the task in
the state the user's kill-criterion prescribes.

**Verification Tier**: full

**Scope Hypothesis**: one new file ~120-200 lines plus one docstring cross-reference edit;
exact lemma set depends on Phase 1's verdict.

**Tasks (kill branch — expected)**:
- [x] New file `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5TotalModels.lean`: P1 as a
      general totality lemma, P2, and the route-refutation corollary (P3), renamed to
      library-grade names; module docstring explaining that total-`r` birelational models
      collapse `□` to a world-independent global modality, hence validate `□a ∨ ¬□a`, hence
      cannot refute `IS5` non-theorems — citing [MarinMoralesStrassburger2021] §7-8 for the
      `≤`/frame-condition delicacy and using durable anchors (file/section names), never task
      numbers.
- [x] Docstring cross-reference in `CS5Completeness.lean` adjacent to
      `CS5PairSeedRightExclusion` (`:507` region): both residuals of the product-model route
      are now machine-closed — (R-b) ⟹ collapse (`is5_derivable_of_boxNotMem_transport`) and
      (R-a) refuted (`IS5TotalModels.lean`). No other edit to the preserved file.
- [x] Barrel registration: `lake exe mk_all --module`; scoped `lake build` of the new module
      and `CS5Completeness`. (mk_all also surfaced the unregistered `Tableau/Blocking.lean`
      owned by a concurrent task; that line was dropped from this commit — out of territory.)
- [x] Disposition: report task closure per rescope — `[BLOCKED]`, justification = report 02
      §5.4 cost table + the two machine-checked route closures, `requires_user_review: true`,
      and the two consumers' answers restated (pair-Lindenbaum consumer: obligation not
      dischargeable by any surveyed route without user-authorised collapse; labelled-soundness
      consumer: fold unrepairable, answer "never", unchanged).

**Tasks (survive branch)**:
- [ ] Same new file, containing instead the positive total-model construction lemma(s) that
      Phase 1's fallback produced, docstringed as the (R-a) discharge; proceed to Phase 3.

**Estimated output**: ~180 lines. **Timing**: 1.5 hours.

**Done when**: new module builds green in the barrel, verdict theorems `lean_verify` sorry-free,
and the disposition (kill: closure report; survive: green light for Phase 3) is recorded in the
dispatch return.

**Verification**:
- Scoped `lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5TotalModels` green;
  `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Completeness` green
- `lake exe checkInitImports` passes; `lake exe lint-style` clean; shake/`mk_all` consistency
  clean on the new file
- `grep -rn "kdisj\|kfs\|kbot\|\[ADS15\]\|\[MMS21\]\|\[Pacheco24\]" Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5TotalModels.lean` empty
- Repo-wide bare-`sorry` count in `Cslib/` still exactly 5

---

### Phase 3: Product frame on `W × W` with componentwise conditions [BLOCKED]: (R-a) refuted, see Phase 1

**Conditional**: execute only if Phase 1 ended in verdict (b) — (R-a) survives. If the
kill-criterion fired, mark this and all later phases `[BLOCKED]: (R-a) refuted, see Phase 1`.

**Goal**: The §5.2 product model as definitions plus frame lemmas: order product `≤'`,
componentwise `r'`, `val' := Sum.elim`-split valuation over `Atom ⊕ Atom`.

**Verification Tier**: full

**Scope Hypothesis**: ~150-250 lines; new file
`Cslib/Logics/Modal/Metalogic/Constructive/CS5ProductModel.lean` (placement keeps the
`Intuitionistic → Constructive` import direction clean; confirm against barrel conventions).

**Tasks**:
- [ ] Define the product order/relation/valuation on `W × W` per report §5.2 (componentwise).
- [ ] Prove: `r'` total (from base totality — the survive-branch supply), `is5FC` conditions
      componentwise, `f1`/`f2` componentwise, `val'` ≤'-monotone.

**Estimated output**: ~200 lines. **Timing**: 2 hours.

**Done when**: all frame lemmas sorry-free; scoped build green.

**Verification**: scoped `lake build` green; `lean_verify` on each frame lemma; barrel/mk_all,
checkInitImports, lint-style clean.

---

### Phase 4: The projection lemma [BLOCKED]: (R-a) refuted, see Phase 1

**Conditional**: as Phase 3.

**Goal**: `M', (u,v) ⊩ cs5PairTauL φ ↔ M, u ⊩ φ` and `M', (u,v) ⊩ cs5PairTauR φ ↔ M, v ⊩ φ`,
by induction on `Proposition Atom`; the `→`/`□`/`◇` cases take other-coordinate witnesses from
reflexivity of `≤` and totality of `r` (this is the report's UNCERTAIN §5.2 core — if a case
fails structurally, record the goal state and fall back to the Phase 2 kill disposition with
the failing case as the negative result).

**Verification Tier**: full

**Scope Hypothesis**: ~150-300 lines, one theorem pair (single induction).

**Estimated output**: ~250 lines. **Timing**: 3 hours.

**Done when**: both directions sorry-free for both translations; scoped build green.

**Verification**: as Phase 3.

---

### Phase 5: `CS5PairAxiom` validity and seed forcing on the product [BLOCKED]: (R-a) refuted, see Phase 1

**Conditional**: as Phase 3.

**Goal**: Every `CS5PairAxiom` instance (`CS5Completeness.lean:90-150`) valid at every world of
`M'`: `.left`/`.right` via `is5_axiom_sound ∘ cs5Axiom_to_is5Axiom` + projection; propositional
core over the whole `Proposition (Atom ⊕ Atom)` type (ordinary birelational tautology
soundness); `cross1`/`cross2` via totality of `r`. Then seed forcing: with `u ⊩ H`, `v ⊮ A`,
`r u v`, the seed `cs5PairSeed H` is forced at `(u,v)` (right component via
`B ∈ boxInv H ⇒ u ⊩ □B ⇒ v ⊩ B`; `K`-closure via `is5_soundness`).

**Verification Tier**: full

**Scope Hypothesis**: ~200-300 lines, two lemma clusters (axiom validity; seed forcing).

**Estimated output**: ~250 lines. **Timing**: 2.5 hours.

**Done when**: axiom-validity lemma and seed-forcing lemma sorry-free; scoped build green.

**Verification**: as Phase 3.

---

### Phase 6: Exclusion theorem and the (R-b) interface endpoint [BLOCKED]: (R-a) refuted, see Phase 1

**Conditional**: as Phase 3.

**Goal**: `cs5Pair_rightExclusion_of_totalCountermodel`: from the hypothesis "some total
`is5FC` model has `u ⊩ H`, `v ⊮ A`, `r u v`", conclude
`cs5PairTauR A ∉ modalDeductiveClosure CS5PairAxiom (cs5PairSeed H)` (soundness of the pair
system over `M'` from Phase 5 + seed forcing + projection). Then STOP: document, in the module
docstring and the dispatch return, that discharging the hypothesis from the caller's `□A ∉ H`
is exactly (R-b), machine-checked equivalent to the collapse
(`is5_derivable_of_boxNotMem_transport`), and that continuation requires explicit user
authorisation. Report both consumers' status. No status of `[COMPLETED]` for the task without
that user decision — the endpoint is `[BLOCKED]`-with-deliverables or a user-directed follow-up.

**Verification Tier**: full

**Scope Hypothesis**: ~100-200 lines, one theorem plus docstring.

**Estimated output**: ~150 lines. **Timing**: 2 hours.

**Done when**: exclusion theorem sorry-free; endpoint documentation landed; full gate set run.

**Verification**: scoped `lake build` green; `lean_verify` sorry-free on the exclusion theorem;
`lake exe checkInitImports`, `lake exe lint-style`, shake/mk_all clean; repo-wide bare-`sorry`
count still 5; BibKey/constructor-name grep (as Phase 2) empty on all new files.

---

## Testing & Validation

- **Per-phase**: scoped `lake build` of every touched module; `lean_verify`/`#print axioms` on
  every new theorem (no `sorryAx`, no new axioms); zero new `sorry` anywhere.
- **End-of-task gates (both branches)**: `lake exe checkInitImports`, `lake exe lint-style`,
  `lake exe mk_all --module` consistency (shake), repo-wide bare-`sorry` count in `Cslib/`
  exactly 5, and the constructor-name/BibTag grep empty on all files this plan created.
- **Regression guard**: `cs5PairSeedDisjunctionProperty_false` / `_of_boxMem` and the whole
  Preserved Assets table still build unchanged (`git diff --stat` on preserved files shows only
  the sanctioned Phase 2 docstring edit).
- Verification tiers govern in-phase granularity only; the full gate set above runs before any
  phase closes the task.

## Artifacts & Outputs

- `specs/554_.../probes/ra_total_probe.lean` (Phase 1)
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5TotalModels.lean` (Phase 2, both branches)
- Kill branch: task closure record ([BLOCKED], §5.4 cost table, `requires_user_review`)
- Survive branch: `Cslib/Logics/Modal/Metalogic/Constructive/CS5ProductModel.lean`
  (Phases 3-6) with `cs5Pair_rightExclusion_of_totalCountermodel` and the (R-b) endpoint
  documentation
- Summary at `specs/554_.../summaries/03_ra-probe-summary.md` on wrap-up

## Rollback/Contingency

- **Phase 1 outcome (c) (both attempts fail in budget)**: no `Cslib/` edits exist yet; mark
  Phase 1 `[BLOCKED]` with goal states, `requires_user_review: true`. Nothing to roll back.
- **Phase 4 projection failure on the survive branch**: keep Phases 2-3's landed lemmas (they
  are true and library-grade regardless), record the failing case as the negative result, and
  execute the Phase 2 kill disposition retroactively — the failing goal state joins the §5.4
  cost table in the closure justification.
- **Any phase**: incremental commits at every green sub-step per git-workflow.md
  (`task {N} phase {P}.{O}` convention); a failed phase never orphans uncommitted green work.
- Preserved files are recoverable via git; the only sanctioned preserved-file edit (Phase 2
  docstring) is a pure addition, revertible in isolation.
