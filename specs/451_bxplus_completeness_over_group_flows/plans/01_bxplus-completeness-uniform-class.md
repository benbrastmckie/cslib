# Implementation Plan: BX⁺ Completeness over the Uniform Class + Dense→ℚ Bridge

- **Task**: 451 - BX+ completeness over ordered-abelian-group time flows
- **Status**: [COMPLETED]
- **Effort**: 9.5 hours
- **Dependencies**: 449 (BX⁺ definition + oag soundness, already complete)
- **Research Inputs**: reports/01_bxplus-completeness-frame-class.md
- **Artifacts**: plans/01_bxplus-completeness-uniform-class.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/plan-format-enforcement.md
  - .claude/rules/state-management.md
  - .claude/rules/cslib.md
  - .claude/rules/lean4.md
  - .claude/rules/plan-compliance.md
- **Type**: lean4

## Overview

Prove the honest, zero-debt completeness result the research decided on: **BX⁺
(`Temporal.BXPlusDerivable` = `ThDerivableFc FrameClass.Metric`) is complete over the uniform
serial-linear class `U`** — the standard "frames validating the four uniformity axioms" class —
mirroring the existing `completeness_dense`. Additionally deliver the **dense→ℚ (ordered-abelian-
group) bridge**: a general `Satisfies` transport lemma along an order isomorphism plus a Cantor
(`Order.iso_of_countable_dense`) refutation corollary landing dense countermodels on ℚ, which is
the concrete artifact that unlocks task 450's semantic route. The literal completeness of BX⁺
over the *whole* ordered-abelian-group class (the discrete sub-case) is **not** attempted: the
research established it is very likely false (BX⁺ lacks a discreteness/archimedean axiom, so a
non-homogeneous `ℤ ×ₗ A` block index is a valid BX⁺ frame but not an oag) and it is escalated as
a precise open lemma in the module docstring and the Risks section — no `sorry`, no axiom, no
vacuous def.

Definition of done: new file `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` builds
sorry-free; `completeness_metric` and the dense→ℚ bridge corollary are stated and proved; a
soundness-over-`U` theorem is added so soundness and completeness are stated over the same class
(packaging option (b), justified below); full CSLib CI is green.

### Research Integration

Key research verdicts honored:
- **Do NOT prove literal oag-completeness** (discrete case likely false; structural obstruction,
  no Mathlib bridge). Escalated, not implemented.
- **Complete over `U`** by mirroring `DenseCompleteness.lean` — the Metric case is the same
  chronicle skeleton with the four uniformity axioms (theorems in every limit-MCS) satisfied at
  every chronicle point instead of the single density axiom.
- **Dense→ℚ bridge** = the general `Satisfies_orderIso` transport lemma (does not exist; ~60–120
  lines, formula induction, explicit witness transport for `untl`/`snce` — not `simp`/`aesop`) +
  Cantor + verified ℚ oag instances.
- **Packaging option (b)** chosen: add a soundness-over-`U` theorem so `BX⁺ = Th(U)` is an exact
  sound-and-complete pair, retaining oag soundness as the `oag ⊆ U` corollary (justified in
  Phase 2).

Correction to the report's transport-lemma sketch: `TemporalModel D Atom` is a **structure** with
field `valuation : D → Atom → Prop` (`Semantics/Model.lean:42`), not a bare function. The pulled-
back model is `{ valuation := fun q p => M.valuation (e.symm q) p }`, not `fun q => M (e.symm q)`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (roadmap flag not set). Task advances the "Bimodal Logic" topic:
BX⁺ metatheory and the semantic route for task 450.

## Goals & Non-Goals

**Goals**:
- General `Satisfies_orderIso` transport lemma along `≃o` (reusable; unlocks task 450).
- `validMetricUniform` (`U`-validity) definition in `Semantics/Validity.lean`.
- Soundness over `U` (`BXPlusDerivable φ → validMetricUniform φ`), with oag soundness as corollary.
- The four uniformity axioms satisfied at every chronicle point built from a Metric-MCS.
- `completeness_metric : validMetricUniform φ → BXPlusDerivable φ`, mirroring `completeness_dense`.
- Dense→ℚ refutation corollary: a countable dense serial countermodel transports to the oag ℚ.
- Precise escalation of the open literal-oag-completeness lemma in the module docstring.
- Sorry-free, lint-clean, full CI green; new file wired into the `Metalogic.lean` barrel.

**Non-Goals**:
- Proving BX⁺ complete over the literal ordered-abelian-group class (discrete sub-case) — escalated.
- Strengthening BX⁺ with a discreteness/archimedean axiom — belongs to a NEW task if desired.
- Modifying `TemporalModel`, the axiom set, or `FrameClass.Metric`.
- Any change to task 449's oag soundness (`MetricSoundness.lean`) beyond adding the `oag ⊆ U`
  corollary.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Exact Lean encoding of the `U` class ("axiom-schema validity" vs. a semantic frame predicate) is ambiguous | H | M | Phase 2 fixes it first: primary recommendation is the **axiom-schema-validity** formulation (chronicle membership = the four `discrete_*` axioms satisfied everywhere, which Phase 3 proves via `theoremInMcsFc` + truth lemma). Choose the encoding that makes Phase 3's chronicle-membership lemma discharge the completeness hypothesis directly; do not invent a bespoke `Densely ∨ Discrete` predicate. |
| `untl`/`snce` transport step under-constrained if done with `simp`/`aesop` | M | M | Research advisory: prove the interval-emptiness quantifier step with explicit witness maps (`e c` / `e.symm c`) using `e.lt_iff_lt`, `e.symm_apply_apply`; the `Satisfies` unfolding is definitional (`Satisfies.lean:70–77`). |
| `dense_indicator_in_all_limit_points` analogue for four axioms is intricate (mirrors an ~70-line proof ×4) | M | M | Phase 3 reuses the exact `theoremInMcsFc h_mcs (.axiom [] _ .discrete_* (le_refl _))` + truth-lemma pattern; the four axioms are *theorems in every limit-MCS*, so no per-axiom C4 gymnastics like the dense case — membership → satisfaction is direct via `chronicle_truth_lemma`. |
| Literal oag-completeness pressure (task text names oag) | H | L | Compliant by design: research + task both authorize refining to `U` and escalating the oag gap. Escalation recorded in docstring + Risks; NOT papered over. |
| **OPEN / ESCALATED**: literal BX⁺-over-oag completeness (discrete case) | — | — | Very likely FALSE. Reduces to the open lemma "every discrete BX⁺-consistent formula has a homogeneous (`ℤ` / `ℤ ×ₗ ℚ`) oag countermodel"; expected `Th(oag) ⊋ BX⁺`. No Mathlib support (order-embeddings destroy `U(⊥,⊤)`). Resolution, if ever wanted: a NEW task strengthening BX⁺ with a discreteness/archimedean axiom (a new `FrameClass ≥ Metric`). Do NOT attempt here. |
| CI import-minimization (`shake`) strips a needed public import | L | L | Phase 6 runs the full 7-step CI order per `cslib.md`; `public import` MetricSoundness + DenseCompleteness for the reused chronicle/dichotomy lemmas; use `--fix` review. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 2, 3 |
| 3 | 5 | 1, 4 |
| 4 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Note: per `plan-compliance.md`, Lean
implementation still executes phases in listed order; the wave table records logical dependency,
not a license to reorder.

---

### Phase 1: `Satisfies_orderIso` transport lemma [COMPLETED]

**Goal**: Prove the general satisfaction-transport lemma along an order isomorphism — the one new
general lemma the research identified (reusable, unlocks task 450).

**Tasks**:
- [ ] Create `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` with header (`import
  Cslib.Init`, `module`, copyright, module docstring stub — full escalation docstring lands in
  Phase 6), `public import` of `MetricSoundness` and `DenseCompleteness`.
- [ ] State `Satisfies_orderIso {D E : Type*} [LinearOrder D] [LinearOrder E] (e : D ≃o E)
  (M : TemporalModel D Atom) (t : D) (φ : Formula Atom) : Satisfies M t φ ↔
  Satisfies { valuation := fun q p => M.valuation (e.symm q) p } (e t) φ` (correct the report's
  bare-function sketch to the `TemporalModel` structure — see Overview correction).
- [ ] Prove by `induction φ`. Atoms: `e.symm_apply_apply`. `bot`/`imp`: congruence.
- [ ] `untl`/`snce` (and derived `allFuture`/`allPast`): explicit witness transport using
  `e.lt_iff_lt` and the monotone-bijection interval bridge `c ∈ (t,s) ↔ e c ∈ (e t, e s)`. Do
  NOT use `simp`/`aesop` for the interval-emptiness quantifier (research advisory).
- [ ] `lean_multi_attempt` before each non-trivial step; `lean_goal` to confirm each case.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` - new file; add transport lemma.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MetricCompleteness` green for the transport lemma.
- `lean_verify Cslib.Logic.Temporal.Satisfies_orderIso` — no `sorry`, no unexpected axioms.

---

### Phase 2: `validMetricUniform` definition + soundness over `U` [COMPLETED]

**Goal**: Define the uniform-class validity `U` and prove BX⁺ soundness over it (packaging option
(b)), so soundness and completeness are stated over the same class.

**Justification of packaging option (b)**: The research offered (a) keep soundness at oag + add
completeness at `U`, or (b) add soundness-over-`U` for an exact `BX⁺ = Th(U)` pair. Option (b) is
chosen because the soundness-over-`U` direction is *easy* (on any frame that validates the four
axioms by definition of `U`, plus base soundness for the base axioms, the metric axiom instances
hold definitionally) and it yields a self-contained sound-and-complete pair over a single class.
oag soundness is retained as the `oag ⊆ U` corollary (every oag frame validates the axioms — this
is exactly task 449's `axiom_sound_metric`).

**Tasks**:
- [ ] Fix the `U` encoding first (see Risks): define `validMetricUniform (φ : Formula Atom) : Prop`
  in `Semantics/Validity.lean` as validity over serial linear orders that validate the four
  uniformity axioms semantically. Recommended: the axiom-schema-validity formulation, so that a
  frame is in `U` iff every instance of `discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd` is
  satisfied at every point. Mirror the `validDense` def shape (`Validity.lean:? ` — `validDense`
  block) with the axiom hypotheses replacing `[DenselyOrdered D]`.
- [ ] lowerCamelCase name (`defsWithUnderscore`); house-style docstring (`docBlame`).
- [ ] Prove `soundness_thderivable_uniform : BXPlusDerivable φ → validMetricUniform φ` mirroring
  `soundness_thderivable_metric` / `soundness_thderivable_dense`, carrying the class hypothesis.
- [ ] Prove/record the `oag ⊆ U` corollary: an ordered-abelian-group frame validates the four
  axioms (reuse `axiom_sound_metric`), so `validMetricUniform φ → (oag validity of φ)` recovers
  task 449's statement.

**Timing**: ~1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Semantics/Validity.lean` - add `validMetricUniform` def.
- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` - add soundness-over-`U` theorem +
  `oag ⊆ U` corollary. (Alternatively co-locate soundness in `MetricSoundness.lean`; implementer's
  choice, but keep the `validMetricUniform` def in `Validity.lean` next to its siblings.)

**Verification**:
- `lake build` of the touched modules green.
- `lean_verify` on `validMetricUniform` soundness theorem — sorry-free.

---

### Phase 3: Uniformity axioms satisfied at every chronicle point [COMPLETED]

**Goal**: Prove the new propagation lemma(s): the chronicle model built from a Metric-MCS
satisfies each of the four uniformity axiom formulas at every chronicle point — the Metric analogue
of `dense_indicator_in_all_limit_points`. This is the chronicle-membership-in-`U` witness.

**Tasks**:
- [ ] For each of the four axioms, obtain its membership in every limit-MCS via
  `theoremInMcsFc h_mcs (.axiom [] _ .discrete_symm_fwd (le_refl _))` (and `_bwd`,
  `discrete_propagate_fwd/bwd`), mirroring `dense_indicator_in_dense_mcs` /
  `g_dense_indicator_in_dense_mcs`.
- [ ] Bridge membership → satisfaction at every chronicle point via `chronicle_truth_lemma`
  (`Chronicle/TruthLemma.lean`), reusing the `limit_c0` / `limit_f_zero` machinery seen in
  `DenseCompleteness.lean:181–219`. Because the axioms are *theorems in every limit-MCS*, this is
  more direct than the dense case — no per-point C4 trichotomy is needed for membership itself
  (the dense case only needed C4 to propagate a *non-theorem* `¬U(⊤,⊥)`; the four metric axioms
  are theorems everywhere).
- [ ] Package as a lemma establishing chronicle membership in the `U` class (matching whichever
  `validMetricUniform` encoding Phase 2 fixed) — i.e. the chronicle model satisfies the axiom
  hypotheses of `validMetricUniform` at every point.

**Timing**: ~2 hours

**Depends on**: none (structurally independent; conceptually feeds Phase 4)

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` - add axioms-on-chronicle lemma(s).

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MetricCompleteness` green.
- `lean_verify` on the axioms-on-chronicle lemma(s) — sorry-free.

---

### Phase 4: `completeness_metric` over `U` [COMPLETED]

**Goal**: Prove `completeness_metric : validMetricUniform φ → BXPlusDerivable φ`, the honest BX⁺
completeness theorem, mirroring `completeness_dense` exactly.

**Tasks**:
- [ ] Mirror `completeness_dense` (`DenseCompleteness.lean:252–269`): contrapositive →
  `neg_consistent_of_not_derivable` at `FrameClass.Metric` (add the Metric analogue of
  `neg_consistent_of_not_derivable_dense` if not reusable) → `temporal_lindenbaum_fc` → build
  `ChronicleSubtype M` + `chronicleModel` + `chronicleZero`.
- [ ] Discharge the `validMetricUniform` axiom hypotheses using Phase 3's axioms-on-chronicle
  lemma, then apply the validity hypothesis at `t₀` and `chronicle_truth_lemma` to get `φ ∈ M`,
  contradicting `φ ∉ M`.
- [ ] Name the theorem `completeness_metric`; house-style docstring; `@[nolint dupNamespace]` if a
  `Temporal.`-prefixed name inside `namespace …Temporal` (mirror `BXPlusDerivable`).

**Timing**: ~1.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` - add `completeness_metric` (+ Metric
  `neg_consistent_of_not_derivable` helper if needed).

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MetricCompleteness` green.
- `lean_verify Cslib.Logic.Temporal.completeness_metric` — sorry-free, no unexpected axioms.

---

### Phase 5: Dense→ℚ (oag) bridge corollary [COMPLETED]

**Goal**: Deliver the concrete task-450 artifact: a dense countermodel transports to the ordered-
abelian-group ℚ via Cantor + Phase 1's transport lemma.

**Tasks**:
- [ ] Prove the general refutation corollary: for a `Countable + DenselyOrdered + NoMinOrder +
  NoMaxOrder + Nonempty` linear order `D`, a model/time refuting `φ` yields a model on ℚ refuting
  `φ`. Obtain `e : D ≃o ℚ` via `obtain ⟨e⟩ := Order.iso_of_countable_dense D ℚ` (all ℚ instances
  verified present: `AddCommGroup ℚ`, `IsOrderedAddMonoid ℚ`, `DenselyOrdered ℚ`, `NoMax/MinOrder ℚ`,
  `Nontrivial ℚ`; subtype-of-ℚ `Countable`; `Nontrivial → Nonempty`), then transport with
  `Satisfies_orderIso` and the pulled-back valuation `fun q p => M.valuation (e.symm q) p`.
- [ ] Wire to the dense chronicle: in the dense branch, `ChronicleSubtype M` carries
  `Countable + DenselyOrdered (via chronicleDenselyOrderedDense-style) + NoMin + NoMax + Nonempty`,
  so a dense-consistent BX⁺ formula refutes on ℚ — i.e. the dense fragment of BX⁺ is complete over
  the oag ℚ. State this as the headline bridge corollary that task 450 will consume.
- [ ] Docstring both results, cross-referencing task 450's semantic route (durable anchor: name the
  bridge corollary and `Order.iso_of_countable_dense`, not a task number, in the deliverable file
  per `no-task-references-in-deliverables.md`).

**Timing**: ~2 hours

**Depends on**: 1, 4

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` - add dense→ℚ transport corollary +
  the oag-ℚ dense-fragment completeness statement.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MetricCompleteness` green.
- `lean_verify` on the ℚ-bridge corollary — sorry-free.

---

### Phase 6: Escalation docstring, barrel wiring, full CI [COMPLETED]

**Goal**: Record the escalated open lemma, wire the new file into the library, and pass full CI.

**Tasks**:
- [x] Complete the `MetricCompleteness.lean` module docstring: state the main results
  (`Satisfies_orderIso`, `validMetricUniform`, soundness-over-`U`, `completeness_metric`, ℚ-bridge)
  AND the escalation note — literal BX⁺-over-oag completeness reduces to the open, expected-false
  lemma "every discrete BX⁺-consistent formula has a homogeneous (`ℤ` / `ℤ ×ₗ ℚ`) oag countermodel";
  resolution would need a discreteness/archimedean axiom (a new `FrameClass ≥ Metric`) — a separate
  task, not this one. Cite `Burgess1984` §6.1 (metric = oag time, but metric-operator language) and
  `Xu1988` Thm 2.9 (successor not U,S-definable) as durable anchors. No task numbers in the file.
  *(written at file creation in Phase 1; verified current in Phase 6, no changes needed)*
- [x] Add `public import Cslib.Logics.Temporal.Metalogic.MetricCompleteness` to
  `Cslib/Logics/Temporal/Metalogic.lean` barrel.
- [x] Run full CSLib CI in order (`cslib.md`): `lake exe cache get`; `lake build`; `lake exe
  checkInitImports`; `lake lint`; `lake exe lint-style`; `lake test`; `lake exe mk_all --module`;
  `lake shake --add-public --keep-implied --keep-prefix`. Fix lint (docBlame, defLemma,
  defsWithUnderscore, simpNF, unusedSectionVars, dupNamespace) per research zero-debt notes.
  *(all steps green; zero lint/lint-style/shake findings in the touched files; pre-existing
  unrelated warnings/sorries in other Cslib files, e.g. Propositional/Tableau, left untouched)*
- [x] Final `lean_verify` sweep on all new public declarations — confirm zero `sorry`, zero new
  axioms across the deliverable.

**Timing**: ~1 hour

**Depends on**: 1, 2, 3, 4, 5

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` - finalize docstring.
- `Cslib/Logics/Temporal/Metalogic.lean` - barrel import.
- `Cslib.lean` - via `mk_all --module` (only if the barrel change requires it).

**Verification**:
- Full `lake build` green; `lake lint` and `lake exe lint-style` clean; `lake exe checkInitImports`
  passes; `lake test` passes; `lake shake` reports no needed changes (or `--fix` applied).

---

## Testing & Validation

- [x] `lake build` (full project) green, no `sorry`, no new axioms.
- [x] `lean_verify` on each new public declaration: `Satisfies_orderIso`, `validMetricUniform`
  soundness theorem, axioms-on-chronicle lemma(s), `completeness_metric`, the dense→ℚ bridge
  corollary — all sorry-free with only expected axioms (`Classical.propDecidable` is already a
  local instance in the dense template).
- [x] `lake lint` clean (docBlame, defLemma, defsWithUnderscore, simpNF, unusedSectionVars,
  dupNamespace) for all files touched by this task.
- [x] `lake exe checkInitImports` passes (transitively imports `Cslib.Init` via `MetricSoundness`).
- [x] `lake exe lint-style` clean.
- [x] `lake test` passes (`CslibTests/`).
- [x] `lake shake --add-public --keep-implied --keep-prefix` reports no changes for the files
  touched by this task.
- [x] Escalation note present in the module docstring; no `sorry`/axiom stands in for the open
  oag-completeness lemma.

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Metalogic/MetricCompleteness.lean` (new): `Satisfies_orderIso`,
  `validMetricUniform` soundness, axioms-on-chronicle lemma(s), `completeness_metric`, dense→ℚ
  bridge corollary, escalation docstring.
- `Cslib/Logics/Temporal/Semantics/Validity.lean` (modified): `validMetricUniform` def.
- `Cslib/Logics/Temporal/Metalogic.lean` (modified): barrel import.
- `Cslib.lean` (modified if `mk_all` requires): top-level barrel.
- `specs/451_bxplus_completeness_over_group_flows/summaries/01_bxplus-completeness-uniform-class-summary.md`
  (on implementation completion).

## Rollback/Contingency

- All new work is additive in one new file plus a def in `Validity.lean` and one barrel import.
  Rollback = remove `MetricCompleteness.lean`, revert the `Validity.lean` def and the barrel line,
  re-run `mk_all --module`; nothing else depends on the new declarations.
- If Phase 3 (axioms-on-chronicle) or Phase 4 (completeness) hits a genuine obstruction, mark the
  phase `[BLOCKED]` per `plan-compliance.md` (do NOT substitute a `sorry` or vacuous def), keep the
  green Phases 1–2 and 5's general transport lemma (independently valuable for task 450), and
  escalate. The transport lemma + dense→ℚ corollary (Phases 1, 5) stand alone as the task-450
  deliverable even if the `U`-completeness packaging needs another round.
- The literal-oag-completeness gap is already escalated by design (Risks + docstring), not a
  rollback trigger.
