# Implementation Plan: Task #180 — Primitive allFuture (G) / allPast (H)

- **Task**: 180 - Add allFuture (G) and allPast (H) as primitive constructors to Temporal.Formula
- **Status**: [PARTIAL]
- **Effort**: 14-20 hours
- **Dependencies**: None
- **Research Inputs**: specs/180_temporal_primitive_always_historically/reports/01_primitive-always-historically-research.md
- **Artifacts**: plans/01_primitive-gh-implementation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; cslib.md
- **Type**: cslib
- **Lean Intent**: false

## Implementation Status (orchestration session sess_1782838873_48a805)

One implementation attempt was dispatched and **exhausted the agent context window**
("Prompt is too long") after editing the early-phase files. No phase was verified green and
**no checklist item below is confirmed complete** — the boxes remain unchecked deliberately.

- **Work-in-progress preserved** (durable): `specs/180_temporal_primitive_always_historically/wip/01_primitive-gh-wip.patch`
  (1063 lines; also retained in `git stash` entry `task180-wip-primitive-gh`). The patch touches
  all 7 Temporal files it reached: `Syntax/Formula.lean`, `Syntax/Subformulas.lean`,
  `Semantics/Satisfies.lean`, `ProofSystem/Axioms.lean`, `ProofSystem/Instances.lean`,
  `Tableau/Completeness.lean`, `Tableau/Rules.lean`. It is **incomplete and unverified** (does
  not build standalone — promoting the constructor breaks downstream until all cases are added).
- **Why it was parked**: promoting the constructor breaks the entire Temporal build until all 8
  phases land, which collides with sibling tasks (#406, #321) that also build the Temporal
  subtree. It must be implemented **alone**, on an otherwise-green Temporal tree.
- **Resume recipe**: `git apply specs/180_temporal_primitive_always_historically/wip/01_primitive-gh-wip.patch`
  (or `git stash apply`), then drive **one phase per agent run** — this task overflows a single
  multi-phase agent, so `/implement 180 --hard` (or `/orchestrate 180 --hard`) per-phase dispatch
  is required. Update each `### Phase N` heading to `[COMPLETED]` only after its scoped
  `lake build` is green.

## Overview

`Temporal.Formula` currently has primitives `{atom, bot, imp, untl, snce}`. The "all future"
(G) and "all past" (H) operators are derived abbreviations `Gφ := ¬𝐅¬φ` and `Hφ := ¬𝐏¬φ`,
which are only classically equivalent to genuine universal temporal quantification. This task
promotes `allFuture` and `allPast` to primitive constructors — giving the 7-constructor set
`{atom, bot, imp, and, or, untl, snce}` plus the two new `{allFuture, allPast}` (note: the
research report lists `and`/`or` in the primitive set per the task description, but in the
current source `and`/`or` are still `abbrev`s built from `imp`/`bot`; this task does **not**
change that and only adds `allFuture`/`allPast` as constructors). `someFuture` (F) and
`somePast` (P) remain derived abbreviations (`F = ⊤ U φ`, `P = ⊤ S φ`) because they need no
negation. The change enables intuitionistic temporal logics where `Gφ` is strictly stronger
than `¬𝐅¬φ`.

Definition of done: `allFuture`/`allPast` are inductive constructors with direct structural
semantics; all recursive functions over `Formula` handle the new cases; proof system, soundness,
and completeness (TruthLemma) carry the new cases; the classical equivalences `Gφ ↔ ¬𝐅¬φ` and
`Hφ ↔ ¬𝐏¬φ` are recovered as theorems; full CI is green.

### Research Integration

Grounded in `reports/01_primitive-always-historically-research.md`:
- **Axiom dependency analysis** (report §"Why G and H Appear in Axioms"): induction axioms
  `G(A→FA)→(A→GA)`, the G/H distribution axioms, and the interaction axioms `A→GP(A)`,
  `A→HF(A)` reference G/H essentially and cannot be re-expressed with only U/S. These already
  use the `.allFuture`/`.allPast` abbreviations in `Axioms.lean`, so the axiom statements are
  unchanged by promotion — only their *meaning* (now structural) changes.
- **Semantics** (report §"Semantics"): structural clauses `(M,t) ⊨ Gφ ↔ ∀s>t. (M,s) ⊨ φ` and
  `(M,t) ⊨ Hφ ↔ ∀s<t. (M,s) ⊨ φ`. The existing `allFuture_iff`/`allPast_iff` lemmas in
  `Satisfies.lean` already state exactly these; after promotion they become definitional
  (`Iff.rfl`-style), preserving every downstream proof that invokes them.
- **swapTemporal complication** (report §"Key Complication: swapTemporal"): the duality map
  needs explicit `| .allFuture φ => .allPast (swap φ)` cases; the existing
  `swapTemporal_allFuture`/`swapTemporal_allPast` theorems must be re-proved structurally.
- **Scope assessment** (report §"Scope Assessment"): ~10-15 files, smaller than task 176.
  Confirmed by codebase scan — only 3 files pattern-match Formula constructors directly
  (`Formula.lean`, `Satisfies.lean`, `Tableau/Defs.lean`, plus `Subformulas.lean`); the
  other ~20 files reference G/H only through abbreviations and `_iff` lemmas.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided; ROADMAP.md not consulted. This task advances the intuitionistic
temporal logic line (companion to tasks 173/176 which made propositional/`and`/`or` choices
explicit).

## Goals & Non-Goals

**Goals**:
- Add `allFuture` and `allPast` as inductive constructors of `Temporal.Formula`.
- Give them direct structural satisfaction clauses (no negation in the semantic definition).
- Update every recursive function over `Formula` (`complexity`, `temporalDepth`,
  `countImplications`, `swapTemporal`, `atoms`, `needsPositiveHypotheses`, `subformulas`,
  Tableau hashing/decomposition) to handle the new constructors.
- Keep `someFuture`/`somePast` derived; keep `Axioms.lean` statements unchanged (they already
  use `.allFuture`/`.allPast`).
- Re-prove `allFuture_iff`/`allPast_iff` and the `swapTemporal_*` duality theorems structurally.
- Carry the new cases through Soundness, MCS, Chronicle/TruthLemma, and Completeness.
- Add the classical equivalences `Gφ ↔ ¬𝐅¬φ`, `Hφ ↔ ¬𝐏¬φ` as theorems.
- Full CI green (`lake build`, `checkInitImports`, `lake lint`, `lint-style`, `lake test`,
  `shake`).

**Non-Goals**:
- Promoting `and`/`or` to constructors (out of scope; they remain abbreviations).
- Promoting `someFuture`/`somePast` to constructors (deliberately kept derived).
- Building out a full intuitionistic proof system or intuitionistic semantics — this task is
  the syntactic/semantic enabling step only; the existing classical axiomatization is retained.
- Changing the Pnueli guard/event convention for U/S.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Promotion breaks the entire downstream build at once (Formula.lean is foundational) | H | H | Sequence strictly by import-dependency; use scoped `lake build Module` per phase; accept that full-project green only returns at the final phase. |
| `complexity` currently matches the *expanded* G/H pattern (`.imp (.untl ⊤ ¬φ) ⊥`); those arms become dead and must be replaced with `.allFuture`/`.allPast` arms | M | H | Phase 1 explicitly removes the expanded-pattern arms and adds constructor arms; verify `complexity` still terminates and `Subformulas`/termination proofs hold. |
| `allFuture_iff`/`allPast_iff` proofs (currently unfold `neg`/`someFuture`) break | M | H | Re-prove as structural lemmas; statement is preserved so downstream callers are unaffected. |
| TruthLemma / Completeness require genuinely new inductive cases for G/H (not just abbreviation unfolding) — these are the hardest proofs | H | M | Isolated as the highest-risk phase (Phase 6); allow sub-division into G-case then H-case via `swapTemporal` duality; flag for `--hard` re-dispatch if a single agent run stalls. |
| MCS / canonical-model construction relies on G/H being `¬𝐅¬` for witness extraction | H | M | Phase 5 audits MCS helpers; if a lemma used the abbreviation defeq, replace with the new `_iff` lemma or the classical-equivalence theorem from Phase 8 (may require reordering — see contingency). |
| Bimodal embedding / OmegaSequence / other Temporal consumers outside `Cslib/Logics/Temporal` break | M | M | Phase 7 + Phase 8 verification sweep builds `Cslib.Logics.Bimodal.*` and `Cslib.Foundations.*Temporal*`; any breakage handled there or logged as a follow-up task. |
| Deriving `DecidableEq` still works with two new constructors | L | L | Automatic; verified by Phase 1 scoped build. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 4 |
| 7 | 8 | 6, 7 |

Phases within the same wave can execute in parallel. Phases 2 (Subformulas) and 3 (Semantics)
both depend only on the new constructors from Phase 1 and touch disjoint files, so they may run
in parallel. Phase 7 (Tableau) depends only on syntax+proof-system (Phase 4) and is independent
of the metalogic chain (Phases 5-6), so it can run in parallel with the metalogic work.

---

### Phase 1: Syntax — promote allFuture/allPast to constructors [COMPLETED]

- **Goal:** Add the two constructors and update every recursive function and duality theorem in
  `Formula.lean` so the syntax module builds in isolation.
- **Tasks:**
  - [ ] Add `| allFuture (φ : Formula Atom)` and `| allPast (φ : Formula Atom)` to the
    `inductive Formula` (keep `deriving DecidableEq`).
  - [ ] Remove the `abbrev Formula.allFuture`/`Formula.allPast` definitions; the notation
    `𝐆`/`𝐇` now binds directly to the constructors (`scoped prefix:40 "𝐆" => Formula.allFuture`
    still works because the constructor has the same name/arity).
  - [ ] Keep `someFuture`/`somePast` as abbreviations (unchanged).
  - [ ] `complexity`: delete the two expanded-G/H pattern arms
    (`.imp (.untl (.imp .bot .bot) (.imp φ .bot)) .bot` and the `.snce` analogue) and add
    `| .allFuture φ => 1 + complexity φ`, `| .allPast φ => 1 + complexity φ`. Keep the
    release/trigger expanded arms (they are genuinely derived). Confirm the match is still
    exhaustive and structurally decreasing.
  - [ ] `temporalDepth`: add `| .allFuture φ => 1 + φ.temporalDepth`,
    `| .allPast φ => 1 + φ.temporalDepth`.
  - [ ] `countImplications`: add `| .allFuture φ => φ.countImplications`, ditto `.allPast`.
  - [ ] `swapTemporal`: add `| .allFuture φ => .allPast (swapTemporal φ)` and
    `| .allPast φ => .allFuture (swapTemporal φ)`.
  - [ ] `atoms`: add `| .allFuture φ => atoms φ`, `| .allPast φ => atoms φ`.
  - [ ] `needsPositiveHypotheses`: covered by the `_ => true` fallback; add explicit `@[simp]`
    lemmas `needsPositiveHypotheses_allFuture/_allPast = true` if symmetry with existing lemmas
    is desired.
  - [ ] Re-prove the involution/duality theorems: extend the `induction φ with` blocks in
    `swapTemporal_involution` and `atoms_swapTemporal` with `allFuture`/`allPast` cases; re-prove
    `swapTemporal_allFuture`/`swapTemporal_allPast` structurally (now `simp only [swapTemporal]`
    suffices); keep `swapTemporal_someFuture`/`_somePast` (unchanged, abbreviation-based).
  - [ ] Update the module docstring constructor list and the derived-operator notes.
- **Timing:** 2-3 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Temporal/Syntax/Formula.lean` — constructors + all recursive functions +
    duality theorems + docstring.
- **Verification:**
  - `lake build Cslib.Logics.Temporal.Syntax.Formula`
  - Confirm `swapTemporal_involution`, `swapTemporal_allFuture`, `swapTemporal_allPast`,
    `atoms_swapTemporal` all compile with no `sorry`.

---

### Phase 2: Syntax — Subformulas and Context [COMPLETED]

- **Goal:** Extend constructor-recursive syntax helpers outside `Formula.lean`.
- **Tasks:**
  - [ ] `Subformulas.lean` `subformulas`: add
    `| φ@(.allFuture ψ) => φ :: subformulas ψ`, `| φ@(.allPast ψ) => φ :: subformulas ψ`.
  - [ ] Re-prove any `cases φ <;> simp [subformulas]` lemmas (`self_mem_subformulas`, etc.) —
    the new cases should fall out of the same tactic; add explicit arms only if needed.
  - [ ] `Context.lean`: scan for constructor matches; add G/H cases if present (grep showed
    abbreviation use only, so likely no change — verify).
- **Timing:** 1-1.5 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Temporal/Syntax/Subformulas.lean`
  - `Cslib/Logics/Temporal/Syntax/Context.lean` (only if it matches constructors)
- **Verification:**
  - `lake build Cslib.Logics.Temporal.Syntax.Subformulas Cslib.Logics.Temporal.Syntax.Context`

---

### Phase 3: Semantics — structural G/H clauses [COMPLETED]

- **Goal:** Give `allFuture`/`allPast` direct satisfaction clauses and make the
  characterization lemmas definitional.
- **Tasks:**
  - [ ] `Satisfies.lean` `Satisfies`: add
    `| .allFuture φ => ∀ s, t < s → Satisfies M s φ` and
    `| .allPast φ => ∀ s, s < t → Satisfies M s φ`.
  - [ ] Re-prove `allFuture_iff`/`allPast_iff` structurally — statement unchanged
    (`Satisfies M t (𝐆φ) ↔ ∀ s, t < s → Satisfies M s φ`); proof becomes `Iff.rfl` or
    `simp only [Satisfies]`. Keep `@[simp]` attributes consistent with existing lemmas
    (`someFuture_iff`/`somePast_iff` are `@[simp]`; consider marking the new ones too).
  - [ ] Confirm `someFuture_iff`/`somePast_iff` still hold (abbreviation-based, unchanged).
  - [ ] `Validity.lean` / `Model.lean`: verify no constructor match needs updating (grep showed
    none; confirm by build).
- **Timing:** 1.5-2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Temporal/Semantics/Satisfies.lean`
  - `Cslib/Logics/Temporal/Semantics/Validity.lean` (verify only)
- **Verification:**
  - `lake build Cslib.Logics.Temporal.Semantics.Satisfies Cslib.Logics.Temporal.Semantics.Validity`
  - Confirm `allFuture_iff`/`allPast_iff` compile; sanity-check that
    `Satisfies M t (𝐆φ)` now reduces to the universal clause definitionally.

---

### Phase 4: Proof system rebuild [IN PROGRESS]

- **Goal:** Rebuild `ProofSystem/*` against the new constructors. Axiom statements are unchanged
  (already use `.allFuture`/`.allPast`), so this is mostly a verification + minor-fix phase.
- **Tasks:**
  - [ ] `Axioms.lean`: confirm all axioms referencing `.allFuture`/`.allPast`/`.someFuture`/
    `.somePast` still elaborate; no statement change expected.
  - [ ] `Derivation.lean`, `Derivable.lean`, `Instances.lean`: build; fix any constructor-match
    sites or `Formula`-recursive helpers that need the new arms.
  - [ ] Re-check the `TemporalConnectives` instance and notation scoping still resolve.
- **Timing:** 1.5-2 hours
- **Depends on:** 2, 3
- **Files to modify:**
  - `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`
  - `Cslib/Logics/Temporal/ProofSystem/Derivation.lean`
  - `Cslib/Logics/Temporal/ProofSystem/Derivable.lean`
  - `Cslib/Logics/Temporal/ProofSystem/Instances.lean`
- **Verification:**
  - `lake build Cslib.Logics.Temporal.ProofSystem`

---

### Phase 5: Metalogic core — Soundness + MCS + helpers [HIGH RISK] [NOT STARTED]

- **Goal:** Carry the new constructors through soundness and the maximal-consistent-set
  machinery. **Second-largest / second-riskiest phase.**
- **Tasks:**
  - [ ] `Soundness.lean` / `DenseSoundness.lean`: the G/H-axiom soundness cases currently chain
    through `someFuture_iff`/`somePast_iff` and the `allFuture`/`allPast` abbreviation unfolding.
    Replace abbreviation-unfolding steps with the structural `allFuture_iff`/`allPast_iff` from
    Phase 3. Verify the induction/interaction/distribution axioms remain sound under the
    structural semantics (they should be *more* directly provable now).
  - [ ] `MCS.lean`: audit witness-extraction and saturation lemmas that assumed `Gφ = ¬𝐅¬φ`
    defeq. Where a proof relied on that defeq, substitute the new `_iff` lemma; if a step needs
    the classical equivalence `Gφ ↔ ¬𝐅¬φ`, note the dependency on Phase 8 and either inline a
    local lemma or reorder (see Contingency).
  - [ ] Supporting files: `CompletenessHelpers.lean`, `GeneralizedNecessitation.lean`,
    `WitnessSeed.lean`, `TemporalContent.lean`, `DeductionTheorem.lean`,
    `PropositionalHelpers.lean`, `GenericMCSBridge.lean`, `DerivationTree.lean`,
    `DenseMCS.lean` — build in dependency order; fix abbreviation-defeq breakages.
- **Timing:** 3-4 hours (consider splitting Soundness vs MCS if a single run stalls)
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Temporal/Metalogic/Soundness.lean`
  - `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean`
  - `Cslib/Logics/Temporal/Metalogic/MCS.lean`
  - `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean`
  - `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`
  - `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean`
  - `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`
  - `Cslib/Logics/Temporal/Metalogic/{DeductionTheorem,PropositionalHelpers,GenericMCSBridge,DerivationTree,DenseMCS}.lean` (as needed)
- **Verification:**
  - `lake build Cslib.Logics.Temporal.Metalogic.Soundness`
  - `lake build Cslib.Logics.Temporal.Metalogic.MCS`
  - `lake build Cslib.Logics.Temporal.Metalogic.DenseSoundness`
  - No `sorry` introduced (`lean_verify` on touched theorems).

---

### Phase 6: Metalogic — Chronicle / TruthLemma / Completeness [HIGHEST RISK, LARGEST] [NOT STARTED]

- **Goal:** Add genuine inductive cases for G/H in the truth lemma and complete the completeness
  proof. **This is the highest-risk and largest phase** — the truth lemma is proved by induction
  on formula structure, so G/H are now first-class cases rather than derived consequences of the
  `imp`/`untl` cases.
- **Tasks:**
  - [ ] `Chronicle/TruthLemma.lean`: add the `allFuture`/`allPast` inductive cases. Each direction
    (formula-in-MCS ⟹ forced, and forced ⟹ in-MCS) must be established directly from the
    structural semantics and the MCS G/H-saturation lemmas from Phase 5, rather than via the
    `¬𝐅¬` unfolding. Exploit `swapTemporal` duality: prove the `allFuture` case, then derive the
    `allPast` case by the past/future symmetry already used elsewhere in the file.
  - [ ] `Chronicle/*` supporting files (`ChronicleConstruction`, `ChronicleTypes`,
    `CanonicalChain`, `Frame`, `RRelation`, `PointInsertion`, `OrderedSeedConsistency`,
    `CounterexampleElimination`, `ChronicleToCountermodel`): add G/H cases where they recurse on
    constructors or build the canonical chain's G/H content.
  - [ ] `Completeness.lean` / `DenseCompleteness.lean`: thread the new TruthLemma cases through
    the final completeness statement; confirm the countermodel construction handles G/H.
- **Timing:** 4-6 hours (split into G-case sub-run and H-case/duality sub-run if needed;
  flag for `--hard` re-dispatch if a single agent run cannot close it)
- **Depends on:** 5
- **Files to modify:**
  - `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`
  - `Cslib/Logics/Temporal/Metalogic/Chronicle/{ChronicleConstruction,ChronicleTypes,CanonicalChain,Frame,RRelation,PointInsertion,OrderedSeedConsistency,CounterexampleElimination,ChronicleToCountermodel}.lean` (as needed)
  - `Cslib/Logics/Temporal/Metalogic/Completeness.lean`
  - `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean`
- **Verification:**
  - `lake build Cslib.Logics.Temporal.Metalogic.Chronicle.TruthLemma`
  - `lake build Cslib.Logics.Temporal.Metalogic.Completeness`
  - `lake build Cslib.Logics.Temporal.Metalogic` (whole metalogic subtree)
  - `lean_verify` on `TruthLemma` and the completeness theorem — zero `sorry`/axioms beyond
    those already accepted in the file.

---

### Phase 7: Tableau subtree [NOT STARTED]

- **Goal:** Add G/H constructor cases to the tableau machinery. Independent of the metalogic
  chain; can run in parallel with Phases 5-6.
- **Tasks:**
  - [ ] `Tableau/Defs.lean`: add `allFuture`/`allPast` arms to `temporalFormulaHash` and to the
    decomposition matchers (the `.imp …`-pattern extractors near lines 109-164). Decide tableau
    decomposition rules for primitive G/H (universal expansion) vs. the previous derived form.
  - [ ] `Tableau/Rules.lean`, `Tableau/Closure.lean`, `Tableau/Branch.lean`,
    `Tableau/Saturation.lean`, `Tableau/Soundness.lean`, `Tableau/Completeness.lean`,
    `Tableau/TimeOrdering.lean`: add G/H handling where they recurse on constructors or
    reference the G/H abbreviations.
- **Timing:** 2-3 hours
- **Depends on:** 4
- **Files to modify:**
  - `Cslib/Logics/Temporal/Tableau/Defs.lean`
  - `Cslib/Logics/Temporal/Tableau/{Rules,Closure,Branch,Saturation,Soundness,Completeness,TimeOrdering}.lean` (as needed)
- **Verification:**
  - `lake build Cslib.Logics.Temporal.Tableau.Defs`
  - `lake build Cslib.Logics.Temporal.Tableau.Soundness Cslib.Logics.Temporal.Tableau.Completeness`

---

### Phase 8: Classical-equivalence theorems + downstream sweep + full CI [NOT STARTED]

- **Goal:** Recover the classical equivalences as theorems, fix any remaining downstream
  consumers, and pass the full CI pipeline.
- **Tasks:**
  - [ ] Add theorems (location: `Theorems.lean` or `ProofSystem/Derivable.lean`, matching
    existing convention):
    `allFuture_iff_neg_someFuture_neg : ⊢ (𝐆φ ↔ ¬𝐅¬φ)` and
    `allPast_iff_neg_somePast_neg : ⊢ (𝐇φ ↔ ¬𝐏¬φ)`, derivable from Peirce's law + temporal
    axioms (classical conservative-extension check, report §"Classical Equivalence as Theorem").
    Also add the semantic counterparts in `Satisfies` if useful.
  - [ ] `ConservativeExtension.lean`, `FromPropositional.lean`, `Theorems.lean`,
    `TemporalDerived.lean`: build and fix.
  - [ ] Downstream sweep — build consumers outside the Temporal namespace:
    `Cslib.Logics.Bimodal.Embedding.TemporalEmbedding`, the Bimodal metalogic/syntax temporal
    files, and `Cslib.Foundations.*Temporal*`. Fix breakage or log a follow-up task if a
    consumer needs substantial rework beyond this task's scope.
  - [ ] Update `Cslib.lean` barrel (`lake exe mk_all --module`) if any new files were added
    (none expected — all changes are in-place).
  - [ ] Run full CI pipeline.
- **Timing:** 2-3 hours
- **Depends on:** 6, 7
- **Files to modify:**
  - `Cslib/Logics/Temporal/Theorems.lean`
  - `Cslib/Logics/Temporal/ConservativeExtension.lean`
  - `Cslib/Logics/Temporal/FromPropositional.lean`
  - `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`
  - `Cslib/Logics/Bimodal/**` temporal consumers (as needed)
- **Verification (full CI, in order):**
  - `lake exe cache get`
  - `lake build`
  - `lake exe checkInitImports`
  - `lake lint`
  - `lake exe lint-style`
  - `lake test`
  - `lake shake --add-public --keep-implied --keep-prefix`

---

## Testing & Validation

- [ ] `lake build` green for the whole project after Phase 8.
- [ ] `lake exe checkInitImports` passes (no new files, but verify).
- [ ] `lake lint` and `lake exe lint-style` clean on all modified files (docstrings on new
  constructors and theorems).
- [ ] `lake test` (CslibTests) passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no import regressions.
- [ ] No new `sorry` or unexpected axioms (`lean_verify` on TruthLemma, Completeness, Soundness,
  and the new classical-equivalence theorems).
- [ ] `allFuture_iff`/`allPast_iff` are definitional/structural; `someFuture_iff`/`somePast_iff`
  unchanged.
- [ ] `swapTemporal_involution`, `swapTemporal_allFuture`, `swapTemporal_allPast` re-proved.
- [ ] Classical equivalences `𝐆φ ↔ ¬𝐅¬φ` and `𝐇φ ↔ ¬𝐏¬φ` derivable as theorems.

## Artifacts & Outputs

- `specs/180_temporal_primitive_always_historically/plans/01_primitive-gh-implementation.md` (this plan)
- Modified Lean sources across `Cslib/Logics/Temporal/{Syntax,Semantics,ProofSystem,Metalogic,Tableau}/`
  plus `Theorems.lean`, `ConservativeExtension.lean`, `FromPropositional.lean`, and any affected
  Bimodal/Foundations temporal consumers.
- `specs/180_temporal_primitive_always_historically/summaries/01_primitive-gh-implementation-summary.md` (on completion)

## Rollback/Contingency

- **Rollback:** All changes are in-place source edits on existing files with no new files; revert
  with `git checkout -- Cslib/Logics/Temporal/ ...` or drop the task branch. No state migration.
- **Build-green ordering caveat:** Promoting the constructor in Phase 1 breaks the full-project
  build until Phase 8. Each phase verifies via *scoped* `lake build Module` of the modules it
  owns; only run full `lake build` at Phase 8. This is expected, not a failure.
- **Phase 5/6 ordering dependency on Phase 8 equivalences:** If an MCS or TruthLemma step
  genuinely needs the classical equivalence `𝐆φ ↔ ¬𝐅¬φ`, prove a *local* version of that
  equivalence inside Phase 5/6 (it follows from the existing classical axioms) rather than
  reordering Phase 8 earlier. If that proves intractable, split: do the syntactic equivalence
  theorems first as a new early phase, then resume metalogic.
- **Phase 6 stall:** If a single agent run cannot close the TruthLemma G/H cases, re-dispatch
  with `--hard` and/or split into a G-case run and an H-case/duality run. Mark the phase
  `[PARTIAL]` with the exact goal state and what saturation lemma is missing; do **not** insert
  `sorry` or vacuous definitions.
- **Downstream consumer breakage (Phase 8):** If a Bimodal/Foundations consumer needs rework
  beyond mechanical case additions, log a follow-up task and mark this task `[PR READY]` for the
  Temporal subtree, scoping the consumer fix separately.
