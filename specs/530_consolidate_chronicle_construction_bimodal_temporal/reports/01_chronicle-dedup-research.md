# Research: Consolidating the Bimodal & Temporal Chronicle Trees

**Task**: Factor the shared Burgess-1982 chronicle / countermodel-elimination machinery
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
duplicated across `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/` and
`Cslib/Logics/Temporal/Metalogic/Chronicle/` into a label-generic module under
`Cslib/Foundations/Logic/Metalogic/Chronicle/`, and have both logics instantiate it.
Structural dedup only — no proof changes, preserve all landed sorry-free results, do not
entangle the bimodal discrete-completeness sorries.

## 1. Executive Summary

- The two trees are near-duplicate ports of one Burgess construction. Divergence is almost
  entirely **mechanical** along three axes (fc-threading, connective spelling, namespace/type
  identity), not mathematical. Measured overlap: `ChronicleTypes` ~95%, `ChronicleConstruction`
  ~92-93% (59 declarations 1:1), `CounterexampleElimination` ~95%+, `RRelation` shared core
  ~38 lemmas (temporal is essentially a subset of bimodal).
- The consolidation pattern is **already established and landed**:
  `Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` defines
  `SinceSeedInterface F` — an interface-parameterized `structure` bundling abstract formula
  operators, an abstract `Type*`-valued derivation family, and MCS/Burgess apparatus lemmas as
  fields — and both trees' `PointInsertion/Since.lean` already instantiate it. This task extends
  that exact approach to the rest of the chronicle machinery. Reuse-first is satisfied by
  building on `SinceSeedInterface` + `GenericMCS.HilbertTree`, not inventing a new abstraction.
- **Recommended approach**: a phased, interface-first extraction. Start with `ChronicleTypes`
  (lowest risk, pure defs + basic theorems), then `RRelation` shared core, then the large
  `CounterexampleElimination` pipeline, then `ChronicleConstruction`. Each phase keeps
  `lake build` green and leaves a green commit.
- **Do NOT touch** `Bimodal/.../Chronicle/ChronicleToCountermodel.lean`. It carries the only
  real proof-level sorries in the tree (discrete/gap-elimination pipeline, all blocked on the
  external `WeakCanonical.IntegerModel.GoodStructuresModelSurgery` port). It has no temporal
  counterpart and is genuinely divergent. Keep it logic-specific and untouched.
- **Task-premise correction**: the description says to "watch the bimodal RRelation sorry".
  `RRelation.lean` is currently **sorry-free**; its only "sorry" is a stale doc-comment at
  line 40. `ChronicleToCountermodelBasic.lean`'s "sorry" mentions are also doc-comments. The
  real proof sorries live only in `ChronicleToCountermodel.lean`. The stale comment should be
  corrected as cleanup.

## 2. Current State Map

### Three trees

| Location | Files | Sorries | Frame parameterization |
|---|---|---|---|
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/` | 7 top-level + `PointInsertion/` (4) + `CounterexampleElimination/` (4) | real sorries only in `ChronicleToCountermodel.lean` | `(fc : FrameClass)` threaded everywhere |
| `Cslib/Logics/Temporal/Metalogic/Chronicle/` | 10 top-level + `PointInsertion/` (4) + `CounterexampleElimination/` (4) | **zero** (fully sorry-free) | fixed to `FrameClass.Base` |
| `Cslib/Foundations/Logic/Metalogic/Chronicle/` | `SinceSeedConsistency.lean` only | zero | interface-parameterized over `F` |

File sizes (lines): Bimodal `ChronicleConstruction` 1532, `RRelation` 1694, `ChronicleTypes` 431,
`ChronicleToCountermodelBasic` 1209, `ChronicleToCountermodel` 233, `CounterexampleElimination/`
{Interface 3049, Elimination 244, BurgessHelpers 219, Structures 157}.
Temporal `ChronicleConstruction` 1435, `RRelation` 746, `ChronicleTypes` 376, `ChronicleToCountermodel`
137, `TruthLemma` 295, `Frame` 254, `OrderedSeedConsistency` 135, `CanonicalChain` 76,
`CounterexampleElimination/` {MainElimination 1685, RecursiveWalks 1125, Elimination 268, Structures 274}.

### Barrel wiring
- Foundations modules are barreled in the root `Cslib.lean` (line 88 already imports
  `Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`). New generic modules add here.
- Bimodal tree barreled in `Cslib/Logics/Bimodal/Metalogic.lean`; temporal in
  `Cslib/Logics/Temporal/Metalogic.lean`.

## 3. The Established Precedent (Reuse-First)

Two landed Foundations modules define exactly the abstraction pattern this task needs:

1. **`Foundations/Logic/Metalogic/GenericMCS.lean`** — the algebraic MCS seam:
   `DerivationSystem`, `HilbertTree` (a `Type*`-valued abstract derivation family), and the
   generic MCS machinery (`closed_under_derivation`, `implication_property`,
   `negation_complete`). fc-polymorphic. This is the base precedent for a `Type*`-valued
   abstract derivation family.

2. **`Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean`** — `SinceSeedInterface F`
   (namespace `Cslib.Logic.Metalogic.Chronicle`). A `structure` (not a `class`) bundling:
   - abstract formula operators (`and`, `untl`, `snce`, `somePast`, `allPast`);
   - an abstract `Deriv : List F → F → Type*` derivation family;
   - low-level derivation combinators (assumption, modusPonens, weakening, deductionTheorem,
     impTrans, etc.) each logic already proves;
   - the Burgess/MCS apparatus lemmas as **statements only** (each logic supplies its proof).

   Purely definitional notions (`SetConsistent`, `SetMaximalConsistent`,
   `ClosedUnderDerivation`, `deductiveClosure`, `burgessR*`, `BurgessR3Maximal`, `gContent`,
   `hContent`, `listConj`) are **not** interface fields — they are generic `def`s parameterized
   by an interface value, since both logics define them identically modulo the axes.

   Design note in that file (authoritative): a `structure` is used, not a `class`, because
   Bimodal needs an **instance family indexed by `fc : FrameClass`** while Temporal needs
   exactly one instance — explicit passing (as with `HilbertTree`) is clearer than instance
   resolution across several live `fc`.

Both trees already instantiate `SinceSeedInterface` in their `PointInsertion/Since.lean`. The
task's "partial prior consolidation" is precisely this Since-seed extraction.

## 4. Divergence Axes (uniform across all files)

Bimodal and Temporal have **genuinely distinct** `Formula` types
(`Logics/Bimodal/Syntax/Formula.lean` vs `Logics/Temporal/Syntax/Formula.lean`) and **distinct**
`DerivationTree` types (both `inductive DerivationTree (fc : FrameClass)` but over different,
per-logic `FrameClass`). Direct code-sharing is therefore impossible; interface-parameterization
over an abstract `F` and abstract derivation family is mandatory. The three axes are:

| Axis | Bimodal | Temporal |
|---|---|---|
| (a) frame class | `(fc : FrameClass)` threaded through every def/theorem; `DerivationTree fc`; `SetMaximalConsistent fc` | fixed `FrameClass.Base`; `Temporal.SetMaximalConsistent` (no fc arg) |
| (b) connective spelling | prefix `Formula.untl/snce/and/or/neg`, `Formula.allFuture/someFuture/allPast/somePast` | notation `U`/`S`/`∧`/`¬`, `𝐆`/`𝐅`/`𝐇`/`𝐏` |
| (c) namespace + helper names | `...Bimodal.Metalogic.BXCanonical.Chronicle`; `theoremInMcsFc`, `SetMaximalConsistent.negation_complete/implication_property`, `set_consistent_not_both`, `liftBase fc` | `...Temporal.Metalogic.Chronicle`; `theoremInMcs`, `temporal_negation_complete/implication_property`, `mcs_not_mem_of_neg`, no `liftBase` |

A generic module abstracts (a) into a section variable / interface field (Temporal instantiates
with `.Base`), (b) into interface operator fields, and (c) into interface API fields (the
helper-rename table is absorbed by the interface's named fields).

## 5. Per-File Overlap and Factoring Verdict

### 5.1 ChronicleTypes (431 / 376) — PRIME TARGET, ~95% shared
Line-for-line identical modulo the three axes. Contents: DCS infrastructure
(`ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs`, `cud_*`, `dcs_*`), r-relations
(`rRelation`, `rRelationSince`, `r3Relation`, `r3RelationSince`), r-maximality, Burgess
content-based relations (`burgessR*`, `BurgessR3Maximal`), the `Chronicle` structure, conditions
`c0`-`c5'`, `ValidChronicle`, C3 consequences, `ChronicleInvariant`, and basic
subset/intersection theorems. All are generic `def`s/`theorem`s over the interface. Bimodal has a
few extra dcs-intersection lemmas (`dcs_inter_*`, `three_way_inter_consistent`) not in temporal —
these lift generically and simply go unused by temporal, or move to the shared core.

### 5.2 ChronicleConstruction (1532 / 1435) — ~92-93% shared, 59 decls 1:1
Same section skeleton (singleton chronicle → counterexample enumeration → omega-chain → limit
chronicle → C0-C5 satisfaction → forward_G/backward_H → `chronicle_model_exists` → strong C5).
59 top-level declarations shared 1:1 in the same order, proof bodies identical modulo the axes +
helper-rename table. **Zero sorries in both.** Genuine divergence: exactly **2 bimodal-only**
duality theorems, `g_content_sub_imp_h_content_sub` / `h_content_sub_imp_g_content_sub` (~100
lines, rely on BX4/BX4' connect_future/connect_past). These stay in the bimodal layer (or are
added to temporal only if the same axioms are available there). No temporal-only declarations.

### 5.3 CounterexampleElimination — ~95%+ shared, repackaged differently
Same declaration set, different file partition. Bimodal's monolithic 3049-line `Interface.lean`
(Kind + result structures + `c5ForwardWalk`/`c5BackwardWalk` + `eliminatePotentialCounterexample`)
is split in temporal into `Elimination.lean` (structs) + `RecursiveWalks.lean` (walks) +
`MainElimination.lean` (driver); bimodal's `BurgessHelpers.lean` is inlined into temporal's
`Structures.lean`. Big defs match tightly by line count (`c5ForwardWalk` ~540 both;
`c5BackwardWalk` ~560/545; `eliminatePotentialCounterexample` ~1677/1642) — axis-only divergence.
`eliminateC5Counterexample` verified as a line-for-line near-duplicate modulo the axes. Genuine
divergence: **2 bimodal-only** eliminators `eliminateGPropCounterexample` /
`eliminateHPropCounterexample` (~80 lines). This is the largest single dedup win (~5000 lines
across the two trees collapse to one generic pipeline). The generic module must pick ONE file
layout (temporal's 3-way split is the cleaner target).

### 5.4 RRelation (1694 / 746) — partial factoring, shared core ~38 lemmas
Temporal is essentially a **strict subset** of bimodal modulo the axes. ~38 shared core lemmas
(deductive-closure infra, r-relation/r3 maximal-extension existence via Zorn, `burgess*_absorption`,
`untl/snce_left_mono*`, seed→BurgessR3Maximal, the `someFuture/somePast` absurdity lemmas,
`burgessR_implies_burgessRSince` pair) factor cleanly. Bimodal carries ~24 extra lemmas with no
temporal analogue in three families: (1) Since-mirrored maximal-extension variants
(`rMaximalSince_extension_exists`, `r3MaximalSince_extension_exists`); (2) a `BurgessR3Maximal`
projection/accessor suite; (3) conjunction-guard machinery (`untl/snce_conj_guard`,
`burgessR_conj`, etc.) plus the `c4/c4'` hard-case lemmas. These stay bimodal-specific (or become
optional generic add-ons). Two small reconciliations: temporal factors a Zorn helper
`chain_finite_subset_in_element` worth hoisting into the generic core, and temporal has a
`deductiveClosure_singleton_imp'` primed variant bimodal lacks.

### 5.5 PointInsertion — already ported; Since-seed already factored
Both trees have their own `PointInsertion/` (Seeds/Burgess/Since + XuGuard[bimodal]/Splitting[temporal]).
These are parallel ports (temporal's header says "Ported from" bimodal). The Since-direction seed
consistency is already lifted via `SinceSeedInterface`. Further point-insertion consolidation is
possible but is a larger, separate effort; recommend it as out-of-scope follow-up unless the plan
explicitly includes it.

### 5.6 ChronicleToCountermodel — GENUINELY DIVERGENT, DO NOT CONSOLIDATE
Bimodal's (233 lines) contains the gap-elimination + discrete countermodel pipeline
(`chronicle_gap_contradiction`, succ-embedding, BFMCS on ℤ) — the only real proof sorries in the
tree, every one blocked on `WeakCanonical.IntegerModel.GoodStructuresModelSurgery` (external port).
Temporal's (137 lines) is sorry-free and much smaller (dense pipeline only). Different content,
different endpoints. Leave both logic-specific and untouched. Same for temporal-only
`TruthLemma`, `Frame`, `CanonicalChain`, `OrderedSeedConsistency` (temporal model-building glue).

## 6. Landed Results to Preserve (zero-debt)

- Temporal completeness endpoint `completeness_dense` (`Logics/Temporal/Metalogic/DenseCompleteness.lean:252`),
  sorry-free — must remain provable and sorry-free after every phase.
- Entire temporal Chronicle tree is sorry-free — must stay that way.
- All 59 shared `ChronicleConstruction` results and the CEE pipeline results are sorry-free in
  both trees — the generic versions must be sorry-free with each logic's instance.
- Bimodal's `ChronicleToCountermodel` sorries are pre-existing and out of scope — they must be
  neither removed nor multiplied; the file is not part of the consolidation.

## 7. Recommended Consolidation Strategy

Extend the `SinceSeedInterface` pattern. Two viable interface shapes; recommend a **layered
design**:

- Add a broader `ChronicleInterface F` (namespace `Cslib.Logic.Metalogic.Chronicle`) bundling
  the formula operators, the `Type*`-valued derivation family (reuse/parallel `HilbertTree`),
  the `SetConsistent`/`SetMaximalConsistent` predicates, and the MCS/Burgess apparatus lemmas as
  statement fields. Keep `SetDeductivelyClosed`, `rRelation`, `burgessR*`, `Chronicle`,
  conditions, etc. as generic `def`s over an interface value (mirroring how
  `SinceSeedConsistency` already treats the definitional notions).
- To minimize churn in landed code, **do not disturb `SinceSeedConsistency.lean` initially**;
  build the new interface to subsume its needs and reconcile (have Since reuse the broader
  interface) only in a final cleanup phase if warranted. Note the field overlap for the planner.
- Each logic supplies its instance: Bimodal an instance **family** `fun fc => …`; Temporal a
  single `.Base` instance. Both re-export the generic declarations under their existing
  namespaces (via `export`/abbrev aliases) so downstream files are minimally perturbed.

### Suggested phasing (each phase = one green `lake build`, one commit)
- **Phase 0**: Design + land `ChronicleInterface F` signature/skeleton in Foundations, defeq to
  both logics' primitives. Wire nothing yet. (Skeleton-only; verify it compiles.)
- **Phase 1**: Lift `ChronicleTypes` → generic `Foundations/.../Chronicle/Types.lean`. Instantiate
  in both trees; replace their `ChronicleTypes.lean` bodies with instance + re-export. Lowest risk.
- **Phase 2**: Lift the `RRelation` shared core (~38 lemmas, + hoist `chain_finite_subset_in_element`).
  Keep bimodal's ~24 extras + temporal's `_imp'` local.
- **Phase 3**: Lift the `CounterexampleElimination` pipeline (Structures + BurgessHelpers + walks +
  driver) as generic modules using temporal's 3-way split. Keep bimodal's 2 GProp/HProp eliminators local.
- **Phase 4**: Lift `ChronicleConstruction` (59 shared decls). Keep the 2 bimodal duality theorems local.
- **Phase 5 (cleanup)**: Fix the stale `RRelation.lean:40` sorry comment; update barrels; optionally
  reconcile `SinceSeedInterface` under the broader interface; optionally lift `OrderedSeedConsistency`
  (Until analog of the Since-seed extraction). Optional/low-priority.

Phases 3 and 4 are large; the planner should size them into agent-runnable sub-phases (the
temporal file split already suggests natural sub-units: Structures, RecursiveWalks, MainElimination).

## 8. Constraints & Risks

- **Zero-debt / no-proof-change**: this is a structural move. No new sorries, no new axioms.
  Every generic lemma must be discharged by porting the existing (already-green) proof body with
  the axes abstracted. If a proof body resists generic abstraction, keep that lemma logic-local
  rather than introducing a sorry — do not defer.
- **Do not entangle** the bimodal discrete-completeness sorries: `ChronicleToCountermodel.lean`
  is out of scope and must not be imported into or merged with any generic module.
- **fc as instance-family vs single instance** is the central design subtlety — already solved by
  the `structure`-not-`class` precedent; follow it.
- **Downstream re-export fidelity**: many files across both trees reference these declarations by
  their current names/namespaces. Use `export`/aliases so the generic move is transparent; verify
  with a full `lake build` at each phase.
- **Build cost**: `RRelation`/`Interface` are heavy; expect long builds. Budget accordingly.
- **Interface reconciliation churn**: touching landed `SinceSeedConsistency` risks re-verifying
  the already-green Since path — defer to the optional final phase.

## 9. Tactic Survey

Not applicable in the usual sense — this task is structural code movement, not new proof search.
The proofs already exist and are green in each tree; the work is abstracting them over an
interface, not discovering tactics. The only "tactic" concern is that some proofs use
`set_consistent_not_both` (bimodal) vs `mcs_not_mem_of_neg` (temporal) as equivalent final steps;
the interface should expose whichever primitive both can supply, or expose both as fields.

## 10. Key File References (absolute)

- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` (precedent interface)
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (HilbertTree precedent)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/` (+ subfiles)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/` (+ subfiles)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean` (OUT OF SCOPE — sorries)
- `/home/benjamin/Projects/cslib/Cslib.lean` (barrel, line 88 for Foundations Chronicle imports)
