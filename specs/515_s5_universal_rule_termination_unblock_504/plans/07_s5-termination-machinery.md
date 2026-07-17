# Implementation Plan: S5 Witness-Reuse Rule + Linear World Budget + Euclidean 5/KB5 Route (v6)

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [IMPLEMENTING]
- **Effort**: 60 hours (25 phases: 27h S5 chain [Phases 0-14] + 33h Euclidean 5/KB5 chain [Phases 15-23, with Phase 19 now split into **19a + 19b**]; the figure is the exact sum of the per-phase timings and is deliberately pessimistic -- see "Budget realism" below). **v6 grows the total honestly (+8h over v5's 52h).** The *second* Phase 19 soundness blocker -- the **mint-arm witness-reuse gap** (handoff 10), distinct from and discovered after the Route-1 propagation gap v5 already resolved -- is resolved by **Route (a)** (`reports/08_*`): a root-aware mint-arm guard **plus a re-derivation of the landed tag-injection termination chain** under a refined "≤1 mint per tag per source-class {root, non-root}" invariant. That re-derivation is **Phase-6/7-scale work on landed green assets**, NOT the bounded local patch v5's Route-1 sizing assumed, so the single 3h Phase 19 splits into **Phase 19a** (guarded mint arm + termination bound re-derivation, 6h, its own dispatch(es), KILL budget) + **Phase 19b** (`modalTableauFive_sound` bespoke assembly, 5h). The world bound stays **linear** (≈ `2·|modalSubfmls φ₀|` -- a larger constant, not a worse asymptotic); decidability is unaffected.
- **Dependencies**: Task 514 (literature grounding); Task 504 (parent; `modalApplyOneS5`, `extractModelS5*`, `modalTruthLemmaS5` landed CI-green). Task 511 (S4 keyed-guard sibling) is **decoupled by this revision** -- see Goals & Non-Goals.
- **Research Inputs**:
  - reports/03_s5-infrastructure-deep-research.md (**the authority for the S5 architecture**; 29-agent deep research, mechanized against the repo; integrated in v3, unchanged here)
  - probes/five-s5-separation.lean (**new in v4**; machine-verified, sorry-free, **zero axioms**; settles the 5/KB5 route question by proof -- see Research Integration finding 4)
  - reports/08_mint-arm-reuse-route-decision.md (**new in v6; the authority for the Phase 19 mint-arm remediation**. Verdict: adopt **Route (a)** -- a root-aware mint-arm guard (exclude root `0` as a reuse witness; root-triggered mint arms mint FRESH) plus a from-scratch re-derivation of the tag-injection termination bound under a source-split "≤1 mint per tag per {root, non-root}" invariant. **Route (b) (Euclidean-closure / model-repair) is PROVABLY DEAD**: (1) the soundness model already satisfies `fiveFC` so `EuclGen m.r = m.r` (closure vacuous, adds no reuse edge), and (2) "add-pair-then-close" falsifies box formulas by anti-monotonicity, so the "closure preserves satisfaction" lemma it would need is FALSE. Fallback 4 (S5-only) is a last resort NOT warranted on soundness grounds -- Route (a) is sound and stays linear. **Route (a) does not fit a single dispatch**; this run's terminus is a real partial.)
  - reports/07_phase19-soundness-blocker-remediation.md (**new in v5**; the authority for the Phase 19 **propagation-arm** remediation. Verdict: adopt **Route (1)**, root/non-root asymmetric propagation. Root cause: `fiveFC := RightEuclidean r` has no reflexivity conjunct, so `reachable_imp_related_s5`'s `hFC.1.refl` base case does not port; machine-checked `Fin 3` counterexample confirms uniform trigger-independent propagation is unsound when triggered from the root. Reuses the landed Phase 17 cod-equivalence lemmas. **Scope note: Route 1 resolved the PROPAGATION arms only** -- it explicitly left the mint arms untouched, which is exactly the gap `reports/08_*` now closes.)
  - reports/01_s5-termination-implementation-blueprint.md (superseded on R7, D2-adjacent findings retained)
  - summaries/01_s5-termination-machinery-summary.md (v1 implementation record)
  - plans/06_s5-termination-machinery.md (v5; superseded by this file -- carried the Phase 19 mint-arm `[BLOCKED]` record now resolved here via Route (a))
  - plans/05_s5-termination-machinery.md (v4; superseded by v5 -- carried the Phase 19 propagation `[BLOCKED]` record resolved in v5 via Route 1)
  - plans/04_s5-termination-machinery.md (v3; superseded by v4)
- **Artifacts**: plans/07_s5-termination-machinery.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
  - .claude/rules/plan-format-enforcement.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Plan v2 pursued a keyed loop-checking termination chain (birth keys, pigeonhole, a 12-field
`S5LoopInv`) mirrored from S4, instantiated at a bespoke S5 universe. It landed Phases 1-7
sorry-free and CI-green and then blocked at Phase 8 on the Hintikka lift. Deep research
(`reports/03_s5-infrastructure-deep-research.md`) has since established that plan v2 is
**architecturally invalid, not merely over budget**: its two offered routes to close Phase 8 are a
**false statement** (R7 fuel domination) and a **cost sink** (a keyed driver that can consume
neither the measure engine nor the landed generic lift), and its measurement substrate
(`modalUniverseS5`/`modalWorldBoundS5`) **breaks the fuel arithmetic** it depends on.

This v3 replaces that architecture. **Bound MINTING, not re-firing.** Replace the two
world-*minting* arms of `modalApplyOneS5` (`T(◇φ)@w`, `F(□φ)@w`) with a guard-less witness-reuse
test: if any known world already carries `⟨s,φ,w'⟩`, add edge `w→w'` and emit `.linear [⟨s,φ,w'⟩]`;
mint fresh only when no witness exists on the branch. Leave the S5 universal-propagation arms
(`T(□φ)`, `F(◇φ)`) **completely untouched** -- they are already correct and already self-limiting.
Keep the generic driver **unmodified** and retarget the entire termination stack at K's **own**
`modalUniverse`/`modalWorldBound`/`modalFuel`, bounding worlds by a monotone tag-injection argument
(each mint permanently consumes a distinct `(sign, subformula)` tag) -- **linear**, not exponential.
Split `RuleApplicationSpec` so the Hintikka machinery no longer sees the three fields S5 cannot
discharge.

**Then deliver 5/KB5 by the route that can actually reach it.** The S5 tableau provably cannot
(Phases 15-23 exist because `probes/five-s5-separation.lean` *proves* it cannot, not because anyone
guessed). 5 and KB5 are reached instead by a **dedicated Euclidean route built on top of** the S5
cluster machinery: rooted Euclidean frames are exactly **root + universal cluster**, so the cluster
half is the S5 machinery this plan already builds, and the only genuinely new pieces are a
`Relation.EuclGen` closure operator and a root-aware rule.

**Definition of done**: `modalTableauS5` re-based on the witness rule; `modalTableauS5_sound` and
`modalTableauS5_complete` both sorry-free; `instDecidableS5Valid : Decidable (s5Valid φ)`; the R7
refutation landed as a theorem; **`modalTableauFive_sound`/`_complete` and
`modalTableauKb5_sound`/`_complete` sorry-free, with `instDecidableFiveValid : Decidable (fiveValid φ)`
and `instDecidableKb5Valid : Decidable (kb5Valid φ)`**; ~2,000 lines of superseded code **archived
out of the CI-built tree** (not deleted); the false docstrings corrected. Zero `sorry`, zero new
axioms, full CSLib CI at every milestone.

### Research Integration

Integrated in v3 and carried forward unchanged: **`reports/03_s5-infrastructure-deep-research.md`**
(56KB). Its §5 lemma-level build plan drives Phases 0-14 below; its §6 drives the archival
accounting; its §7 drives Risks & Mitigations; its §8 (Rejected Alternatives) is the standing
do-not-re-attempt record.

Newly integrated **this revision (v4)**: **`probes/five-s5-separation.lean`** -- a machine-verified,
sorry-free probe whose theorems depend on **no axioms at all** (not even `propext` /
`Classical.choice`). It **splits** v3's finding 4 into a confirmed half and a refuted half; see
finding 4 below. It changes no other finding, and it changes **nothing** about the S5 architecture.

Newly integrated **this revision (v5)**: **`reports/07_phase19-soundness-blocker-remediation.md`** --
the blocker-remediation research that resolves the **propagation-arm** Phase 19 `[BLOCKED]` record
carried by v4. **The decision is made and is NOT re-litigated here**: adopt **Route (1)**, root/non-root
asymmetric propagation. v5 baked that corrected design into Phases 19-23 and moved them from `[BLOCKED]`
to `[NOT STARTED]`. Finding 5 below records the substance; the diagnosis it resolves is **preserved**
(not deleted) in Phase 19's "Resolved blocker record". It changes **nothing** about the S5 architecture
(Phases 0-14) and **nothing** about Phases 15-18's landed assets. **Route 1 resolved the propagation
arms ONLY** -- the mint arms it explicitly left untouched carry the *second* gap that v6 now closes.

Newly integrated **this revision (v6)**: **`reports/08_mint-arm-reuse-route-decision.md`** and
**`handoffs/10_phase19-mint-arm-reuse-soundness-gap.md`** -- the diagnosis and route decision for the
*second, independent* Phase 19 soundness gap (the **mint-arm witness-reuse gap**), discovered while
building the `modalTableauFive_sound` fuel-induction assembly *after* Route 1 landed. **The decision is
made by adversarial research and is NOT re-litigated here**: adopt **Route (a)** -- a root-aware
mint-arm guard + termination-bound re-derivation. **Route (b) (Euclidean-closure / model-repair) is
PROVABLY DEAD** and is added to the Rejected Alternatives standing record (item 12). v6 does exactly
four things: (1) it **re-scopes the single Phase 19 into Phase 19a + Phase 19b**, because Route (a)'s
termination re-derivation is Phase-6/7-scale and genuinely two large pieces, not the bounded local
patch v5's Route-1 sizing assumed; (2) it updates Phase 18's post-hoc caveat and the Phase 19 records
to cite the mint-arm resolution (Route (a), `reports/08_*`), **preserving both blocker diagnoses**
(the Route-1 propagation gap AND the mint-arm gap) as resolved/decided records with their
countermodels, not deletions; (3) it grows the effort honestly (+8h) and updates the wave table for the
19→19a+19b split; (4) it reaffirms R9 -- the S5 chain (Phases 0-14) + Phase 18 + the Phase-19
soundness building blocks are green/committed and independent, so the current state is a **real partial
delivery**, and the 5/KB5 chain is `[BLOCKED -- Route (a) selected]` pending 19a/19b. Finding 6 below
records the substance. It changes **nothing** about the S5 architecture (Phases 0-14) and **nothing**
about the landed Route-1 propagation fix, `accReachableInv_related_five`, or the five building-block
lemmas landed across the last two dispatches (all still valid and reusable).

5. **Phase 19 soundness gap: root cause found, bounded fix adopted (Route 1).**
   `accReachableInv_related_s5` (`FrameSoundness.lean:1385`), via `reachable_imp_related_s5` (`:1378`),
   consumes frame **reflexivity** (`hFC.1.refl (f 0)`, the first conjunct of `s5FC`) in its induction
   base case. `fiveFC := Relation.RightEuclidean r` (`:1282`) has **no reflexivity conjunct**, so that
   discharge does not port -- and the missing fact is genuinely **false** at the frame level (committed
   `Fin 3` counterexample: `r = {(0,1),(1,1),(1,2),(2,1),(2,2)}` is `RightEuclidean` with `¬ r 0 2`).
   v4's Phase 18 propagation helpers (`modalFiveBoxAll`/`modalFiveDiaNegAll`) propagate uniformly over
   `modalKnownWorlds b \ {0}` **ignoring the trigger `_w`**, which is sound for `s5FC` (an equivalence
   relation) but unsound for `fiveFC` when the trigger is the root. **Route (1) closes the gap**:
   root-triggered propagation is restricted to `acc.successorsOf 0` (sound by the standard K
   realized-edge argument -- the discipline the base rule already uses at `Rules.lean:93`); non-root
   propagation stays universal across the cluster, sound via the **already-landed Phase 17** lemmas
   `Relation.rooted_cluster_isEquiv : IsEquiv (cod r) r` and `rooted_mem_cod` (reflexivity recovered on
   `cod r`, not on the frame). This **converges** with Phase 20's `EuclGen` structure (`EuclGen`'s
   `eucl` constructor only combines derivations sharing a first argument, so it relates the root only to
   its direct successors -- the same split), a strong cross-check that Route (1) is the right shape for
   both soundness and completeness, not a soundness-only patch. Fallback 4 (S5-only) is **not**
   warranted: the fix is bounded and does not cascade into termination or the K/T/B/S5 surface.

6. **Second Phase 19 soundness gap: mint-arm witness-reuse, Route (a) adopted (NOT bounded).** After
   Route 1 landed, building the `modalStepBranchFive_preserves_satIn` witness-reuse branch exposed a
   *second, independent* gap -- in the **mint arms** (`T(◇φ)@w`/`F(□φ)@w`), which Route 1 explicitly
   left untouched. `witnessWorldS5` (`S5Simplification.lean:521`) searches **all** known worlds (root
   included), unguarded, for a syntactic `⟨s,φ,w'⟩`; on a hit it adds edge `sf.label → w'`, and
   soundness then needs `m.r (f sf.label) (f w')`. S5 gets this free from `accReachableInv_related_s5`
   (any two known worlds are related under an equivalence). The Route-1 replacement
   `accReachableInv_related_five` requires **both** endpoints non-root, so it proves nothing when the
   trigger is the root (`sf.label = 0`) or the witness is the root (`w' = 0`) -- both realizable on
   ordinary branches (e.g. imp-decomposition puts a positive formula at world 0), both with concrete
   adversarial `RightEuclidean` countermodels (handoff 10). **DECISION -- Route (a)** (`reports/08_*`,
   adversarial research; do NOT re-litigate): (i) exclude root `0` as a reuse witness in the mint arms'
   use of `witnessWorldS5`; (ii) root-triggered mint arms mint **FRESH** (equivalently: reuse only
   under `acc.hasEdge 0 w'`). Soundness of the guard is the **same root asymmetry** Route 1 fixed for
   propagation. **This is NOT a local patch**: the landed tag-injection termination chain
   (`mintTags`/`usedTags`/`S5wTagInv`/`modalMaxWorld_lt_worldBound_of_S5w`, Phases 6/7, currently
   GREEN and committed) rests on "≤1 mint per `(sign,subformula)` tag"; the guard refines that to "≤1
   mint per tag **per source-class {root, non-root}**", so the whole chain must be **re-derived** under
   the refined invariant, giving a still-linear bound ≈ `2·|modalSubfmls φ₀|`. Excluding root-as-witness
   never forces a second mint of an already-minted tag, because a formula sitting *at the root* was
   never minted (root formulas arrive by decomposition, not via `witnessWorldS5`), so minting fresh for
   it is that tag's *first* mint in the root source-class. **Route (b) is PROVABLY DEAD** (item 12,
   Rejected Alternatives): (1) in the soundness direction `m` already satisfies `fiveFC`, so
   `EuclGen m.r = m.r` by `EuclGen.least` + `.mono` (closure vacuous, supplies no edge); (2) the only
   non-vacuous reading `EuclGen (m.r ∪ {(f w, f w')})` **falsifies box formulas** by anti-monotonicity
   (concrete killer in `reports/08_*` §Kill 2: a world carrying both `◇p` and `□q`, reuse edge to a
   `w'` with `w' ⊭ q`, makes `□q` false), so the "closure preserves satisfaction" lemma it needs is
   **false**. The five building-block lemmas landed across the last two dispatches
   (`modalApplyOneFiveProp_knownWorlds_step`, `modalApplyOneFive_agree_or_reuse`,
   `modalStepBranchFive_preserves_accReachableInv`, `FiveSoundInv`,
   `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`) are **structural/propagation** facts, all
   **still valid and reusable** -- the mint-arm guard does not invalidate them. **Honest scope**: Route
   (a) does **not** fit one more implementation dispatch (`reports/08_*` critical scoping fact); the
   termination re-derivation is its own phase (**19a**) and `modalTableauFive_sound` assembly is
   another (**19b**), with Phases 20-23 on top. This orchestration run ends in a **real partial**
   regardless -- exactly what R9 anticipates.

Four findings invalidate plan v2. **Each was independently re-verified against this repo by the
orchestrator before this plan was written** -- they are not taken on the research agent's word:

1. **R7 (fuel domination) is REFUTED BY EXECUTION, not merely unproven.**
   `modalExpandBranchesGen modalApplyOneS5` on `[T(□◇p)@0]` yields `maxWorld` = 5/10/20/40 at fuel
   10/20/40/80 -- exactly `fuel/2`, no fixpoint. The unguarded S5 expansion is **unbounded** on a
   formula with a **one-world** S5 model. Plan v2's Phase 8 offered exactly two routes to close the
   Hintikka lift; this one is a **false statement**. It is therefore landed as a **theorem** in
   Phase 3, beside `modalApplyOneS5_rankStep_not_dischargeable`, so no future dispatch re-attempts it.
2. **`modalUniverseS5`/`modalWorldBoundS5` BREAK the fuel arithmetic and must leave the tree**
   (archived, Phase 14 -- moved, not destroyed).
   `modalFuel` does not dominate the entry measure at `modalUniverseS5`: it fails at `atom` (19 > 8),
   `□p` (135 > 120), `p ∧ q` (779 > 120). The advertised escape hatch
   `modalWorldBoundS5 φ ≤ modalWorldBound φ` is **false** (`atom` 4 vs 1; `□p` 16 vs 9); it holds
   only at `□◇p` -- the single formula the prior dossier was built on. `modalFuel` is calibrated
   *razor-thin* against K's own universe (margin of exactly **1** at `atom p` and `p ∧ q`), so the
   looseness sits **in the exponent**. The whole termination stack retargets at K's own universe,
   where `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:208`) applies **verbatim**.
3. **No φ₀-parametrized rule can ever work.** `modalExpMeasure_step_lt_gen`'s
   `hOutputsSubsetUniverse` (`FmpMeasure.lean:3241`) binds `φ0` **universally inside the hypothesis**
   (verified by reading the signature). This kills static pre-allocation outright, and kills the
   `modalApplyOneS5a φ₀` / `modalApplyOneS5g phi0` shapes. The witness rule is plain
   `RuleApply Atom` and discharges the field uniformly. *(This also explains why the landed
   `modalApplyOneS5g phi0` precedent never reached the measure layer.)*
4. **5/KB5 is NOT deliverable by any S5 tableau -- PROVEN. But it IS deliverable, by another route.**
   `probes/five-s5-separation.lean` settles both halves of this by machine proof. **The probe did not
   vindicate v3 wholesale: it confirmed v3's narrow claim and refuted v3's broader one.** Read both
   halves before acting on either.

   **CONFIRMED (v3 was right).** `fiveValid_ssubset_s5Valid` and `kb5Valid_ssubset_s5Valid` are both
   proven, sorry-free and axiom-free. `s5FC = Std.Refl r ∧ Relation.RightEuclidean r`
   (`FrameSoundness.lean:1273`) but `fiveFC = Relation.RightEuclidean r` **alone** (**:1282** -- v3
   miscited this as :1283; the probe found the drift) and
   `kb5FC = Std.Symm r ∧ Relation.RightEuclidean r` (:1291) -- **strictly larger** frame classes. The
   separating formula is `□p → p` on the **one-world EMPTY frame**: `RightEuclidean` and `Std.Symm`
   are both **vacuous** when there are no edges, so `□p` holds vacuously (`box_atom_holds`) while `p`
   is false (`atom_fails`); reflexivity is exactly what `fiveFC`/`kb5FC` drop and exactly what
   `boxImp_s5Valid` consumes. So `fiveValid ⊊ s5Valid`, and an `s5Valid` decision procedure
   genuinely **cannot** decide `fiveValid` -- the S5 tableau's closure sits on the wrong side of a
   strict inclusion. This is a fact about the frame classes, not about any tableau engineering.

   **REFUTED (v3 was wrong).** v3 escalated that narrow result into *"mathematically impossible …
   This plan cannot deliver it and no successor plan can either"*, and called the absent Mathlib
   Euclidean-closure operator *"a real mathematical obstruction"*. **That is missing library
   infrastructure, not a mathematical obstruction.** The probe's own scope note says so explicitly:
   *"It does NOT establish that 5/KB5 completeness is unreachable in principle -- K5 and KB5 are
   well-known to be complete and decidable via a Euclidean-frame tableau."* Four independent
   grounds, all checkable:
   - **(a) The closure exists.** Euclideanness is closed under **arbitrary intersection**: if `R1`,
     `R2` are Euclidean and `R = R1 ∩ R2`, then `R a b` and `R a c` give `R1 b c` and `R2 b c`,
     hence `R b c`. The full relation is Euclidean, so the intersection is over a non-empty family.
     Therefore the **least Euclidean relation containing a given one exists**, and is definable as an
     inductive closure -- exactly as `Relation.SymmGen`/`Relation.EqvGen`
     (`Cslib/Foundations/Relation/Confluence.lean`) already are in this repo. Phase 16 builds it.
   - **(b) Rooted Euclidean frames are exactly "root + universal cluster"**, immediate from the
     definition: `R w a → R w b → R a b` says `R(w) × R(w) ⊆ R`. **This repo already mechanizes it**:
     `Relation.RightEuclidean.equiv_cod : IsEquiv (cod r) r` (`Euclidean.lean:124`), with
     `rightTotal_cod` (:121), `cod_subset_dom` (:113) and `refl_cod` (:45). A K5 countermodel is a
     root plus an S5-like universal cluster -- which is why K5 sits **adjacent** to S5, not beyond
     it, and why **the S5 cluster machinery this plan already builds is most of the work**.
   - **(c) K5 and KB5 have the finite model property and are decidable** -- textbook
     (Blackburn/de Rijke/Venema; Chagrov/Zakharyaschev).
   - **(d) The repo's own note says COST, not impossibility.** `FrameCompleteness.lean:583-585` says
     5/KB5 is *"OUT OF SCOPE … would need a bespoke construction"*. v3 escalated that cost into
     impossibility, then used the impossibility to justify dropping a stated deliverable.

   **Consequence: 5/KB5 is RE-SCOPED, NOT STRUCK.** See "Route correction" below. The task
   description **stands unchanged**; no amendment is needed or requested.

**The re-firing "crux" does not exist.** `.persistent` returns `[expanded]` **unchanged**
(`Saturation.lean:141`), so boxes are never retired and re-fire automatically; `Saturation.lean:39`
states this as design intent. Re-firing is the divergence **engine** of the shipped rule *and* the
mechanism that makes the fix complete: `modalS5BoxAll` filters formulas already on `b` and returns
`.notApplicable` when `allNew.isEmpty`, so **applicable ⟺ some known world lacks the formula** --
bound the world set and the box saturates **by itself**. No stratification, no firing-order
discipline, no fairness. The report proves these impossible (§8 item 2): the strata do not
stratify, because *firing boxes creates world-creating formulas*. Any phase proposing them solves a
non-problem.

Empirical validation of the recommended rule, executed against the **real** driver: an exhaustive
**3,963-formula** corpus (depth 2 over `{p,q,⊥}` under `□,◇,→,∧,∨`) differentially against an exact
S5 oracle -- **0 mismatches, 0 fuel-instability, 0 world-bound violations** (1,057 valid /
2,906 invalid, non-vacuous). `□◇p` saturates at **2 worlds**, stable across fuel 20→2000.

### Prior Plan Reference

This v6 supersedes `plans/06_s5-termination-machinery.md` (v5), which superseded
`plans/05_s5-termination-machinery.md` (v4), which superseded
`plans/04_s5-termination-machinery.md` (v3), which superseded
`plans/02_s5-termination-machinery.md`, which superseded `plans/01_*.md`.

**The v5 → v6 delta is a targeted, non-destructive re-scoping of Phase 19 driven by a SECOND
soundness blocker.** v5 landed Phases 0-18 plus the Route-1 propagation fix and the Phase-19
soundness building blocks (`accReachableInv_related_five` + five structural/propagation lemmas), all
green and committed. Continuing into the `modalTableauFive_sound` fuel-induction assembly then exposed
a *second, independent* soundness gap -- the **mint-arm witness-reuse gap** (handoff 10) -- which
Route 1 explicitly did not touch. **v6 changes nothing v5 landed.** Phases 0-18 remain `[COMPLETED]`;
the Route-1 fix, `accReachableInv_related_five`, and the five building-block lemmas remain green and
are **not** demoted or discarded. v6 does exactly four things: (1) it adopts the Route (a) decision
from `reports/08_*` (root-aware mint-arm guard + termination re-derivation) and **re-scopes the single
Phase 19 into Phase 19a + Phase 19b**, because Route (a) is Phase-6/7-scale, not the bounded local
patch v5's sizing assumed; (2) it updates Phase 18's post-hoc caveat and the Phase 19 records to cite
the mint-arm resolution, **preserving BOTH blocker diagnoses** (Route-1 propagation gap AND mint-arm
gap) as resolved/decided records with their countermodels; (3) it records Route (b)
(Euclidean-closure / model-repair) as **PROVABLY DEAD** in the Rejected Alternatives standing record
(item 12); (4) it grows the effort honestly (52h→60h, +8h) and updates the wave table. **R9 is
reaffirmed, not weakened**: the S5 chain (Phases 0-14) + Phase 18 + the Phase-19 soundness building
blocks are green/committed and independent of the remaining Euclidean chain -- the current state is a
**real partial delivery, not a failure**; the 5/KB5 chain (Phase-19 capstone through 23) is
`[BLOCKED -- Route (a) selected, see report 08]` pending 19a/19b, and 5/KB5 is **never re-struck**.

**The v4 → v5 delta is a single, targeted, non-destructive change.** v4 landed Phases 0-18 and then
recorded a `[BLOCKED]` on Phase 19: a computer-verified soundness gap in the Phase 18 propagation
design for pure Euclidean (`fiveFC`) frames. **v5 changes nothing v4 landed.** Phases 0-18 remain
`[COMPLETED]`; their committed Lean assets are untouched. v5 does exactly three things: (1) it adopts
the blocker-remediation decision from `reports/07_*` -- **Route (1)**, root/non-root asymmetric
propagation -- and bakes the corrected design into Phases 19-23, which move from `[BLOCKED]` to
`[NOT STARTED]`; (2) it updates Phase 18's post-hoc caveat and Phase 19's record to reference the
**resolution** (Route 1) rather than only the diagnosis, **preserving the diagnosis** for provenance;
(3) it folds the bounded helper revision (add an `acc` parameter + a `hasEdge 0 w'` root-arm guard to
`modalFiveBoxAll`/`modalFiveDiaNegAll`; thread `acc` through `modalApplyOneFiveProp`; re-verify
`modalApplyOneFive_specCore`) into the head of Phase 19, where the soundness proof consumes it. The
R9 partial-delivery posture is unchanged and reaffirmed: the S5 chain (Phases 0-14) is landed, green,
and independent; a later stall in the Euclidean chain remains a **real partial delivery, not a
failure** (Fallback 4), and 5/KB5 is **never re-struck**.
**No phase of v2 is carried forward as `[COMPLETED]`.** v2's Phases 1-7 landed CI-green and are
committed, but v3 re-architects beneath them: most of that work is **archived** in Phase 14 (see
"Preserved-Assets Accounting"). This is intentional and is the honest sticker price of the
recommendation. v2's *findings* survive in full: `modalApplyOneS5_rankStep_not_dischargeable`
(the rank route is dead) is **kept** as landed documentation, and v2's "recommended next dispatch
item 1" (the `accTargetsKnown` top-loop generalization) survives verbatim as Phase 5.

**The v3 → v4 delta is narrow and targeted. v3's architecture is SOUND and is carried forward
substantially verbatim.** Do not re-litigate or re-derive the witness-reuse rule `modalApplyOneS5w`,
the linear tag-injection world budget, retargeting at K's own universe, the `RuleApplicationSpec`
split, `hintikka_congr`, the R7 refutation-as-theorem, the Phase 0 kill test, the Phase 8
scratch-probe gate, the Phase 12b regression gate, or the phase DAG for Phases 0-14. Exactly three
things changed:

1. **5/KB5 is re-scoped, not struck** (Phases 15-23 are new; the Non-Goal became a Goal; the
   "ACTION REQUIRED FROM THE USER" task-description-amendment demand is **deleted**). Driven by
   `probes/five-s5-separation.lean`, which confirmed v3's narrow claim and **refuted** its broader
   one (finding 4). **User decision, explicit and binding**: *"write the mathematically correct
   solution, no matter the cost"* -- the user was offered the strike and **refused** it.
2. **Phase 14 is ARCHIVAL, not demolition.** **User decision, explicit and binding**: *"Code should
   be archived not deleted."* The ~2,000 superseded lines are **moved**, not destroyed.
3. **Effort doubles, honestly**: 25h/15 phases -> 52h/24 phases. See "Budget realism".

Everything else is v3 verbatim.

### Budget realism

Plan v2 budgeted its Phase 8 at **3 hours**; it proved to be several phases and ultimately
`[BLOCKED]`. This plan does not repeat that error. Every phase below is sized to **one agent run**
(~100-500 lines of output) and the aggregate is deliberately pessimistic. Where the report supplies
concrete Lean declarations they are named inline; where a phase is a port of an existing proof its
source `file:line` and line count are given. Phase 12 (the ~310-line double induction) carries an
explicit authorization to split across two dispatches rather than being compressed.

The research report recommends **13** phases (0-12). This plan has **25** (0-23, with Phase 19 split
into 19a+19b). The deviations, all justified above: (a) Phase 3 lands the R7 refutation as a theorem
plus the docstring/scope corrections (report §6 "Add a sibling" + §7 scope corrections, unphased
there); (b) Phase 8 is an explicit scratch-probe **gate** for R1 (report R1: "Probe it in scratch
BEFORE committing to Phase 6+"); (c) the report's Phase 10 (`accTargetsKnown`) is promoted to Phase
5, early and off the critical path, because **every route needs it**; (d) **Phases 15-23 are the
Euclidean 5/KB5 route**, which the report did not phase because v3 had written the deliverable off;
(e) **Phase 19 is split into 19a + 19b (v6)** because Route (a)'s mint-arm remediation is genuinely
two large pieces -- a Phase-6/7-scale termination re-derivation and a bespoke soundness assembly.

**On the doubling (v4).** The S5 chain (Phases 0-14) is **27 hours**: v3's own per-phase timings
summed to **26h**, not the **25h** its metadata claimed (v3 carried a 1h arithmetic drift -- checked
and corrected here), plus **1h added to Phase 14**, because archival with per-block provenance
headers and a `shake` re-run genuinely costs more than `rm` did. Inheriting v3's figure for changed
work would be exactly the kind of convenient arithmetic this section exists to prevent. The Euclidean
chain (Phases 15-23) adds **25 hours**, for **52 hours** total -- **the exact sum of the 24 per-phase
timings**, checked, not estimated. That is a **doubling, and it is stated plainly rather than
shaved to look palatable.** The user's instruction is *"write the
mathematically correct solution, no matter the cost"* -- which licenses a **large** number, not an
optimistic one. Under-budgeting a capstone is exactly the error plan v2 made at its Phase 8 (3
hours budgeted; `[BLOCKED]` delivered), and this plan does not repeat it at a **second** capstone
merely because the first one is now correctly sized. Each of the nine new phases is sized to **one
agent run** (~100-500 lines) per the same rule applied to Phases 0-14, and Phase 15 is a **cheap
scratch gate** that fails before the expensive work it guards. The honest downside case is recorded
in R10 and in Fallback 4: if the Euclidean chain stalls, **it stalls after the S5 chain is green,
landed, and independently valuable** -- the doubling buys an additive deliverable, and never puts
the S5 deliverable at risk.

**On the v6 re-scope (52h → 60h, +8h).** The single 3h Phase 19 splits into **19a (6h)** and **19b
(5h)** -- an honest +8h. This is the *same* under-budgeting error, caught before it repeats: v5 sized
the mint-arm fix at "bounded, fits Phase 19's 3h/400-line budget" on the assumption that Route 1's
propagation pattern would port cheaply to the mint arms. It does not. `reports/08_*`'s critical
scoping fact is explicit -- Route (a) requires re-deriving the landed tag-injection termination chain
(`mintTags`/`usedTags`/`S5wTagInv`/`modalMaxWorld_lt_worldBound_of_S5w`, Phases 6/7, ~5h of the
original S5 chain) under a source-split invariant, on **already-committed green assets**, as sorry-free
sub-milestones each re-verified CI-green with a KILL budget. That is Phase-6/7-scale (Phase 6 = 1.5h,
Phase 7 = 2h), hence **19a = 6h and does NOT fit a single dispatch**. 19b is the bespoke
`modalTableauFive_sound` fuel-induction assembly (~800-1100 new lines per handoff 09, mirroring the
S5 bespoke chain `S5SoundInv`…`modalTableauS5_sound` ≈ 860 lines / Phase 13's 3h) -- sized at **5h**.
The world bound stays **linear** (≈ `2·|modalSubfmls φ₀|`, a larger constant only); this is a cost
number, not an asymptotic regression. Stating +8h plainly rather than shaving it is the whole point
of this section -- and per R9 the re-scope changes nothing about the partial-delivery posture: 19a/19b
sit on top of a green, committed, independent S5 deliverable.

## Route correction (READ THIS FIRST -- does NOT contradict the task description)

**5/KB5 is unreachable *by the S5 tableau route* (proven). It is therefore reached by a dedicated
Euclidean route built ON TOP OF the S5 cluster machinery. The deliverable stands; only the route
changes.**

This section replaces v3's "Scope correction", which recommended **striking** the task description's
5/KB5 deliverable. **The user was offered that strike and explicitly refused it**, directing:
*"write the mathematically correct solution, no matter the cost."* The task description
**stands unchanged**. No amendment is requested, and none is needed -- the deliverable was never
impossible, only misrouted.

### What is proven unreachable: the S5 tableau route

The task description's stated deliverable -- *"5/KB5 validity + completeness via `Satisfies.five`
(Basic.lean) and `Cslib/Foundations/Relation/Euclidean.lean` RightEuclidean API (Phase 7
completion)"* -- **cannot be delivered by any S5 tableau**, and plan v2's Phase 9 was therefore
pursuing it down a road that provably does not arrive. Now **proven**, not argued, by
`probes/five-s5-separation.lean` (sorry-free, **zero axioms**):

| Frame class | Definition | file:line |
|---|---|---|
| `s5FC` | `Std.Refl r ∧ Relation.RightEuclidean r` | :1273 |
| `fiveFC` | `Relation.RightEuclidean r` (**reflexivity absent**) | **:1282** |
| `kb5FC` | `Std.Symm r ∧ Relation.RightEuclidean r` (**reflexivity absent**) | :1291 |

`fiveFC` and `kb5FC` are **strictly larger** frame classes than `s5FC`. The probe's
`fiveValid_ssubset_s5Valid` and `kb5Valid_ssubset_s5Valid` establish `fiveValid ⊊ s5Valid` and
`kb5Valid ⊊ s5Valid`, witnessed by `□p → p` on the one-world **empty** frame (both `RightEuclidean`
and `Std.Symm` are vacuous with no edges). So a sound+complete decision procedure for `s5Valid`
**does not compose into one for `fiveValid`**. This is a property of the *mathematics*, not of any
tableau engineering -- and it is now a citable proof rather than prose.

### What is NOT unreachable: 5/KB5 itself

The strict inclusion kills **one route**. It says nothing about the deliverable. K5 and KB5 have the
finite model property and are decidable; the closure operator exists (Euclideanness is closed under
arbitrary intersection); and **rooted Euclidean frames are exactly root + universal cluster**, a
fact this repo has already mechanized as `Relation.RightEuclidean.equiv_cod` (`Euclidean.lean:124`).
See Research Integration finding 4 (a)-(d) for the full argument. **K5 is adjacent to S5, not beyond
it**: the cluster half of a K5 countermodel *is* the S5 machinery Phases 0-14 build. That is why
these phases **consume** the S5 chain rather than duplicating it, and why they sit at the **end** of
the DAG.

**In-scope consequence (Phase 3)**: `FrameCompleteness.lean:571-580` currently frames the gap as a
mere **scheduling** dependency -- *"Such a completeness/decidability result needs
`modalTableauS5_complete` (Phase 4) and `modalTableauS5_sound` (Phase 5) as its proof engine, and
both are transitively blocked by Phase 2"*. **That docstring is wrong on the mathematics** and
appears to have misled the last planner into plan v2's Phase 9. Correcting it to state the
frame-class inclusion obstruction -- **citing the probe's theorem names** -- is an **in-scope task
of this plan** (Phase 3), so it does not mislead the next one. Phase 3 corrects it to say *"not via
this route; see Phases 15-23 for the route that reaches it"* -- **not** *"impossible"*.

The genuinely independent fragment that *is* landed and CI-green from task 504 --
`extractModelS5_rightEuclidean` (`RightEuclidean (extractModelS5 b acc).r` holds unconditionally,
since every equivalence relation is right-Euclidean) -- stays landed and untouched.

**Retained from v3, correctly, but re-labelled**: pure-K5 / pure-5 needs a **bespoke construction**
(no Mathlib "Euclidean closure" operator analogous to `Relation.EqvGen` exists). v3 recorded this as
an *impossibility*. It is a **cost input** to Phases 15-23 -- the bespoke construction is
`Relation.EuclGen`, and Phase 16 builds it. `FrameCompleteness.lean:583-585` and
`S5Simplification.lean:3018-3037` both say **"OUT OF SCOPE … would need a bespoke construction"**,
i.e. **cost**; neither says *impossible*. Phase 23 reconciles both docstrings.

**Second, smaller correction**: *"against `Cube.S5`"* is a docstring gesture, not a theorem. No Lean
theorem connects `s5Valid` to `Cube.S5` -- and none connects `kValid` to `Cube.K` either, so this is
precedent-consistent rather than an S5 regression. The real deliverable is `Decidable (s5Valid φ)`.

## Goals & Non-Goals

**Goals**:
- Land the guard-less witness-reuse rule `modalApplyOneS5w : RuleApply Atom` (plain, **not**
  φ₀-parametrized) intercepting exactly the two minting shapes; leave the universal-propagation arms
  untouched.
- Land `hintikka_congr` early -- it ports the entire landed countermodel half of S5 completeness
  with **zero edits** to `FrameCompleteness.lean`.
- Land the linear a-priori world budget: `modalOps_lt_worldBound` + the `usedTags` monotone-injection
  counting crux, replacing the birth-key pigeonhole. Retarget at K's own
  `modalUniverse`/`modalWorldBound`/`modalFuel`, reused **verbatim**.
- Split `RuleApplicationSpec` into `RuleApplicationSpecCore` (+ 3 S5-impossible fields), with the
  witness-world obligations weakened to existential form. K/T/B keep their exact names and statements.
- Re-derive the Hintikka lift parametrically over an auxiliary step-preserved predicate `Aux`, with
  a hard **regression gate**: `modalExpandBranchesGen_hintikka` keeps its exact existing name and
  statement.
- Land `modalTableauS5_sound` (statement unchanged) and `modalTableauS5_complete`, then
  `instDecidableS5Valid : Decidable (s5Valid φ)`.
- Land the **R7 refutation as a theorem**; correct the false docstrings and the 5/KB5 route note.
- **Deliver 5/KB5 validity + completeness by the Euclidean route** (Phases 15-23), the task
  description's stated deliverable, reached by the route that can actually reach it:
  - `Relation.EuclGen` -- an inductive least-Euclidean closure operator, with its
    least-Euclidean-containing property, in `Cslib/Foundations/Relation/Euclidean.lean`. This is the
    "bespoke construction" the repo's own scope notes name as the cost; it is missing **library
    infrastructure**, not a mathematical obstruction.
  - The rooted **root + universal cluster** normal form, consuming the already-landed
    `Relation.RightEuclidean.equiv_cod` (`Euclidean.lean:124`).
  - `extractModelFive` -- root+cluster countermodel extraction, mirroring `extractModelS5`.
  - `modalTableauFive_sound` / `modalTableauFive_complete`; `modalTableauKb5_sound` /
    `modalTableauKb5_complete`.
  - `instDecidableFiveValid : Decidable (fiveValid φ)`; `instDecidableKb5Valid : Decidable (kb5Valid φ)`.
- **Archive** ~2,000 lines of superseded code out of the CI-built tree -- **moved, never deleted**
  (see accounting below).
- Zero `sorry`, zero new axioms; full CSLib CI at every milestone; incremental commit at each green
  milestone; narrow `git add` (concurrent sessions active).

**Non-Goals**:
- **5/KB5 via the S5 tableau** -- *proven* unreachable (`probes/five-s5-separation.lean`;
  `fiveValid ⊊ s5Valid`). **This rejects a ROUTE, not the deliverable.** 5/KB5 itself is a **Goal**
  above, delivered by the Euclidean route (Phases 15-23). See "Route correction".
- Any `RuleApplicationSpec modalApplyOneS5` witness (proven false, kept as landed documentation).
- **Any stratification / firing-order / fairness / round-robin discipline** -- provably impossible
  (report §8 item 2). Do not phase it.
- **Any re-firing machinery** -- the crux does not exist (`.persistent` never retires the box).
- Any φ₀-parametrized rule -- type-level impossible (report §8 item 3).
- Filtration / semantic FMP as the primary route -- category error (report §8 item 9). Retained only
  as the R1 fallback (`[PARTIAL]`, deliverable 4 only).
- Tightening `modalFuel` -- scope creep; sufficiency, not tightness, is the requirement.
- **Task 511 (S4) coordination.** v2 coupled 515 to 511 via a shared keyed guard. v3 **decouples**
  them: the keyed guard is retired here, so there is no shared artifact and no sequencing
  constraint. 511 is unaffected by this plan and this plan does not owe S4 anything.
- Editing K/T/B rule declarations, `Saturation.lean`'s driver, or `FmpMeasure.lean`'s measure engine.
  The `RuleApplicationSpec` **structure** is split (Phase 9) but K/T/B's instantiations keep their
  shape via `extends`.

## Preserved-Assets Accounting

The task description says *"REUSE the CI-green Phase 1/3 assets already landed and committed by task
504: S5Simplification.lean and FrameCompleteness.lean."* This plan reuses **`FrameCompleteness.lean`
in full and verbatim** (better than v2 managed), and **archives roughly 2,000 of
`S5Simplification.lean`'s 3,041 lines** (file length verified) out of the CI-built tree. That
archival is counter-intuitive and is justified below so the next implementer does not try to rescue
it -- and so no one mistakes it for destruction. **The code is moved, not deleted** (Phase 14);
every line remains readable, in git history and at a stable archive path, with a provenance header.

### Reused VERBATIM (zero edits)

| Asset | file:line | Note |
|---|---|---|
| `modalTruthLemmaS5` | FrameCompleteness.lean:2048 | ports via `hintikka_congr` (Phase 2) |
| `modalOpenBranchS5_countermodel` | FrameCompleteness.lean:2288 | via `hintikka_congr` + Phase 5's `hTgt` |
| `hintikkaS5_box_pos` / `_diamond_neg` | :1956 / :1995 | shapes the witness rule does not touch |
| `eqvGen_mem_modalKnownWorlds_iff`, `extractModelS5*` | :1934, :499-531 | loop-back edges inert under `EqvGen` |
| `extractModelS5_rightEuclidean` | FrameCompleteness.lean | landed task-504 asset; unaffected by the 5/KB5 drop |
| `modalS5BoxAll` / `modalS5DiaNegAll` + `_mem` | S5Simplification.lean:216-291 | **untouched -- correct as they stand** |
| `modalApplyOneS5` | S5Simplification.lean:300 | called for all 12 non-mint arms **and** the mint `none` branch |
| `modalApplyOne_diamondPos_witness` / `_boxNeg_witness` | Rules.lean | discharge the `none` arm |
| `modalExpMeasure` / `modalWork` / `_step_lt_gen` | FmpMeasure.lean:192/197/3231 | **spec-free -- VERIFIED** |
| `modalUniverse` / `modalWorldBound` / `modalExpMeasure_entry_le_fuel` | FmpMeasure.lean:149/144/208 | **K's own -- verbatim** |
| `modalFuel` | Saturation.lean:98 | **unchanged, no re-derivation** |
| `modalExpandBranchesGen` / `modalStepBranchGen` / `modalTableauGen` | Saturation.lean:122/201/363 | **generic driver UNMODIFIED** |
| `accReachableInv_related_s5` | FrameSoundness.lean:1381 | the reuse-soundness engine (R1's mitigation) |
| `modalApplyOneS5_fresh_local` | FrameSoundness.lean:~1326 | stays reusable (witness rule is *defeq* to `modalApplyOneS5` on all 12 non-mint arms) |
| `signedSubfmls` + `signedSubfmls_card_le` | LoopChecking.lean:290/298 | the card bound |
| `modalApplyOneS5_rankStep_not_dischargeable` | S5Simplification.lean:2995 | **KEPT** as landed documentation of the dead rank route |

### ARCHIVED (Phase 14) -- ~2,000 CI-green, sorry-free, committed lines, MOVED not deleted

**These are retired on COST and on CORRECTNESS-OF-SUBSTRATE, not because they contain bugs.** Do not
rescue them into the live tree -- but do not destroy them either. Each block below is **moved** to
the archive path named in Phase 14, under a provenance header recording its original `file:line`,
what superseded it, and why it was retired. **They must not remain in the CI-built `Cslib/` tree**:
they are superseded, unreferenced, and would rot -- `modalUniverseS5` in particular is actively
*harmful* to keep, since it breaks the fuel arithmetic.

| Asset | file:line | Why it is retired |
|---|---|---|
| `modalWorldBoundS5`, `modalUniverseS5` + membership/length lemmas | :60-204 | **Must** be retired: `modalFuel` does **not** dominate the entry measure at this universe (`atom` 19 > 8, `□p` 135 > 120, `p∧q` 779 > 120 -- VERIFIED by execution). Keeping them in-tree **breaks the fuel**. The escape hatch `modalWorldBoundS5 ≤ modalWorldBound` is **false**. |
| `blockingWorldS5`, `successorBirthContentS5`, `modalApplyOneS5g` | :888-1051 | The **unkeyed** guard provably **never fires** (`= none` at every mint): birth content is scanned trigger-world-**locally**, but S5's universal box broadcasts **globally**, so live sets are permanently a strict superset of birth content. The S4 birth-content abstraction is sound only because in S4 a world inherits at birth everything it will ever have; **S5 violates that premise**. Additionally `modalApplyOneS5g` emits `.linear []` (:987), which **breaks `freshLocal`'s right disjunct** (needs a cons). |
| `blockingWorldS5Keyed`, `modalStepBranchS5gKeyed` | :1424-1549 | The keyed guard **genuinely works** (0/700 differential errors) -- but **no driver runs it**, and one cannot be added cheaply. See the decisive cost fact below. **The strongest archival candidate in the set**: correct code, retired only on cost. |
| `S5LoopInv` (12 fields) + ~11 `modalStepBranchS5g_preserves_*` | :1566-2723 | Invariants of a stepper **no driver runs**; and it carries **none** of `ModalLoopInvGen`'s five Hintikka-forcing fields, so it could not close the lift even if a driver existed. |
| `modalKnownWorlds_length_le_worldBoundS5`, `S5LoopInv.worldBound` | :2724-2830 | The birth-key **pigeonhole**. Replaced by `modalOps_lt_worldBound` -- a monotone injection: no powerset, no rank, no potential, no birth keys. |
| `modalApplyOneS5_snd_eq` + the acc-invariance chain | :340-351, :398 | Becomes **false** (the reuse arm adds an edge where K adds none). **Restated in place** (Phase 13), not archived -- this row is a correction, not a move. |
| Docstrings at :40-45 and :1071-1073 | | **Factually false.** *"`modalFuel` is sufficient here too"* is refuted by execution. **Rewritten in place** (Phase 3), not archived -- a false statement is corrected, never preserved as though it were a retired asset. |

**Archival makes one v3 worry moot.** v3 had to argue at length that the retired assets would never
be needed again. Under archival that argument no longer has to be airtight: if a future dispatch
does need `blockingWorldS5Keyed`, it is one `git log --follow` or one read of the archive path away.
Archival is the cheaper, more reversible decision, and it is what the user directed.

**The decisive cost fact -- why the keyed assets are retired even though the keyed stepper works.** This is
*not* "the guard fails" (that was the **unkeyed** guard -- a different function; the prior dossier's
apparent contradiction resolves because two angles measured `blockingWorldS5` and two measured
`blockingWorldS5Keyed`, and **both measurements are true**). It is:
**`modalExpMeasure_step_lt_gen` is stated for `modalStepBranchGen`** [VERIFIED]. The keyed stepper
threads `keys` and has a **different shape**, so a keyed driver could consume neither the measure
engine **nor** `modalExpandBranchesGen_hintikka` -- the single most expensive landed asset -- and
would have to re-derive both against `FmpMeasure.lean`'s 3,392 lines. The keyed route's
"~1,900 preserved lines" are **inputs to work that must still be written from scratch**. It also
grows **quadratically** (⌊n²/4⌋+1 on alternating `□◇` chains) and has an unresolved
`keysTotal`-at-initialization gap (the driver starts `keys = []` while world 0 is already known).
The witness route keeps the generic driver and *re-instantiates* that induction. **That is the whole
ballgame.**

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| **R1 (TOP RISK) -- `modalTableauS5_sound` re-proof.** `modalTableauS5_sound` (`FrameSoundness.lean:2379`) is stated for the unguarded rule. The statement stays **identical**, but the proof must be re-run against the witness rule. This is the largest un-costed item in the prior effort and is **un-mechanized**. | H | M | The new case is the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩` -- structurally **easier** than the landed mint case, because the world-assignment `f` is **not extended** (no mint), so the only obligation is `m.r (f w) (f w')` for an existing `w'`. **The decisive reuse**: `accReachableInv_related_s5` (`FrameSoundness.lean:1381`) -- **already landed** -- states exactly that two known worlds, both reachable from 0, are related in any model whose relation is an equivalence relation. **MITIGATION IS A GATE: Phase 8 probes this in scratch BEFORE Phase 9**, exactly as `hintikka_congr` and `diaPosWitness'` were probed in the research session. **Kill condition**: if the re-proof exceeds **~400 lines**, stop and re-litigate the fork (fallback 2 below). |
| **R2 -- Phase 0 tag closure.** If `(s,ψ) ∈ mintTags φ₀` is not derivable from `S5wTagInv` under the `neg φ = φ.imp .bot` encoding, the counting argument fails and the linear bound with it. | H | L | **30-minute kill test. Phase 0. Runs FIRST, before any investment.** `Proposition` has 7 constructors -- `atom, bot, imp, and, or, box, diamond` -- with no primitive negation (`Basic.lean:72-88`) [VERIFIED]. **Kill**: if it fails, fallback 1 (obtain the world bound another way -- a phase, not a redesign). |
| **R3 -- `Aux` parametrization lands on the K/T/B surface.** Phase 10 changes `ModalLoopInvGen`'s shape; dropping `rank` is an **arity change** to the structure K/T/B share, not a field swap. | H | M | `extends` + the **Phase 12 regression gate**: `modalExpandBranchesGen_hintikka` must keep its **exact existing name and statement** (`TDriver.lean:911` / `BDriver.lean:871` consume it **by name** with `∃ rank, ModalLoopInvGen …` in the hypothesis), re-derived from the parametric lift at `Aux := (∃ rank, …)`. **Kill**: if that re-derivation does not go through, **STOP at Phase 12, before any further S5-specific work is wasted** -- the factoring is wrong. |
| **R4 -- un-enumerated `modalApplyOneS5_snd_eq` consumers.** The lemma becomes **false** under the witness rule. | M | L | Blast radius is smaller than feared: `FrameSoundness.lean:1326` is inside `modalApplyOneS5_fresh_local`, which stays reusable; every other site (`S5Simplification.lean:1720/1868/1943/1953/2017/2025/2083`, and :398) lives in the S5g/keyed machinery this plan retires anyway. **Run `lean_references` on `modalApplyOneS5_snd_eq` before Phase 13** to confirm. **Kill**: if a consumer genuinely needs the **unconditional** form and is load-bearing for the countermodel half, the "ports free" claim is falsified -- re-scope. (Judged unlikely: `hintikka_congr` bypasses that lemma entirely. INFERRED.) |
| **R5 -- correctness is validated, not proved.** 3,963 formulas / 0 mismatches / 0 instability is strong evidence, **not a proof**. Depth 2, two atoms. | M | L | The soundness+completeness theorems are the proof; the corpus is the safety net. **Falsifiers**: any formula with `maxWorld > modalOps φ` under `modalApplyOneS5w`; any super-linear world growth. Land the corpus oracle as a `#eval`-backed regression test in `CslibTests` (Phase 14) -- route-independent and the cheapest correctness net available. |
| **R6 -- guard-less arm is non-negotiable.** Adding an `if acc.hasEdge w w' then (.notApplicable, acc)` guard makes `.notApplicable` **reachable on a mint shape**, which **inverts** the `exfalso` conjunct-3/4 discharge (`CompletenessLoop.lean:1049-1060`) from a refutation into a proof obligation. | H | L | Documented as a hard constraint in Phase 1 and Phase 9. Guard-less costs at most one duplicate edge per (formula, world) and is measure-inert. Do not "optimize" it. |
| **R7 (retired) -- fuel domination.** | -- | -- | **REFUTED BY EXECUTION.** Not a risk; a **settled false statement**, landed as a theorem in Phase 3. `maxWorld = fuel/2` exactly, no fixpoint. Do not spend another cycle here. |
| **R8 -- the `birth` trap.** A `birth` function must **NOT** be defined concretely as "the least world carrying the pair": S5's universal box can later add `⟨s,φ,w''⟩` at a **smaller** world, so that formulation is **not step-preserved**. | H | M | The `usedTags`-cardinality formulation (Phase 7) sidesteps this entirely by **never naming a witness world**. This trap is real and cost a prior design; it is called out inline in Phase 7. |
| **R9 -- scope realism.** Landing all 25 phases sorry-free in one task is optimistic; v2's precedent is a `[BLOCKED]` capstone, and 515 has now hit **two** distinct Phase-19 soundness blockers (propagation, then mint-arm). | M | H | Three hard gates (Phase 0, Phase 8, Phase 15), one regression gate (Phase 12), and now a **Phase 19a KILL budget** on the termination re-derivation fail **cheap and early**, before investment. Each phase commits independently at green. If a phase resists, mark `[BLOCKED]` with the exact `lean_goal` open state -- never a `sorry`. **The DAG is ordered so the S5 deliverable never depends on the Euclidean one**: Phases 15-23 sit strictly after Phase 14, so a stall there lands the S5 chain green and the 5/KB5 chain `[BLOCKED]`, a real partial delivery rather than a total loss. **REAFFIRMED (v6)**: the current state IS that real partial -- S5 (Phases 0-14) + Phase 18 + the Phase-19 soundness building blocks (Route-1 propagation fix, `accReachableInv_related_five`, the five green lemmas) are committed and independent of the remaining Euclidean chain; the 5/KB5 chain is `[BLOCKED -- Route (a) selected, see report 08]` pending 19a/19b. Likelihood is **H** honestly: 25 phases at 60h is a lot of surface, two capstone soundness gaps have already materialized, and saying otherwise would repeat v2's error. |
| **R10 (NEW in v4) -- the Euclidean chain is genuinely new mathematics, not a port.** Phases 16-23 have **no landed precedent** in the way Phases 9-12 port K's machinery. `Relation.EuclGen` does not exist in Mathlib or this repo; the root-aware rule has no sibling; `extractModelFive` is a new extraction. Cost could exceed the 25h budgeted for them. | M | M | **Three real cost reducers, all verified**: (1) `Relation.RightEuclidean.equiv_cod : IsEquiv (cod r) r` (`Euclidean.lean:124`) **already mechanizes the root+cluster fact** -- the cluster's `IsEquiv` is free, with `rightTotal_cod` (:121), `cod_subset_dom` (:113), `refl_cod` (:45) supporting it; (2) `Relation.SymmGen`/`Relation.EqvGen`/`Relation.ReflGen` (`Confluence.lean`) are a **direct structural template** for `EuclGen` -- including `ReflTransGen (SymmGen r) = EqvGen r` (:374) as a worked closure-characterization precedent; (3) the **entire termination half is reused** from Phases 1-7 -- the mint arms of the root-aware rule are shape-identical to `modalApplyOneS5w`'s, so `usedTags`/`S5wWorldInv`/`modalOps_lt_worldBound` port directly. **Phase 15 is a scratch gate** that measures this before any file is written. **Kill**: if Phase 15 finds the rooted normal form does not hold in the shape claimed, or `EuclGen`'s least property resists, `[BLOCKED]` at 15 -- cost ~1.5h, and Phases 0-14 are already green and committed. |
| **R11 (NEW in v4) -- `EuclGen` lands in `Foundations/`, a shared, high-traffic directory.** `Cslib/Foundations/Relation/Euclidean.lean` is consumed outside this task's blast radius; adding a closure operator there is a wider surface than `S5Simplification.lean`. | M | L | `EuclGen` is **purely additive** -- a new inductive plus its own lemmas, touching no existing declaration in the file. It mirrors the placement precedent of `SymmGen`/`EqvGen` in the sibling `Confluence.lean`. Phase 16's verification requires the **whole `Foundations/` tree to compile unmodified** and `shake` to report no new suggestions. **Kill**: if the addition perturbs any existing `Euclidean.lean` consumer, move `EuclGen` into the Tableau directory as a local definition and re-scope upstreaming to a follow-up. |
| **R12 (NEW in v6) -- Phase 19a re-derives the tag-injection termination bound on LANDED GREEN assets.** The mint-arm guard (Route (a)) forces a from-scratch re-derivation of `mintTags`/`usedTags`/`S5wTagInv`/`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w` under a source-split "≤1 mint per tag per {root, non-root}" invariant. These are Phase-6/7 assets, currently committed and CI-green; re-deriving them risks perturbing the S5 chain if the invariants are shared rather than Five-local. This is the single largest un-mechanized item in v6 and the honest reason for the +8h. | H | M | **`reports/08_*` proves the bound stays LINEAR** (≈ `2·|modalSubfmls φ₀|` -- a larger constant only). Execute as **sorry-free CI-green sub-milestones with a KILL budget** (Phase 19a), each committed per `git-workflow.md`'s commit-per-green-substep mandate. **Prefer Five-local analogues** of the tag invariants over mutating the shared S5 lemmas, so the S5 chain (Phases 0-14) stays untouched -- only reach into `S5Simplification.lean` if a genuine source-split generalization is unavoidable, and re-verify the whole S5 surface if so. **Kill**: if the re-derivation blows the budget, `[BLOCKED]` at 19a with the exact `lean_goal` + line count, then **Fallback 4** (permanent S5-only delivery). The S5 deliverable is already green and committed, so a 19a stall is a cost overrun, never a loss. |

**Fallbacks (in order)**:
1. **If R2 fails but the rule is sound**: keep the rule; obtain the world bound another way. This is a
   phase, not a redesign.
2. **If R1 fails**: the **atom-quotient semantic FMP** route (`Decidable (s5Valid φ)` via enumerating
   quotient models over `Fin k → Bool`) is **pre-authorized** by plan v2's Phase 8 blocked branch and
   was compiled sorry-free and axiom-clean in the research session. It delivers **deliverable (4)
   only** -- not `modalTableauS5_complete`, and **not** 5/KB5 (its `qTransfer` needs reflexivity,
   which `fiveFC`/`kb5FC` lack). Legitimate as a documented `[PARTIAL]`, **not** as the primary route.
3. **If R3 fails**: stop at Phase 12. Phases 0-8 (rule, congruence, refutation, budget,
   `accTargetsKnown`, tag invariant, counting crux) remain landed, green, and independently valuable.
4. **If R10/R11/R12 fail (the Euclidean chain stalls -- specifically, if Phase 19a's termination
   re-derivation blows its KILL budget, or any later Euclidean phase resists)**: land Phases 0-14 green
   (the full S5 deliverable -- rule, soundness, completeness, `Decidable (s5Valid φ)`, archival) and
   mark the stalled Euclidean phase `[BLOCKED]` with the exact `lean_goal` open state. **This is a
   genuine partial delivery, not a failure**: the S5 chain is the task's primary deliverable and does
   not depend on the Euclidean chain in either direction. `reports/08_*` names this the legitimate
   terminus **only if** Route (a)'s termination re-derivation is judged not worth its cost -- it is NOT
   warranted on soundness grounds (Route (a) IS sound and bounded), so Fallback 4 is a cost decision,
   never a soundness retreat, and **Route (b) is never the alternative** (it is provably dead). **The
   5/KB5 deliverable is NOT re-struck by this fallback** -- a `[BLOCKED]` Euclidean phase is a cost
   overrun to be resumed, and the honest disposition is a follow-up task carrying the exact open goal,
   never a scope amendment. Do not let a stall here be re-narrated as vindication of v3's impossibility
   claim; `probes/five-s5-separation.lean` refutes that claim independently of whether this plan's
   budget holds.

## Testing & Validation

Run the full CSLib CI pipeline at **every** phase milestone (zero-debt contract) before committing:

- [ ] `lake build` -- full project green (baseline: 3239/3239 jobs)
- [ ] `lake exe checkInitImports` -- clean
- [ ] `lake exe lint-style` -- clean
- [ ] `lake lint` -- 0 new errors on task-touched files (1 pre-existing unrelated `unusedArguments`
      error in `PrimeExclusion.lean`, and a pre-existing `sorry` in
      `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:118` from task 317, both predate
      this task; do not action)
- [ ] `lake test` -- `CslibTests` suite exit 0
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- no NEW suggestions for task-touched files
- [ ] `grep -c 'sorry' <touched files>` -- 0 (prose mentions excepted)
- [ ] `grep -c '^axiom ' <touched files>` -- 0 new axioms
- [ ] `lean_verify` on each phase's headline declaration -- axioms limited to
      `propext` / `Classical.choice` / `Quot.sound`
- [ ] **Regression gate (Phases 9-12)**: `TDriver.lean` and `BDriver.lean` compile **unmodified**;
      `modalExpandBranchesGen_hintikka` retains its exact name and statement.
- [ ] `lake exe mk_all --module` -- **required whenever a new file is added** (Phases 18, 22 may add
      `FiveSimplification.lean` / `Kb5Simplification.lean`); the `Cslib.lean` barrel import must stay
      current.
- [ ] **Archival gate (Phase 14)**: all six CI steps green **with the ~2,000 archived lines out of
      the tree**; every archived block present at its `archive/` path with a complete provenance
      header; **`git status` shows the archive files as ADDED, not only `S5Simplification.lean` as
      modified** -- a removals-only diff is a demolition and a phase failure.
- [ ] **Regression gate (Phases 15-23)**: the S5 surface is **untouched** by the Euclidean chain --
      `modalTableauS5`, `modalTableauS5_sound`, `modalTableauS5_complete`, `instDecidableS5Valid`,
      `extractModelS5*`, `modalTruthLemmaS5` all retain their exact names and statements. The
      Euclidean route is **additive**.
- [ ] **Separation regression (Phases 21, 23)**: `#eval` confirms `□p → p` is **not** `fiveValid` and
      **not** `kb5Valid` while being `s5Valid` -- a live check that the Euclidean route really sits at
      `fiveFC`/`kb5FC` and has not silently collapsed into `s5FC`.
- [ ] **Foundations gate (Phase 16)**: the whole `Cslib/Foundations/` tree compiles unmodified after
      `Relation.EuclGen` lands; `shake` reports no new suggestions (R11).

Per-milestone commit discipline: **narrow `git add`** -- only the specific `.lean` file(s) touched by
the phase, plus this plan and state files. **Never `git add -A` / `git commit -am`** (concurrent
sessions are active on this repo). Commit message: `task 515 phase {P}: {name}`. **Phase 14 stages
both the archive additions and the `S5Simplification.lean` removals in the same commit**, so the
move is atomic and reviewable as a move.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0, 3, 4, 5 | -- |
| 2 | 1, 6 | 0, 4 |
| 3 | 2, 7, 8 | 1, 6 |
| 4 | 9, 13 | 2, 8 |
| 5 | 10 | 7, 9 |
| 6 | 11 | 10 |
| 7 | 12 | 11 |
| 8 | 14 | 3, 5, 12, 13 |
| 9 | 15 | 14 |
| 10 | 16 | 15 |
| 11 | 17 | 16 |
| 12 | 18 | 17 |
| 13 | 19a, 20 | 18 |
| 14 | 19b | 19a |
| 15 | 21 | 19b, 20 |
| 16 | 22 | 21 |
| 17 | 23 | 22 |

Phases within the same wave can execute in parallel. **Phase 0 gates everything.** **Phase 8 (R1
scratch probe) gates Phase 9 onward.** **Phase 12 carries the K/T/B regression gate: if it fails,
stop.** Phases 3, 4, 5 are independent of the rule and can start immediately in parallel with the
kill test. Phase 13 (soundness) forks after Phase 8 and runs parallel to the 9→10→11→12 lift chain.
**Phase 19a (mint-arm guard + termination re-derivation) gates Phase 19b** (`modalTableauFive_sound`
assembly consumes the re-derived, source-split termination bound and the now-sound mint lemmas);
**Phase 20 (`extractModelFive`, the completeness/countermodel side) is independent of the soundness
re-derivation** and depends only on Phases 17/18, so it runs in parallel with 19a.

**Waves 9-17 are the Euclidean 5/KB5 route (Phases 15-23, Phase 19 now split into 19a+19b), and they
sit at the END of the DAG by design.** They **consume** the S5 chain rather than blocking it: rooted
Euclidean frames are root + universal cluster, so the cluster half is exactly what Phases 0-14 build,
and the whole termination argument (Phases 4, 6, 7) ports -- **and is now re-derived once more, under
a source-split invariant, in Phase 19a**. Nothing in Phases 0-14 depends on them. A stall anywhere in
15-23 therefore leaves the **entire S5 deliverable green, committed, and shipped** (Fallback 4).
**Phase 15 is a cheap scratch gate** on the same pattern as Phases 0 and 8. **Phase 19a carries its
own KILL budget** (the termination re-derivation touches landed green assets; if it blows the budget,
Fallback 4 -- permanent S5-only delivery -- becomes the terminus).

Ambient context for every Lean phase: `S5Simplification.lean:54-56`
(`namespace Cslib.Logic.Modal.Tableau`, `open Cslib.Logic.Tableau Cslib.Logic.Modal`) and the file's
`variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]`. **No `Fintype Atom` is needed
anywhere.**

### Phase 0: Kill test -- `modalSubfmls` tag closure under the `neg` encoding [COMPLETED]

**Goal**: Cheaply falsify the entire design before any investment. Verify `modalSubfmls` closure
survives the `neg φ = φ.imp .bot` encoding, so that `(s,ψ) ∈ mintTags φ₀` is derivable from the tag
invariant in the mint case. **This is the single load-bearing step of the counting argument.**

**Tasks**:
- [ ] In scratch only (`lean_run_code` / `lean_multi_attempt`; **no `.lean` file edited**), confirm
      that for `φ₀` containing `◇ψ` (resp. `□ψ`), the pair `(.pos, ψ)` (resp. `(.neg, ψ)`) is
      reachable in `signedSubfmls φ₀` / `modalSubfmls φ₀` under the encoding
      `neg φ = φ.imp .bot`. `Proposition` has 7 constructors -- `atom, bot, imp, and, or, box,
      diamond` -- with **no primitive negation** (`Basic.lean:72-88`) [VERIFIED].
- [x] Record the result in the phase's completion note (pass -> proceed; fail -> invoke fallback 1
      and re-plan the world bound, keeping the rule).

**Completion note (PASS)**: Verified in `lean_run_code` scratch (no `.lean` file touched) against
`Cslib/Logics/Modal/Tableau/LoopChecking.lean`: for `φ₀ := ◇ψ` with `ψ := p.imp .bot` (the
negation encoding of `¬p`), `ψ ∈ modalSubfmls φ₀` closes by `simp [modalSubfmls]`; symmetrically
for `φ₀ := □ψ`; and the actual tag codomain `(Sign.pos, ψ) ∈ signedSubfmls φ₀` /
`(Sign.neg, ψ) ∈ signedSubfmls φ₀` both close by `simp [signedSubfmls, modalSubfmls]`. The
generic, **public** `modalSubfmls_self_mem` (`FmpMeasure.lean:266`) already gives `ψ ∈
modalSubfmls ψ` unconditionally regardless of whether `ψ` is negation-encoded (`Proposition` has
no primitive negation constructor to special-case), and this fact already underlies `BDriver.lean`
(K/B route) and the superseded `S5Simplification.lean`'s own local re-derivation
(`modalSubfmls_self_mem_S5`, `modalSubfmls_trans_S5`). **Kill test PASSES.** Proceed to Phase 1.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**: none (scratch probe only)

**Verification**: a scratch snippet demonstrating the derivation, or a documented counterexample.

**Blocked-branch**: if closure fails, **do not proceed to Phase 6/7**. The rule (Phases 1-2) and the
refutation (Phase 3) remain independently valuable and should still land. Invoke fallback 1.

---

### Phase 1: The witness-reuse rule + the free bridges [COMPLETED]

**Goal**: Land the rule. All four declarations below **already compiled sorry-free in the research
session**; this phase transcribes and CI-greens them.

**Tasks**:
- [x] Land `witnessWorldS5`:
      ```lean
      def witnessWorldS5 (b : List (SignedFormula (Proposition Atom) WorldIndex))
          (s : Sign) (φ : Proposition Atom) : Option WorldIndex :=
        (modalKnownWorlds b).find? (fun w' => b.any (· == (⟨s, φ, w'⟩ : SignedFormula _ _)))
      ```
- [x] Land `modalApplyOneS5w : RuleApply Atom` (**plain, NOT φ₀-parametrized** -- see report §8 item
      3; `hOutputsSubsetUniverse` at `FmpMeasure.lean:3241` binds `φ0` universally **inside** the
      hypothesis, so a φ₀-parametrized rule can never discharge it):
      ```lean
      /-- GUARD-LESS. Always `.linear [witness]` on a hit -- never `.notApplicable`, never `.linear []`. -/
      def modalApplyOneS5w : RuleApply Atom := fun sf b acc =>
        match sf.sign, sf.formula with
        | .pos, .diamond φ =>
          (match witnessWorldS5 b .pos φ with
           | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
           | none => modalApplyOneS5 sf b acc)
        | .neg, .box φ =>
          (match witnessWorldS5 b .neg φ with
           | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
           | none => modalApplyOneS5 sf b acc)
        | _, _ => modalApplyOneS5 sf b acc
      ```
- [x] Land `witnessWorldS5_mem (h : witnessWorldS5 b s φ = some w') : ⟨s, φ, w'⟩ ∈ b`.
      **Compiled in research** (2 lines: `have := List.find?_some h; simpa using (List.any_eq_true.mp this)`;
      axioms `[propext, Quot.sound]`).
- [x] Land the two `rfl` bridges -- **compiled in research**, axioms `[propext]`:
      `modalApplyOneS5w_boxPos_eq`, `modalApplyOneS5w_diaNeg_eq`.
- [x] Land `modalApplyOneS5w_eq_of_not_mint_shape (h : ¬mint-shaped sf) : modalApplyOneS5w sf b acc = modalApplyOneS5 sf b acc`.

**Completion note**: All four declarations landed verbatim in
`Cslib/Logics/Modal/Tableau/S5Simplification.lean`, inserted immediately after
`modalApplyOneS5_boxPos_diaNeg_eq` (before the `modalWorldBoundS5`-dependent section slated for
Phase 14 archival). `lake build Cslib.Logics.Modal.Tableau.S5Simplification` green (848/848
jobs); `lake exe checkInitImports` clean; `lake exe lint-style` clean; zero new `sorry`.
`lean_verify` confirms `witnessWorldS5_mem` -> `[propext, Quot.sound]` and
`modalApplyOneS5w_eq_of_not_mint_shape` -> `[propext, Quot.sound]`, matching the research-session
figures exactly (the two `rfl` bridges are axiom-free `rfl` terms, subsumed by the general
`_eq_of_not_mint_shape` lemma). Note `modalApplyOneS5w_eq_of_not_mint_shape`'s hypothesis is
phrased over the mint shapes directly (`.pos,.diamond` / `.neg,.box`) rather than the
propagation shapes, which is the logically dual (and equivalent, since these are the only two
S5-relevant shapes) framing to the task list's "¬mint-shaped sf" description.

**Three design constraints, EACH LOAD-BEARING -- do not "optimize" any of them**:
- **`.linear [witness]`, not `.linear []`** -- the cons is required for `freshLocal`'s right disjunct
  (`.linear (wsf :: rest) ∧ .snd = acc.addEdge sf.label wsf.label`). Note `wsf` is bound only as the
  **head of the linear output**; nothing requires `wsf.label = modalNextWorld b`, despite the
  docstring saying "fresh" [VERIFIED, `GenericDriver.lean:181-190`]. The landed `modalApplyOneS5g`
  emits `.linear []` (`S5Simplification.lean:987`) and **breaks this shape** -- a genuine correction
  over the landed code.
- **`.linear [witness]`, not `.persistent []`** -- `.persistent` with an empty payload returns `some`
  with `b` **and** `expanded` unchanged (`Saturation.lean:141`): an instant infinite loop.
- **No `hasEdge` guard** (R6) -- see Phase 9.

**Timing**: 1 hour

**Depends on**: 0

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `witnessWorldS5_mem` and both bridges.

---

### Phase 2: The Hintikka congruence bridge [COMPLETED]

**Goal**: Land `hintikka_congr`. **This is the single highest-value declaration in the plan** -- it
ports the entire landed countermodel half of S5 completeness **verbatim, with zero edits to
`FrameCompleteness.lean`**. Land it early and the whole plan de-risks.

**Tasks**:
- [x] Land:
      ```lean
      theorem hintikka_congr (b) (acc) :
          modalHintikkaSetGen modalApplyOneS5w b acc ↔ modalHintikkaSetGen modalApplyOneS5 b acc
      ```
      **COMPILED IN RESEARCH, sorry-free, `#print axioms` = `[propext]`**, by:
      ```lean
      unfold modalHintikkaSetGen
      constructor <;> · rintro ⟨h1, h2, h3, h4⟩
                        refine ⟨h1, ?_, h3, h4⟩
                        intro sf hsf
                        have h := h2 sf hsf
                        rcases hs : sf.sign with _ | _ <;>
                          rcases hf : sf.formula with _|_|_|_|_|ψ|ψ <;> simp_all [modalApplyOneS5w]
      ```
- [x] Record **why it works** in the docstring [VERIFIED by reading `Saturation.lean:460-480`]:
      conjunct 2 binds `let (result, _) := apply sf b acc` but then returns **literal `True`** at
      `| .neg, .box _` and `| .pos, .diamond _` -- `result` is **unused at exactly the two shapes the
      witness rule intercepts**. Conjuncts 1/3/4 name no rule function at all.
- [x] Confirm this supersedes the two `rfl` bridges as the porting mechanism: the bridges alone are
      defeated by the 8 rewrites through `modalApplyOneS5_eq_of_not_boxPos_diaNeg` at
      `FrameCompleteness.lean:2096-2181`.

**Completion note**: Landed verbatim in `S5Simplification.lean` immediately after
`modalApplyOneS5w_eq_of_not_mint_shape`. `lake build` scoped green (848/848); `lean_verify`
confirms `hintikka_congr` -> `[propext]`, exactly the research-session figure.
`FrameCompleteness.lean` diff-verified **unmodified** (`git diff --stat` empty). `checkInitImports`
and `lint-style` clean; sorry count unchanged (0 real sorries).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `hintikka_congr` (expect `[propext]`);
`FrameCompleteness.lean` **unmodified**.

---

### Phase 3: Land the R7 refutation as a theorem + correct the false docstrings and the 5/KB5 ROUTE note [COMPLETED]

**Goal**: Convert *"Phase 8 blocked"* into *"the Phase 8 target was refutable"* -- a landable,
sorry-free result -- and correct the three factually false pieces of documentation that misled the
last planner. **Independent of the rule; can start immediately.**

**Tasks**:
- [x] Land a **sibling** to `modalApplyOneS5_rankStep_not_dischargeable` (`S5Simplification.lean:2995`),
      in the same `decide`-backed idiom, refuting the Phase 8 goal for `modalApplyOneS5`: exhibit
      `[T(□◇p)@0]` and show `modalExpandBranchesGen modalApplyOneS5` yields `maxWorld = fuel/2` with
      no fixpoint, hence `modalHintikkaSetGen modalApplyOneS5 bR aR` is **false at every fuel value**.
      Suggested name: `modalApplyOneS5_hintikka_not_reachable` (or
      `modalApplyOneS5_expansion_unbounded`). Mechanism to record in the docstring: `T(□◇p)@0` is
      `.persistent` so it never retires; it re-fires at the newest world `w`, emitting `T(◇p)@w`;
      that fresh signed formula is `.linear`, fires **once**, and mints `w+1`; the box re-fires
      there; repeat. The supply of trigger formulas never runs out because **each new world
      manufactures a new one**. This is the honest disposition of the
      `FrameCompleteness.lean:2245-2273` scope note (whose route (b) is this false statement).
- [x] **Remove and rewrite** the false docstring at `S5Simplification.lean:1071-1073` (a false
      statement is corrected in place, never archived as though it were a retired asset):
      *"S5 never mints a world
      outside the K `diamondPos`/`boxNeg` arms, so `modalFuel` is sufficient here too"*. The first
      half is **true** (and is precisely why the fix is local to minting); the second half is
      **false** by execution. Rewrite, do not preserve.
- [x] **Correct** the docstring at `S5Simplification.lean:40-45` (*"`modalApplyOneS5` never mints a
      world"*).
- [x] **Correct `FrameCompleteness.lean:571-580`** -- the 5/KB5 note. It currently frames the gap as
      a **scheduling** dependency (*"needs `modalTableauS5_complete` … as its proof engine"*). Replace
      with the **frame-class inclusion obstruction**: `s5FC = Std.Refl r ∧ RightEuclidean r` (:1273)
      but `fiveFC = RightEuclidean r` alone (**:1282** -- **note the corrected line number; v3
      miscited this as :1283**) and `kb5FC = Std.Symm r ∧ RightEuclidean r` (:1291) are **strictly
      larger** frame classes; `□p → p` on the one-world **empty** frame separates them (both
      `RightEuclidean` and `Std.Symm` are vacuous with no edges); hence `fiveValid ⊊ s5Valid` and
      **no S5 tableau can decide `fiveValid`**, regardless of whether `modalTableauS5_complete`
      exists.
- [x] **Cite the probe by theorem name** in that corrected docstring, so the claim is backed by a
      proof rather than by prose: `fiveValid_ssubset_s5Valid` and `kb5Valid_ssubset_s5Valid`, with
      supporting `boxImp_s5Valid`, `boxImp_not_fiveValid`, `boxImp_not_kb5Valid`,
      `fiveValid_imp_s5Valid`, `kb5Valid_imp_s5Valid`, `s5FC_imp_fiveFC`, `s5FC_imp_kb5FC`
      (`specs/515_s5_universal_rule_termination_unblock_504/probes/five-s5-separation.lean`,
      sorry-free, **zero axioms**). **If Phase 23 lands, port these to the live tree beside the
      Euclidean route** rather than leaving them cited from a probe path.
- [x] **CRITICAL -- state the ROUTE obstruction, NOT an impossibility.** The corrected docstring must
      say *"5/KB5 is not deliverable **via this S5 route**; it is delivered by the dedicated
      Euclidean route (`modalTableauFive`, `Relation.EuclGen`)"*. It **MUST NOT** say 5/KB5 is
      impossible, unreachable in principle, or a mathematical obstruction. **That overclaim in v3 is
      precisely what this revision corrects**, and a docstring is exactly where it would ossify and
      mislead the next planner -- the same way `:571-580`'s scheduling framing misled the last one.
      Phase 23 will replace this note wholesale once the Euclidean route lands; until then it must
      point forward, not close the door.
- [x] **Retain** the note's second half (pure-K5/pure-5 needs a bespoke closure operator for want of
      a Mathlib "Euclidean closure" analogous to `Relation.EqvGen`) -- that half is **factually
      correct** and stays. But **re-label it as COST, not impossibility**: it is missing library
      infrastructure, and `Relation.EuclGen` (Phase 16) is exactly the bespoke construction it names.
      Note the file's own wording already says *"OUT OF SCOPE … would need a bespoke construction"*
      (:583-585) -- i.e. cost. Do not escalate it.
- [x] Add BibKey docstring traceability for the refutation: **Gore1999** (`references.bib:987`),
      **TR p.48** -- *"it can lead to an infinite chain A ∈ w, ◇A ∈ w, ◇◇A ∈ w, … so this system
      cannot give a decision procedure for S5 either."* **Cite by TR pagination (TR pp.1-106), NOT
      the Handbook's pp.297-396 -- they do not map.**

**Completion note**: The R7 refutation is landed as **four `decide`-backed theorems**
(`modalApplyOneS5_hintikka_not_reachable_step{1,2,3,4}` + `_growth`) chaining single steps of
`modalStepBranchGen modalApplyOneS5` from `[T(□◇(atom 0))@0]`: the process never returns `none`
(never Hintikka-saturates) over 4 steps while `modalMaxWorld` strictly climbs `0 ↦ 1 ↦ 2`
(matching the empirically-verified `maxWorld = fuel/2` relationship exactly). **Deviation from
the task's literal wording**: the theorem does NOT execute `modalExpandBranchesGen` (the
fuel-wrapped driver) directly, because that driver's nested well-founded recursion does not
reduce under kernel `rfl`/`decide` at any tested fuel magnitude (confirmed: `decide`/`rfl` both
get stuck mid-reduction) -- this is the SAME structural limitation `LoopChecking.lean`'s "Sanity
Checks" section already documents and works around (interactive `#eval` only, never embedded,
since `#eval`/`native_decide` additionally fail outright under this directory's `module`/
`public meta import` boundary). The single-step `modalStepBranchGen`, by contrast, IS a plain
non-recursive function and reduces fine; chaining it four times gives a fully rigorous,
sorry-free, `decide`-backed counterexample of equivalent evidentiary strength, verified against
an independent interactive `#eval` reproduction of the exact research-report table
(`fuel 10 ↦ maxWorld 5`, `20 ↦ 10`, `40 ↦ 20`) cited in the new docstring but, per the same
precedent, not embedded as permanent code. Both docstring corrections
(`S5Simplification.lean` near the file header and near `modalTableauS5`) and the
`FrameCompleteness.lean` 5/KB5 route note are landed verbatim per the task list, citing the
probe's theorem names. `grep -rn -i "impossib" Cslib/Logics/Modal/Tableau/` returns no hit
referring to 5/KB5 (verified). Full project `lake build` green (3239/3239); `checkInitImports`,
`lint-style`, `lint` (scoped) clean; `lake shake` shows no new suggestions for either touched
file (pre-existing suggestions elsewhere in the repo are unrelated to this task). `lean_verify`
on `modalApplyOneS5_hintikka_not_reachable_growth` -> `[propext]`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`,
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (docstring only)

**Verification**: full CI green; the refutation theorem closes sorry-free; no docstring in either
file asserts fuel sufficiency for the unguarded S5 expansion or frames 5/KB5 as a scheduling issue;
**and no docstring anywhere asserts that 5/KB5 is impossible, unreachable in principle, or a
mathematical obstruction** -- `grep -rn -i "impossib" Cslib/Logics/Modal/Tableau/` must return no
hit that refers to 5/KB5 (hits referring to `rankStep`, stratification, or φ₀-parametrization are
correct and expected).

---

### Phase 4: The linear budget arithmetic [COMPLETED]

**Goal**: Land the arithmetic that lets `modalUniverse` / `modalWorldBound` / `modalExpMeasure` /
`modalExpMeasure_entry_le_fuel` / `modalFuel` be reused **verbatim at K's own universe**, and lets
`modalWorldBoundS5`/`modalUniverseS5` be **archived** rather than parametrized. It single-handedly
retires the `(universe, worldBound)`-parametrization blocker. **Independent of the rule.**

**Tasks**:
- [x] Land `def modalOps : Proposition Atom → Nat` -- **modal-operator OCCURRENCES**.
- [x] Land `lemma modalOps_le_complexity (φ) : modalOps φ ≤ modalComplexity φ`.
- [x] Land `lemma modalOps_lt_worldBound (φ) : modalOps φ < modalWorldBound φ`.
      **PROVED sorry-free in research** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`),
      via `modalWorldBound φ = (2c+1)^(c+1) ≥ (2c+1)^1 = 2c+1 > c ≥ modalOps φ`.
      **The `c = 0` case is the tight one** (`0 < 1 = 1^1`) -- and the *naive* `2 * |modalSubfmls φ|`
      budget **fails** there (2 > 1). **Counting modal-operator occurrences rather than subformulas
      is load-bearing, not cosmetic.**
- [x] Land `def mintTags (φ₀) : Finset (Sign × Proposition Atom)` -- `◇ψ ↦ (pos,ψ)`; `□ψ ↦ (neg,ψ)`.
- [x] Land `lemma mintTags_card_le_modalOps (φ₀) : (mintTags φ₀).card ≤ modalOps φ₀`.

**Completion note**: All four declarations landed verbatim in `S5Simplification.lean`
immediately after `hintikka_congr`. `lean_verify` on `modalOps_lt_worldBound` ->
`[propext, Quot.sound]` (leaner than the research-session figure -- no `Classical.choice`
needed; the proof only uses `Nat.pow_le_pow_right`/`omega`, no classical case split).
`mintTags_card_le_modalOps` -> `[propext, Classical.choice, Quot.sound]` (Finset lemmas pull in
`Classical.choice`), matching expectations for `Finset`-valued reasoning. `lake build` scoped
green (848/848); `checkInitImports` and `lint-style` clean; zero new sorry.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `modalOps_lt_worldBound`.

---

### Phase 5: `accTargetsKnown` top-loop generalization [COMPLETED]

**Goal**: Close a genuinely missing generic lemma that **every route needs**. This survives verbatim
from plan v2's "recommended next dispatch, item 1" and from the repo's own scope note. Promoted here
(from the report's Phase 10) because it is early, cheap, off the critical path, and unblocks
`modalOpenBranchS5_countermodel`'s `hTgt` argument. **Independent of the rule.**

**Tasks**:
- [x] Land `theorem modalExpandBranchesGen_openBranch_accTargetsKnown`. `grep` for
      `openBranch_accTargetsKnown` returns **zero hits** across `Cslib/` [VERIFIED]; the repo's own
      scope note (`FrameCompleteness.lean:2250-2253`) says it is *"not yet built"* and prescribes the
      fix.
- [x] Route: **generalize `modalExpandBranchesGen_openBranch_accSourcesKnown`'s double induction**
      (`BDriver.lean:1065-1205`) over an arbitrary step-preserved per-`(branch, acc)` predicate `P`
      -- **its body is already predicate-agnostic** -- then instantiate at **both**
      `accSourcesKnown` and `accTargetsKnown`. ~60-line clone.
- [x] Confirm zero regression to B: `modalExpandBranchesGen_openBranch_accSourcesKnown` keeps its
      exact name and statement (re-derived from the generalized form).
- [x] Note: the step-level fact is already generic and S5-ready
      (`modalStepBranch_preserves_accTargetsKnown_gen`); **only the top-loop propagation is missing**.
      `modalOpenBranchS5_countermodel` **REQUIRES** this as its `hTgt` argument -- several candidate
      designs listed that theorem under "reuses" while never supplying its hypothesis.

**Completion note**: Landed `modalExpandBranchesGen_openBranch_gen` (the generic double
induction, parametrized over `P` and its step-preservation hypothesis `hPresP`), then
re-derived `modalExpandBranchesGen_openBranch_accSourcesKnown` from it (exact name/statement
preserved, one-line proof term now) and landed the new
`modalExpandBranchesGen_openBranch_accTargetsKnown` by instantiating at `accTargetsKnown` +
`modalStepBranch_preserves_accTargetsKnown_gen` (already generic, `FmpMeasure.lean`). Full
project `lake build` green (3239/3239) -- confirms zero regression to every existing B consumer.
`lean_verify` on the new theorem -> `[propext, Classical.choice, Quot.sound]`. `checkInitImports`,
`lint-style`, `lint` (scoped) clean; zero new sorry.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**: `Cslib/Logics/Modal/Tableau/BDriver.lean` (generalization + re-derivation)

**Verification**: full CI green; `BDriver.lean`'s existing consumers compile unmodified; the new
theorem closes sorry-free.

---

### Phase 6: The tag invariant (no world hypothesis -- breaks the circularity) [COMPLETED]

**Goal**: Land the tag-only branch invariant. **It deliberately carries NO world-bound hypothesis**
-- this is necessary, not an oversight.

**Tasks**:
- [x] Land:
      ```lean
      def S5wTagInv (φ₀) (b) : Prop := ∀ x ∈ b, (x.sign, x.formula) ∈ signedSubfmls φ₀
      def usedTags (φ₀) (b) : Finset (Sign × Proposition Atom) :=
        (mintTags φ₀).filter (fun p => b.any (fun x => x.sign == p.1 && x.formula == p.2))
      lemma usedTags_mono (h : ∀ x ∈ b, x ∈ b') : usedTags φ₀ b ⊆ usedTags φ₀ b'
      theorem modalApplyOneS5w_outputs_tags (hb : S5wTagInv φ₀ b) (hsf : sf ∈ b) : ...
      ```
- [x] Record **why `S5wTagInv` carries no world hypothesis**: the landed
      `modalApplyOneS5_outputs_subset` (`S5Simplification.lean:1330`) takes
      `modalMaxWorld b < modalWorldBoundS5 φ₀` as an **input**, so it **cannot be used to prove the
      world bound**. The tag-only invariant breaks that circularity. (That landed lemma is part of
      the Phase 14 archival set anyway.)
- [x] Consume Phase 0's tag-closure result for the mint case.

**Completion note**: Landed `S5wTagInv`, `usedTags`, `usedTags_mono` verbatim per the task list.
For `modalApplyOneS5w_outputs_tags`, the plan left its exact statement as `...`; landed it as the
conjunction bundling two directional lemmas (`modalApplyOneS5w_diamondPos_tag_mem`,
`modalApplyOneS5w_boxNeg_tag_mem`) that consume Phase 0's kill-test result via two new
subformula-closure lemmas (`mem_mintTags_of_diamond_mem`/`_of_box_mem`, proved by structural
induction on `φ₀` mirroring `mintTags`'s own recursion): `sf ∈ b` mint-shaped plus `S5wTagInv φ₀
b` gives `(sf.sign, sf.formula) ∈ signedSubfmls φ₀`, hence the argument formula is itself a
member of `modalSubfmls φ₀`, hence (by the two new closure lemmas) its mint tag is a member of
`mintTags φ₀`. All 7 new declarations close sorry-free; `lean_verify` on
`modalApplyOneS5w_outputs_tags` -> `[propext, Classical.choice, Quot.sound]`. `lake build`
scoped green (848/848); `checkInitImports`/`lint-style` clean; zero new sorry; zero new
unused-section-variable warnings (all three world-independent lemmas carry `omit [Hashable
Atom] in`, placed BEFORE the docstring per Lean's doc-comment/command-modifier ordering rule).

**Timing**: 1.5 hours

**Depends on**: 0, 4

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; all four declarations close sorry-free.

---

### Phase 7: The counting crux [COMPLETED]

**Goal**: The load-bearing new proof. Land the linear a-priori world budget, replacing the birth-key
pigeonhole entirely.

**Completion note**: landed exactly as specified, with one documented, necessary deviation from
the literal 2-hypothesis signature: `modalStepBranchS5w_preserves_worldInv` takes
`accTargetsKnown b acc` as a THIRD hypothesis. This is required because K's own `boxPos`/
`diamondNeg` propagation shapes emit at `acc.successorsOf w`, which is unbounded by
`modalMaxWorld` without it. The `accTargetsKnown` preservation instantiation itself is a free
corollary of `modalStepBranch_preserves_accTargetsKnown_gen`, discharged via a new
`modalApplyOneS5w_fresh_local` dichotomy lemma. The per-call counting argument is centralized in
one new combined lemma, `modalApplyOneS5w_step`, which gives both the `signedSubfmls`-closure
half of `S5wTagInv`'s preservation and the known-label-or-fresh-tag-mint dichotomy `S5wWorldInv`
needs, in one pass over `modalApplyOneS5w`'s three-way dispatch (the two tag-consuming mint/reuse
shapes, the two S5-relevant propagation shapes, and the fallthrough to `modalApplyOne`). Full CI
green (`lake build`: 3239/3239); zero sorry, zero new axioms (`propext`, `Classical.choice`,
`Quot.sound` only) in the new declarations.

**Tasks**:
- [x] Land:
      ```lean
      def S5wWorldInv (φ₀) (b) : Prop := modalMaxWorld b ≤ (usedTags φ₀ b).card

      theorem modalStepBranchS5w_preserves_worldInv
          (hT : S5wTagInv φ₀ b) (hW : S5wWorldInv φ₀ b) (hK : accTargetsKnown b acc)
          (h : modalStepBranchGen modalApplyOneS5w b e acc = some (bs, es, acc')) :
          ∀ b' ∈ bs, S5wTagInv φ₀ b' ∧ S5wWorldInv φ₀ b'

      theorem modalMaxWorld_lt_worldBound_of_S5w (hW) : modalMaxWorld b < modalWorldBound φ₀
      ```
      (`modalMaxWorld_lt_worldBound_of_S5w` needed only `hW`, not `hT`, since the chain
      `modalMaxWorld b ≤ (usedTags φ₀ b).card ≤ (mintTags φ₀).card ≤ modalOps φ₀ <
      modalWorldBound φ₀` never touches `S5wTagInv` directly.)
- [x] **The argument** (recorded in the docstring): a mint fires only when
      `witnessWorldS5 b s ψ = none`, which implies `(s,ψ) ∉ usedTags φ₀ b`
      (`witnessWorldS5_none_not_mem_usedTags`; any `⟨s,ψ,w''⟩ ∈ b` puts `w''` in
      `modalKnownWorlds b`, `Branch.lean:89`, so `find?` cannot miss it). The mint **emits its own
      witness** at `w' = modalNextWorld b = modalMaxWorld b + 1` (`Rules.lean:125`,
      `Branch.lean:99`). So `modalMaxWorld` grows by 1 while `usedTags` gains `(s,ψ)` -- and since
      `b` only ever **grows**, that tag is **used forever after**, so it can never mint again.
      Mints inject into `mintTags`. Every non-mint arm leaves `modalMaxWorld` unchanged and
      `usedTags` monotone. Chain:
      `modalMaxWorld b ≤ (usedTags φ₀ b).card ≤ (mintTags φ₀).card ≤ modalOps φ₀ < modalWorldBound φ₀`.
- [x] Confirmed `modalMaxWorld_lt_worldBound_of_S5w` is the **drop-in replacement** for
      `modalMaxWorld_lt_worldBound_of_phiBound` (`CompletenessLoop.lean:775-776`) -- same conclusion,
      at K's own bound, with **no rank, no potential, no pigeonhole, no powerset, no birth keys**.
      That scalar is **all the rank ever buys** (report §2.3).

> **TRAP THE IMPLEMENTER MUST NOT STEP IN (R8 -- this is real and cost a prior design)**: a `birth`
> function must **NOT** be defined concretely as "the least world carrying the pair". S5's universal
> box can later add `⟨s,φ,w''⟩` at a **smaller** world, so that formulation is **not step-preserved**.
> The `usedTags`-cardinality formulation above sidesteps this entirely by **never naming a witness
> world**. Do not reintroduce a `birth` function.

**Timing**: 2 hours

**Depends on**: 1, 6

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**: full CI green; `lean_verify` on `modalMaxWorld_lt_worldBound_of_S5w`. Empirical
cross-check: **0 violations of `maxWorld ≤ modalOps φ` across all 3,963 corpus formulas** at
saturation on every branch (research session).

**Blocked-branch**: if the counting crux resists, mark `[BLOCKED]` with the exact open goal and
invoke fallback 1 (keep the rule, obtain the bound another way). No `sorry`.

---

### Phase 8: R1 scratch probe -- soundness re-proof feasibility [COMPLETED]

**Goal**: **GATE.** Falsify or confirm the top risk (R1) in scratch **before** committing to the
spec split and the lift refactor (Phases 9-12). The report is explicit: *"Probe it in scratch BEFORE
committing to Phase 6+, exactly as `hintikka_congr` and `diaPosWitness'` were probed this session."*
This phase writes **no** production Lean.

**Tasks**:
- [x] In scratch (`lean_run_code` / `lean_multi_attempt`; **no `.lean` file edited**), probe the new
      soundness case: the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩`. Confirm the
      world-assignment `f` is **not extended** (no mint), so the only obligation is `m.r (f w) (f w')`.
- [x] Confirm `accReachableInv_related_s5` (`FrameSoundness.lean:1381`, **landed**) discharges it:
      it states that two known worlds, both reachable from 0, are related in **any** model whose
      relation is an equivalence relation. That is exactly the obligation.
- [x] Run `lean_references` on `modalApplyOneS5_snd_eq` (`S5Simplification.lean:340-351`) to
      **enumerate its real consumers** (R4). Expected: `FrameSoundness.lean:1326` (inside
      `modalApplyOneS5_fresh_local`, which stays reusable) plus S5g/keyed sites
      (`S5Simplification.lean:1720/1868/1943/1953/2017/2025/2083`, :398) that Phase 14 retires anyway.
- [x] Estimate the re-proof size. **KILL CONDITION: if the probe indicates > ~400 lines, STOP and
      re-litigate the fork** -- invoke fallback 2 (atom-quotient semantic FMP, `[PARTIAL]`,
      deliverable 4 only).

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**: none (scratch probe only)

**Verification**: a written go/no-go with the `lean_references` output and a line estimate, recorded
in the phase completion note and the handoff JSON.

**Blocked-branch**: a no-go here is **cheap and valuable** -- it saves Phases 9-13. Record the
finding, land Phases 0-7 green, and pivot to fallback 2 as a documented `[PARTIAL]`.

#### Phase 8 completion note: **GO** verdict, measured

**1. `f` not extended -- CONFIRMED BY PROBE, structurally.** The probe's target `example`
(`specs/515_s5_universal_rule_termination_unblock_504/probes/phase8-r1-reuse-soundness.lean`) states
both reuse-case obligations purely in terms of the *original* `f` -- no `f'`, no model extension was
constructed anywhere in the proof. This is the strongest form of confirmation available: had `f`
needed extending, the statement itself would have required an existential model/assignment, and it
does not.

**2. `accReachableInv_related_s5` discharges the obligation -- CONFIRMED BY PROBE, sorry-free.**
`lean_run_code` against the real project imports (`S5Simplification.lean`, `FrameSoundness.lean`)
returned `"success":true` with **zero diagnostics on the target example** (the only two warnings
attach to an orthogonal scratch-only auxiliary lemma, see below). The obligation splits into two
parts, both closed using only already-landed lemmas:
  - `sfSat m f ⟨.pos, φ, w'⟩` -- one line, `hb _ (witnessWorldS5_mem hw)` (the witness formula is
    already on the branch, hence already satisfied by the existing IH; no new argument).
  - `m.r (f lbl) (f w')` -- one line, `accReachableInv_related_s5 hFC hacc hreach hlblknown hw'known`.
  The only auxiliary fact needed (`w' ∈ modalKnownWorlds b`, from `witnessWorldS5_mem` +
  membership-in-fold) is orthogonal plumbing already proven identically at 3+ sites in this codebase
  (`mem_modalKnownWorlds_S5`, `BDriver.lean`'s `mem_modalKnownWorlds_B`, `FmpMeasure.lean`'s
  original); the probe `sorry`'d only that re-derivation (needed solely because the probe lives
  outside `S5Simplification.lean` and can't see its `private` lemma) -- Phase 13's real
  implementation sits inside that file and calls the existing private lemma directly, no
  re-derivation required.

**3. `lean_references` on `modalApplyOneS5_snd_eq` -- run, with a documented mismatch against the
plan's expected line numbers.** `modalApplyOneS5_snd_eq` is at `S5Simplification.lean:358` (the plan
cited `:340-351`, which is actually the *preceding* lemma, `modalApplyOneS5_eq_of_not_boxPos_diaNeg`).
Actual `lean_references` output (8 real consumers, excluding the declaration site):
  - `FrameSoundness.lean:1326` -- inside `modalApplyOneS5_fresh_local`, **matches expectation**
    (stays reusable, per the plan).
  - `S5Simplification.lean:415` -- inside `modalApplyOneS5_snd_eq_acc_of_not_mint_shape` (private).
  - `S5Simplification.lean:1670` -- inside `modalApplyOneS5_fresh_local_local` (private; the
    in-file twin of the `FrameSoundness.lean` lemma above).
  - `S5Simplification.lean:3054, 3064` -- inside `modalStepBranchS5g_preserves_accFresh`.
  - `S5Simplification.lean:3128, 3136` -- inside `modalStepBranchS5g_preserves_accKnown`.
  - `S5Simplification.lean:3194` -- inside `modalStepBranchS5g_preserves_outDegEq`.
  **Mismatch**: none of the plan's expected literal line numbers
  (`1720/1868/1943/1953/2017/2025/2083`, `:398`) matched a real reference site. Root cause, confirmed
  by inspection: those numbers are stale, predating Phases 4-7's ~1,500 lines of new S5w code
  inserted into `S5Simplification.lean` since the deep-research report was written. **The taxonomy
  and count still match**: 8 total references, split exactly as predicted between (a) the reusable
  `fresh_local`-family lemmas and (b) `S5g`-prefixed (keyed/generalized-stepper) sites -- and every
  one of the `S5g` sites Phase 14 is already scheduled to retire, confirmed by name
  (`modalStepBranchS5g_preserves_{accFresh,accKnown,outDegEq}`). **No blocker**: the reference
  surface is exactly as small and exactly as retirable as the plan claimed; only the citation's line
  numbers need correcting in future artifacts.

**4. Re-proof size estimate: ~150-250 new lines, well under the 400-line kill threshold.**
Grounded in measured comparables, not guesswork:
  - `modalStepBranchS5_preserves_satIn` (`FrameSoundness.lean:1708-2221`, ~514 lines) is the direct
    analogue of what Phase 13 must build for `modalApplyOneS5w`. Of its ~514 lines, ~394 are the
    "port every other shape verbatim from K" branch (all shapes except the two S5-universal-rule
    cases) -- **unaffected by the witness-reuse change**, since `modalApplyOneS5w` only diverges
    from `modalApplyOneS5` at the two mint shapes.
  - The two mint-shape case bodies that DO change: `.pos,.diamond` (diaPos mint, lines 1901-2019,
    ~118 lines) and `.neg,.box` (boxNeg mint, lines 2090-2212, ~122 lines). Each needs a
    `cases witnessWorldS5 b s φ with` split: the `none` arm reuses the existing ~118/122-line mint
    proof **verbatim** (behind `modalApplyOneS5w_eq_of_not_mint_shape`-style reduction, ~5-10 wiring
    lines), and the `some w'` arm is **new**: probe-confirmed core content is ~4-5 lines
    (`sfSat`/`m.r` obligations), but the surrounding `RuleResultSat`/`branchSatisfiableIn` packaging
    (matching the `refine ⟨..., W, m, f, hFC, ?_, ?_⟩` shape used throughout
    `modalStepBranchS5_preserves_satIn` and `modalS5BoxAll_soundIn`, `FrameSoundness.lean:1581-1627`,
    ~47 lines) brings each reuse arm to a realistic **~30-40 lines**. Net new per case: **~40-50
    lines** (2 cases: **~80-100 lines**).
  - A new `accReachableInv`-preservation lemma is needed for `modalStepBranchGen modalApplyOneS5w`
    (the S5w analogue of the already-landed `modalStepBranchS5_preserves_accReachableInv`,
    `FrameSoundness.lean:1508`, accounting for the reuse arm's new edge between two already-known
    worlds rather than a newly-minted one). Comparable in complexity to Phase 7's already-landed
    `modalStepBranchS5w_preserves_worldInv`/`_preserves_accTargetsKnown` (each ~50-100 lines per the
    Phase 7 completion note): estimate **~50-100 lines**.
  - `modalTableauS5w_sound` itself is structurally identical to `modalTableauS5_sound`
    (`FrameSoundness.lean:2379-2404`, ~26 lines) -- near-zero new content, a rename/adapt.
  - **Total: ~80-100 (two reuse cases) + ~50-100 (new preservation lemma) + wiring ≈ 150-250 new
    lines.** This is comfortably under the ~400-line kill threshold, with the highest-risk step
    (the semantic core of the reuse-case obligation) already probe-confirmed sorry-free.

**VERDICT: GO.** Proceed to Phase 9 (spec split). `next_action_hint`: Phase 9.

---

### Phase 9: Spec split + the one-token weakening [COMPLETED]

**Goal**: Split `RuleApplicationSpec` so the Hintikka machinery no longer sees the three fields S5
cannot discharge. **Drop THREE fields, not one.**

**Tasks**:
- [ ] Land:
      ```lean
      structure RuleApplicationSpecCore (apply : RuleApply Atom) : Prop where
        freshLocal, outputsSubsetUniverse, persistentFresh, branchingLength,
        localShapeInvariance, boxPosNotExpanding, diaNegNotExpanding,
        boxNegWitness', diaPosWitness'          -- witness world EXISTENTIAL, not `modalNextWorld b`

      structure RuleApplicationSpec (apply) extends RuleApplicationSpecCore apply : Prop where
        rankStep, outDegStep, knownWorldsStep   -- the three fields S5 cannot discharge

      theorem RuleApplicationSpec.toCore (spec : RuleApplicationSpec apply) : RuleApplicationSpecCore apply
      theorem modalApplyOneS5w_specCore : RuleApplicationSpecCore (modalApplyOneS5w (Atom := Atom))
      ```
- [ ] Justify dropping **three** fields, not one (report §2.3, all VERIFIED by reading): for any rule
      that adds an edge to an **existing** world, three fields fail --
      `rankStep` (`GenericDriver.lean:213`, the landed S5 counterexample);
      `knownWorldsStep` (`GenericDriver.lean:245`, a **strict dichotomy**: either `.snd = acc` or
      `.snd = acc.addEdge sf.label (modalNextWorld b)` -- the reuse arm satisfies **neither**);
      and `rankEdge` inside `ModalPotentialInv` (`FmpMeasure.lean:2326`) -- irreparably false, since
      the saturated `□◇p` branch has a **reflexive** edge `(1,1)`, forcing `rank 1 + 1 = rank 1`.
      All three are confined to the potential/measure path; `modalStepBranchGen_knownWorlds` has
      **zero** consumers in the Tableau directory.
- [ ] The structural fact that makes this work [VERIFIED]: the spec-field usage of the five
      Hintikka-forcing lemmas (`CompletenessLoop.lean:233-760`) is
      `3 boxNegWitness, 3 boxPosNotExpanding, 3 diaNegNotExpanding, 3 diaPosWitness, 8 freshLocal,
      1 localShapeInvariance, 1 outputsSubsetUniverse` -- **no `rankStep`, no `knownWorldsStep`, no
      `outDegStep`**. Also: `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3231`) takes `apply` plus
      **three raw hypotheses** and a raw `hW : modalMaxWorld bh < modalWorldBound φ0`, mentioning
      **neither `RuleApplicationSpec` nor `rankStep`** [VERIFIED from the full signature]. **The
      measure layer never needed the rank.**
- [ ] Land `diaPosWitness'` for the witness rule. **COMPILED IN RESEARCH** sorry-free (axioms
      `[propext, Quot.sound]`), delegating the `none` arm to `modalApplyOne_diamondPos_witness`:
      ```lean
      cases h : witnessWorldS5 b .pos ψ with
      | some w' => exact ⟨w', [], by simp [modalApplyOneS5w, h], by simp [modalApplyOneS5w, h]⟩
      | none => obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
                exact ⟨modalNextWorld b, rest, by simp [...], by simp [...]⟩
      ```
- [ ] Land `boxNegWitness'` symmetrically (via `modalApplyOne_boxNeg_witness`).
- [ ] K/T/B adapters: they instantiate via `where` syntax (`GenericDriver.lean:335`,
      `TDriver.lean:847`, `BDriver.lean:821`), so `extends` keeps those blocks compiling; discharge
      the existential form with `w' := modalNextWorld b` via a 3-line adapter each. **K/T/B pay
      nothing.**

> **R6 -- WHY THE REUSE ARM MUST BE GUARD-LESS** [VERIFIED by reading `CompletenessLoop.lean:1049-1060`]:
> the conjunct-3/4 saturated-leaf discharge is an **`exfalso`** that derives a contradiction *from*
> `.notApplicable`:
> ```lean
> · exfalso
>   obtain ⟨-, rest, hlin⟩ := spec.diaPosWitness bR aR ψ' w
>   rw [hlin] at hna; simp at hna
> ```
> It consumes the **`.linear` shape**, not the witness world. A `hasEdge` guard makes
> `.notApplicable` **reachable** and **inverts this proof from a refutation into a proof obligation**.
> Guard-less keeps both `exfalso` proofs byte-identical.

**Timing**: 2.5 hours

**Depends on**: 2, 8

**Files to modify**: `Cslib/Logics/Modal/Tableau/GenericDriver.lean` (the structure split -- the one
authorized edit to this file), `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
(`modalApplyOneS5w_specCore`), plus 3-line adapters in `TDriver.lean` / `BDriver.lean` if required.

**Verification**: full CI green; **K/T/B compile with their existing `where` blocks**; `lean_verify`
on `modalApplyOneS5w_specCore`.

#### Phase 9 completion note

Landed as planned, with one scope deviation: `CompletenessLoop.lean` also required edits (6
destructuring sites for `spec.boxNegWitness`/`spec.diaPosWitness` gained an extra existential
witness-world binder after the field rename to `boxNegWitness'`/`diaPosWitness'`), even though it
wasn't in the "Files to modify" list. This is mechanical fallout of the field rename in
`RuleApplicationSpecCore`, not a design change -- `CompletenessLoop.lean`'s lemma signatures still
take the *full* `RuleApplicationSpec` (unchanged), since `modalStepGen_preserves_invariant`
(and, through it, `modalExpandBranchesGen_hintikka`) calls `modalStepBranchGen_potential_step`,
which needs `rankStep`/`outDegStep`/`knownWorldsStep` transitively. The "Hintikka machinery no
longer sees the three fields" weakening (swapping `RuleApplicationSpec` to
`RuleApplicationSpecCore` in `CompletenessLoop.lean`'s own signatures) is Phase 12's job, not
this one -- Phase 9 only lands the structural split plus the `modalApplyOneS5w_specCore` Core
witness.

Verified: **K/T/B pay nothing** -- `modalApplyOneT_spec`/`modalApplyOneB_spec`'s `where` blocks
needed only the 3-line existential-wrapping adapter for `boxNegWitness'`/`diaPosWitness'`, no
other change. `lean_verify` on `modalApplyOneS5w_specCore` reports axioms
`[propext, Classical.choice, Quot.sound]` -- identical to the existing `modalApplyOneT_spec`/
`modalApplyOneB_spec` baseline, no new axioms. Full CI green: `lake build` (3239/3239),
`checkInitImports`, `lake lint` (only the pre-existing, out-of-scope `PrimeExclusion.lean` error),
`lake exe lint-style` (clean), `lake test` (9230 jobs, only pre-existing unrelated sorries),
`lake shake` (no new suggestions for any of the five touched files). Zero sorry, zero new axioms,
zero vacuous definitions in the touched files.

The nine `RuleApplicationSpecCore` fields for `modalApplyOneS5w` required substantially more new
proof content than the plan's task list detailed (which only fully specified `diaPosWitness'`/
`boxNegWitness'`): `outputsSubsetUniverse`, `persistentFresh`, `branchingLength`,
`localShapeInvariance`, `boxPosNotExpanding`, `diaNegNotExpanding` all needed fresh lemmas built
on the two-layer agreement chain (`modalApplyOneS5w_eq_of_not_mint_shape` /
`modalApplyOneS5_eq_of_not_boxPos_diaNeg`) plus new local re-derivations of `mem_modalUniverse_of`/
`modalUniverse_mem_formula` (private in `FmpMeasure.lean`, hence re-derived locally, matching this
file's existing `_S5`/`_S5w`-suffixed re-derivation pattern) and a new hypothesis-free combined
F9/F10 shape fact `modalApplyOneS5_boxPos_diaNeg_shape`.

---

### Phase 10: Rank-free loop invariant with the `Aux` parametrization [COMPLETED]

**Correction (post-audit, see `reports/06_k-aux-unprovability-audit.md`)**: this phase's original
verification bar -- "both `Aux` instantiations elaborate" -- was too weak. Elaboration is not
satisfiability: `ModalLoopAuxK` elaborated but was not step-preservable, and
`ModalLoopInvGen_iff_hintikka_auxK` gave false assurance precisely because it is stated at a
single fixed `(b, e, acc)` and never exercises a step, which is exactly where the frozen-`e`
defect bites. **Strengthened bar going forward**: both `Aux` instantiations must have closed
`AuxStepPreserved` **and** `AuxBounds` witnesses, not merely elaborate. Phase 11.5 (below) closes
this gap by re-aritying `Aux` to thread `e`; Phase 10's declarations as landed are otherwise
sound and are re-aritied in place, not replaced.

**Re-marked `[COMPLETED]` (post-Phase-11.5, this dispatch)**: the strengthened bar above is now
met. Confirmed directly against the landed Lean: `ModalLoopAuxK_bounds`,
`ModalLoopAuxS5w_bounds`, `ModalLoopAuxK_stepPreserved`, and `ModalLoopAuxS5w_stepPreserved` are
all closed, sorry-free (`grep sorry` clean), and axiom-checked via `lean_verify` to use only
`propext`/`Classical.choice`/`Quot.sound` (K's `_bounds` uses only `propext`/`Quot.sound`) -- no
new axioms. The bar was met via Phase 11.5's re-arity correction, not as originally landed here;
this note documents that provenance rather than erasing the `[PARTIAL]` history above.

**Goal**: Land the rank-free Hintikka loop invariant. **This is real work, not a rename.**

**Tasks**:
- [x] Landed `ModalLoopInvHintikka (apply) (φ0) (Aux) (b e) (acc) : Prop` with `bClosure`,
      `eClosure`, `eNodup`, `accFresh`, `accKnown` (from `ModalPotentialInv`, rank-free), an
      opaque `aux : Aux b acc` field (replacing `potentialInv`/`phiBound`), and `hintikkaInv`,
      `eBoxOnlyNeg`, `eBoxNegWitness`, `eDiamondOnlyPos`, `eDiamondPosWitness`
      (`CompletenessLoop.lean`, after `modalMaxWorld_lt_worldBound_of_phiBound`).
- [x] **The honest hazard, and the fix -- landed as specified.** Did **not** land a bare
      `worldBound` scalar. Landed `Aux : List (SignedFormula (Proposition Atom) WorldIndex) →
      Accessibility → Prop` as an explicit structure parameter, plus the two standalone
      obligations `AuxStepPreserved apply Aux` (takes `accFreshInv`/`accTargetsKnown` as
      additional ambient hypotheses alongside `Aux b acc`, matching S5w's documented
      third-hypothesis deviation) and `AuxBounds φ0 Aux` (`Aux b acc → modalMaxWorld b <
      modalWorldBound φ0`). K instantiates `ModalLoopAuxK φ0 e b acc := ∃ rank,
      ModalPotentialInv φ0 b e acc rank ∧ phiBound`-statement; S5w instantiates
      `ModalLoopAuxS5w φ₀ b _acc := S5wTagInv φ₀ b ∧ S5wWorldInv φ₀ b`. Both `AuxBounds`
      instances are proved outright (`ModalLoopAuxK_bounds`, `ModalLoopAuxS5w_bounds`), and
      S5w's `AuxStepPreserved` is proved outright too (`ModalLoopAuxS5w_stepPreserved`, a direct
      corollary of the landed `modalStepBranchS5w_preserves_worldInv`) -- K's `AuxStepPreserved`
      is left to the step-preservation port (next phase), as scoped.
- [x] Note for sizing (R3) -- confirmed exactly as documented: `ModalLoopInvGen` has **7** fields
      parametrized by `(rank : WorldIndex → Nat)`; the flat five-field list (`bClosure`,
      `eClosure`, `eNodup`, `accFresh`, `accKnown`) lives inside `ModalPotentialInv`, and is what
      `ModalLoopInvHintikka` promotes directly. `outDegEq`/`rankBound`/`rankEdge` (the genuinely
      rank-dependent remainder) live only inside K's `ModalLoopAuxK` instantiation. Proved the
      full bridge `ModalLoopInvGen_iff_hintikka_auxK : (∃ rank, ModalLoopInvGen apply φ0 b e acc
      rank) ↔ ModalLoopInvHintikka apply φ0 (ModalLoopAuxK φ0 e) b e acc` confirming the arity
      change is sound, not merely a field swap.
- [x] `hintikkaInv`'s cheapness for the witness rule was not separately re-verified in this
      phase (no new proof needed it yet); the field is carried unchanged from `ModalLoopInvGen`
      into `ModalLoopInvHintikka`.

**Timing**: 2 hours

**Depends on**: 7, 9

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green; the structure typechecks; both `Aux` instantiations elaborate.

---

### Phase 11: Step preservation [COMPLETED]

**Correction (post-audit, see `reports/06_k-aux-unprovability-audit.md`)**: this phase's own
verification bar reads *"the port closes sorry-free at **both** `Aux` instantiations."* It met
one of two (S5w). A phase that meets half its stated bar is `[PARTIAL]`, not `[COMPLETED]`. The
self-assessment below ("documented, not a blocker for this phase") under-stated the defect: the
audit machine-checked that `AuxStepPreserved modalApplyOne (ModalLoopAuxK φ0 [])` is not merely
unproven but **refutable** (`auxK_not_stepPreserved`, sorry-free, `#print axioms` ->
`[propext, Quot.sound]`), and that the finding's own stated mechanism ("frozen `e` and step's `e`
diverge") is wrong -- the audit's counterexample sets them equal and the statement is still
false. The real defect, and its fix, are Phase 11.5's (below), not this phase's remit; this
phase's generic `modalStepHintikka_preserves_inv` port itself was correct and is unchanged.

**Re-marked `[COMPLETED]` (post-Phase-11.5, this dispatch)**: the phase's own bar -- "the port
closes sorry-free at both `Aux` instantiations" -- is now met at both K and S5w. Confirmed
directly against the landed Lean: `ModalLoopAuxK_stepPreserved` (generic over any `apply` with a
full `RuleApplicationSpec`) and `ModalLoopAuxS5w_stepPreserved` are both closed, sorry-free, and
axiom-checked to use only `propext`/`Classical.choice`/`Quot.sound`. This was closed by Phase
11.5's `Aux` re-arity (threading `e`), not by a change to this phase's own
`modalStepHintikka_preserves_inv` port, which was correct all along per the Finding below.

**Goal**: Port `modalStepGen_preserves_invariant` to the rank-free invariant with `Aux` threaded.

**Tasks**:
- [x] Landed:
      ```lean
      lemma modalStepHintikka_preserves_inv (apply) (hs : RuleApplicationSpecCore apply) (φ0)
          (Aux) (hAuxStep : AuxStepPreserved apply Aux) (hAuxBounds : AuxBounds φ0 Aux) ... :
        (∀ p ∈ newBs.zip newExps, ModalLoopInvHintikka apply φ0 Aux p.1 p.2 newAcc) ∧ measure-drop
      ```
      (`CompletenessLoop.lean`, immediately before "The Combined-Invariant Single-Step
      Preservation Lemma" section).
- [x] Port of `modalStepGen_preserves_invariant` (located by name, not the stale line citation)
      **minus the two `potential_step` lines** (the existential rank witness and the `phiBound`
      re-derivation), with `Aux` threaded via `hAuxStep`/`hAuxBounds` in their place. The five
      rule-dependent helpers it composes (`modalLoopGen_bClosure`, `_eBoxOnlyNeg`,
      `_eDiamondOnlyPos`, `_eBoxNegWitness`, `_eDiamondPosWitness`) are declared against the full
      `RuleApplicationSpec` even though each proof body only ever touches a Core field; rather
      than weaken those five declarations in place (explicitly Phase 12's remit per this plan's
      own scoping note), landed five purely-additive `_core`-suffixed twins (identical proof
      bodies, parametrized over `RuleApplicationSpecCore`) and used those instead. The other four
      preservation facts needed (`accFreshInv`, `accTargetsKnown`, `eNodup`, `eClosure`,
      hintikka-inv) already had raw, Core-compatible underlying lemmas taking field hypotheses
      directly (not a bundled spec) -- no new plumbing needed there.
- [x] Consumed `modalExpMeasure_step_lt_gen` (located by name; stale line citation) directly for
      the measure drop: `apply` + `hs.branchingLength`/`hs.persistentFresh`/
      `hs.outputsSubsetUniverse` (all three Core fields) + `hW : modalMaxWorld bh <
      modalWorldBound φ0` -- supplied by `hAuxBounds b acc haux` at S5w's instantiation via the
      landed `modalMaxWorld_lt_worldBound_of_S5w` (Phase 7). **No rank.** Bypassed the
      full-spec-typed `modalStepBranchGen_expMeasure_step_lt` wrapper entirely.
- [x] Landed `modalStepHintikka_preserves_inv_S5w`, a concrete corollary instantiating the generic
      lemma at `Aux := ModalLoopAuxS5w φ0` (using the already-landed `modalApplyOneS5w_specCore`,
      `ModalLoopAuxS5w_stepPreserved`, `ModalLoopAuxS5w_bounds`), demonstrating the S5w half of
      the verification bar concretely, sorry-free.

**Finding (documented, not a blocker for this phase)**: the K-side half of the verification bar
("closes sorry-free at both `Aux` instantiations") cannot be satisfied by a *closed*
`AuxStepPreserved modalApplyOne (ModalLoopAuxK φ0 e)` term, for a genuine mathematical reason, not
a missing tactic: `ModalLoopAuxK`'s `outDegEq` conjunct is stated against a **frozen** `e`
(`ModalLoopAuxK` must close over a fixed `e` to fit `Aux`'s bare `b → acc → Prop` type), but
`AuxStepPreserved`'s own step hypothesis is universally quantified over an independent, per-call
`e`. A step that mints a new edge changes `outDeg` against the step's own *current* expanded set,
not against `ModalLoopAuxK`'s frozen `e` -- so whenever the frozen `e` and the step's actual `e`
diverge, the post-state conjunct is false (concrete counterexample: an empty frozen `e0 := []`
together with any `boxNeg`/`diamondPos`-shaped step that mints an edge). This is architecture
work for Phase 12's parametric Hintikka lift (which will need to thread the current `e` through
K's instantiation explicitly, rather than freezing it inside `Aux`), not a Phase 11 port defect --
`modalStepHintikka_preserves_inv` itself is fully generic and sorry-free for **any** `Aux`
genuinely satisfying `AuxStepPreserved`/`AuxBounds` (as S5w's does).

**Timing**: 2 hours

**Depends on**: 10

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green (build, `checkInitImports`, `lint-style`, `lint` [pre-existing
`PrimeExclusion.lean` error only, out of scope], `test`, `shake`); the port closes sorry-free;
zero new axioms (`propext`/`Classical.choice`/`Quot.sound` only); confirmed sorry-free at S5w's
`Aux` instantiation concretely; K's instantiation genuinely requires Phase 12 architecture (see
Finding above), not a gap in this phase's port.

---

### Phase 11.5: `Aux` re-arity -- thread `e` (audit-inserted) [COMPLETED]

**Goal**: Close the K-side half of Phase 11's original verification bar by re-aritying `Aux` to
thread the expanded set `e` explicitly, per the verified fix in
`reports/06_k-aux-unprovability-audit.md` §5. Re-arity only -- the design is settled and
machine-checked by the audit, not re-derived here.

**Tasks**:
- [x] Re-arity `AuxStepPreserved (apply) (Aux)` (`CompletenessLoop.lean`): `Aux` now has type
      `List (SignedFormula …) → List (SignedFormula …) → Accessibility → Prop` (was
      `List (SignedFormula …) → Accessibility → Prop`); the step hypothesis becomes `Aux b e acc`
      (was `Aux b acc`); the conclusion becomes `∀ p ∈ newBs.zip newExps, Aux p.1 p.2 newAcc`
      (was `∀ b' ∈ newBs, Aux b' newAcc`), pairing each new branch with its own new expanded set.
- [x] Re-arity `AuxBounds (φ0) (Aux)` to the same `Aux` type; `Aux b e acc → modalMaxWorld b <
      modalWorldBound φ0` (was `Aux b acc → …`).
- [x] Re-arity `ModalLoopInvHintikka.aux : Aux b e acc` (was `Aux b acc`) -- the structure's own
      `e` parameter was already in scope, so this is a one-line field-type change.
- [x] Re-arity `ModalLoopAuxK (φ0) (b e) (acc)` (was the curried `ModalLoopAuxK (φ0) (e) (b) (acc)`)
      -- body unchanged, only the parameter order/currying changes to match `Aux`'s shared shape.
- [x] Re-arity `ModalLoopAuxS5w (φ₀) (b _e) (_acc)` (was `(φ₀) (b) (_acc)`, no `e` at all) --
      body unchanged; `_e` genuinely unused, covered by the existing `@[nolint unusedArguments]`.
- [x] Re-land `ModalLoopAuxK_bounds`, `ModalLoopInvGen_iff_hintikka_auxK`, `ModalLoopAuxS5w_bounds`
      against the new arities -- all mechanical, proof bodies unchanged apart from binder shape.
- [x] Re-land `ModalLoopAuxS5w_stepPreserved`: one token, `(List.of_mem_zip hp).1` replaces the
      prior direct `hb'` membership; nothing else changes.
- [x] Adjust `modalStepHintikka_preserves_inv`'s body: `hAuxBounds b e acc haux` (added `e`),
      `hAuxAll : ∀ p ∈ newBs.zip newExps, Aux p.1 p.2 newAcc` (was `∀ b' ∈ newBs, …`), and the
      final `refine`'s aux-field call site becomes `hAuxAll p hp` (was `hAuxAll p.1 hp1`) -- the
      `refine`'s own `p`/`hp` destructuring via `List.of_mem_zip` was already in place from Phase 11
      and needed no other change.
- [x] Land **NEW** `ModalLoopAuxK_stepPreserved (apply) (spec : RuleApplicationSpec apply) (φ0) :
      AuxStepPreserved apply (ModalLoopAuxK φ0)`, generic over any `apply` with a full
      `RuleApplicationSpec` (K, T, B all get it from one theorem -- the "K/T/B pay nothing"
      guarantee, actually delivered). Discharged per audit §5: `modalStepBranch_potential_step_gen`
      for the rank witness and `rankBound`/`rankEdge`/`phiBound`-conservation; the five
      `_core`-suffixed helpers from Phase 11 (via `spec.toCore`) for `bClosure`/`eNodup`/
      `eClosure`/`accFresh`/`accKnown`; the crux, `modalStepBranch_preserves_outDegEq_gen`, applied
      at `p.2` (the branch's own new `e`), not a frozen `e`.
- [x] Verified the one residual line the audit flagged (`modalLoopGen_bClosure_core`, `private` in
      this file, so the audit's out-of-file probe supplied it as a hypothesis): in-file it is
      discharged directly via `spec.toCore`, exactly as Phase 11's port already does at the same
      position. Closes with no additional machinery.

**Timing**: 1 hour (audit estimated ~60 lines / mechanical; actual diff: 100 insertions, 46
deletions, entirely within `CompletenessLoop.lean`)

**Depends on**: 11 (and the audit report, `reports/06_k-aux-unprovability-audit.md`)

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green (`lake build`, `checkInitImports`, `lint-style`, `lint`
[pre-existing `PrimeExclusion.lean` error only, out of scope], `test`, `shake` -- all six
confirmed); **closed `AuxStepPreserved` witness at BOTH instantiations** (`ModalLoopAuxK_bounds`
+ `ModalLoopAuxK_stepPreserved` for K, `ModalLoopAuxS5w_bounds` +
`ModalLoopAuxS5w_stepPreserved` for S5w) -- Phase 11's original bar, now met; zero `sorry`; zero
new axioms (`lean_verify` on `ModalLoopAuxK_stepPreserved`, `ModalLoopAuxS5w_stepPreserved`, and
`modalStepHintikka_preserves_inv` all report `propext`/`Classical.choice`/`Quot.sound` only, no
`sorryAx`); `TDriver.lean`/`BDriver.lean` compile unmodified (confirmed via `lake test`, since
neither file consumes `Aux`/`ModalLoopAuxK`/`AuxStepPreserved` directly -- they consume
`ModalLoopInvGen`, which this phase does not touch).

---

### Phase 12: The parametric Hintikka lift + the K/T/B REGRESSION GATE [COMPLETED]

**Note (post-audit)**: Phase 11.5 (above) closed the K-side `AuxStepPreserved`/`AuxBounds` gap
this phase's own KILL (R3) gate would otherwise have hit **after** the ~310-line double
induction below, per `reports/06_k-aux-unprovability-audit.md` §1/§4. Both `Aux` instantiations
now have closed step-preservation and bounds witnesses; this phase can proceed on that
foundation rather than rediscovering the arity defect mid-induction.

**Goal**: The big one. Re-derive the lift parametrically and **prove the factoring correct by
re-deriving K's own theorem from it, unchanged**. ~310 lines, a **double induction**.

**AUTHORIZED TO SPLIT ACROSS TWO DISPATCHES** (12a: the parametric lift; 12b: the K re-derivation +
regression gate). Do **not** compress this into one run if the first does not close -- plan v2's
Phase 8 failed exactly by being budgeted as one unit.

**Tasks**:
- [x] (12a) Land:
      ```lean
      theorem modalExpandBranchesHintikka (hs : RuleApplicationSpecCore apply) (hAux …) … :
        modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
        modalHintikkaSetGen apply bR aR
      ```
      Port of `modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean:876-1185`, ~310 lines, a
      double induction). **LANDED** (333 lines, commit `ecfa123e`). Recovered from the crashed
      session's uncommitted draft, which was found to compile as-authored; this dispatch verified
      it (852/852, `lean_verify`: `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`) and
      stripped ephemeral task-number citations from its docstring/comments per the deliverables
      rule.
- [x] (12b) **REGRESSION GATE -- non-negotiable**: re-derive
      ```lean
      theorem modalExpandBranchesGen_hintikka (…)   -- K-facing name/statement UNCHANGED
      ```
      from the parametric lift at `Aux := (∃ rank, …)`. `TDriver.lean:911` and `BDriver.lean:871`
      consume it **by name** with `∃ rank, ModalLoopInvGen …` in the hypothesis. Both files must
      compile **unmodified**. **GATE PASSED** (commit `4e6b9a98`). Re-derived at
      `Aux := ModalLoopAuxK φ0` as a 7-line corollary, deleting the ~290-line double induction it
      duplicated (net -287 lines). Gate verified honest, not merely green: the K statement is
      **byte-identical** to the prior revision (extracted + `diff`ed signature, empty), and
      `TDriver.lean`/`BDriver.lean` are **unmodified** (`git status` empty) and both compile
      (`lake test` exit 0). Bridges: `spec.toCore` (weakens `RuleApplicationSpec` to
      `...SpecCore`), `ModalLoopAuxK_stepPreserved`/`_bounds` (the `Aux` obligations, landed in
      11.5), and `ModalLoopInvGen_iff_hintikka_auxK` (per-index hypothesis conversion).
- [x] **KILL (R3)**: **NOT TRIGGERED** -- the re-derivation went through with the K-facing
      statement unchanged, so the factoring is validated and the KILL gate does not fire. The lift
      is confirmed faithful to the K contract; Phase 14 is unblocked on this axis. (Phase 11.5's
      `Aux` re-arity is what made this pass: the audit predicted the curried-`e` shape would fail
      here, and the crux was `modalStepBranch_preserves_outDegEq_gen` landing at the branch's own
      new `e`.)

**Timing**: 3 hours (may require two dispatches)

**Depends on**: 11

**Files to modify**: `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean`

**Verification**: full CI green; **`TDriver.lean` and `BDriver.lean` unmodified and compiling**;
`modalExpandBranchesGen_hintikka` retains its exact name and statement; `lean_verify` on both
theorems.

**Blocked-branch**: `[BLOCKED]` with the exact `lean_goal` open state at the failing induction step.
No `sorry`. Do not weaken the K-facing statement to make the gate pass -- that defeats its purpose.

---

### Phase 13: Soundness re-proof -- `modalTableauS5_sound` [COMPLETED]

**Goal**: Re-prove S5 soundness against the witness rule. **Statement unchanged.** This is R1, the
top risk, and the largest un-costed item of the prior effort. **Forks after Phase 8's probe and runs
parallel to the 9→12 lift chain.**

**Tasks**:
- [x] Land `theorem modalTableauS5_sound (φ) (h : modalTableauS5 φ = .closed) : s5Valid φ` --
      **STATEMENT UNCHANGED**. Verified byte-identical against `git show 4e6b9a98`; the only diff
      is the proof delimiter (`:= by` -> `:=`), since it is now a term-mode corollary of the new
      lift `modalTableauS5Gen_sound`. The witness-rule terminus `modalTableauS5w_sound`
      (over `modalTableauGen modalApplyOneS5w φ`) is delivered alongside it, so Phase 14's
      one-line re-base carries the capstone over by definitional unfolding.
- [x] The new case is the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩`.
      Structurally **easier** than the landed mint case: the world-assignment `f` is **not extended**
      (no mint), so the only obligation is `m.r (f w) (f w')` for an existing `w'`.
- [x] **The decisive reuse**: `accReachableInv_related_s5` -- **landed** --
      states that two known worlds, both reachable from 0, are related in **any** model whose relation
      is an equivalence relation. That is exactly the obligation. Consume the Phase 8 probe's findings
      verbatim.
- [x] **Known breakage**: *(deviation: skipped -- premise factually incorrect; no work exists)*
      `modalApplyOneS5_snd_eq` does **not** become false: it is a statement about
      `modalApplyOneS5`, which the witness rule does not modify. It remains true and all 14 of
      its consumers still compile untouched. What the plan anticipated is that its *`w`-analogue*
      would be false -- and indeed no `modalApplyOneS5w_snd_eq` was ever stated, because the
      landed `modalApplyOneS5w_fresh_local` proves the needed dichotomy directly: the reuse arm
      satisfies the dichotomy's **right** disjunct (`.linear (wsf :: rest)` with `rest := []`,
      edge `sf.label → wsf.label`), never the `snd = acc` left disjunct. So there was no
      restatement to make and no consumer to fix. `S5Simplification.lean` was **not modified**.
      Original task text: restate `modalApplyOneS5_snd_eq` (`S5Simplification.lean:340-351`,
      *"accessibility output is unconditionally identical to K's"*) -- it becomes **false** under the
      witness rule. Use Phase 8's `lean_references` enumeration (R4) to fix each real consumer.
      `modalApplyOneS5_fresh_local` (`FrameSoundness.lean:~1326`) stays reusable -- the witness rule
      is **defeq** to `modalApplyOneS5` on all 12 non-mint arms.
- [x] Reuse the landed `S5SoundInv`, `modalStepBranchS5_preserves_satIn`,
      `modalExpandBranchesS5_closed_unsatIn`, `modalS5BoxAll_soundIn`, `modalS5DiaNegAll_soundIn`,
      `accReachableInv` (+`_initial`), `modalStepBranchS5_preserves_accReachableInv`,
      `reachable_imp_related_s5` (all `FrameSoundness.lean`, landed CI-green by v2's Phase 7)
      wherever the witness rule is defeq to `modalApplyOneS5`.
- [x] **KILL CONDITION NOT TRIGGERED**: re-proof measured at **+282/-47 = 235 net lines** in a
      single file, against the ~400 budget. The saving came from lifting the three landed S5
      soundness theorems over an abstract rule constrained by a new per-call contract
      `S5SoundSpec` (agree-with-`modalApplyOneS5` **or** fire a witness reuse), rather than
      duplicating them: the reuse arm itself is ~20 lines, and every original S5 statement
      returns as a free corollary at `Or.inl rfl`. Same architecture as Phase 12's parametric
      lift + regression corollary.

**Timing**: 3 hours

**Depends on**: 8 (and 1)

**Files modified**: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` **only**.
`S5Simplification.lean` was NOT modified -- the `modalApplyOneS5_snd_eq` restatement it was
predicted to need turned out to be moot (see the Known-breakage task above).

**Verification**: full CI green; `lean_verify` on `modalTableauS5_sound` (expect
`propext`/`Classical.choice`/`Quot.sound` only); **zero edits to any K/T/B/S4 declaration**.

**Blocked-branch**: `[BLOCKED]` with the exact open goal + the measured line count. Invoke fallback 2
(atom-quotient semantic FMP -> `Decidable (s5Valid φ)` only, documented `[PARTIAL]`). No `sorry`.

---

### Phase 14: S5 assembly, ARCHIVAL, CI, regression test [COMPLETED]

**Goal**: Re-base the shipped surface on the witness rule, deliver the S5 capstone, and **archive**
the superseded code out of the CI-built tree.

> **ARCHIVAL, NOT DELETION -- user decision, explicit and binding**: *"Code should be archived not
> deleted."* The ~2,000 superseded lines are **moved to an archive location**, never destroyed. v3
> specified demolition; that is overridden here. Every retired block stays readable at a stable path
> with a provenance header.

**Tasks**:
- [x] Re-base the surface (**one line**):
      ```lean
      def modalTableauS5 (φ) : ModalTableauResult Atom := modalTableauGen modalApplyOneS5w φ
      ```
- [x] Land `theorem modalTableauS5_complete (φ) (h : s5Valid φ) : modalTableauS5 φ = .closed`, from
      the Phase 12 lift + `hintikka_congr` (Phase 2) + `modalOpenBranchS5_countermodel` (landed) +
      Phase 5's `hTgt`.
- [x] Land `instance instDecidableS5Valid (φ) : Decidable (s5Valid φ)`, mirroring `instDecidableTValid`
      (`FrameCompleteness.lean:1281`).
- [x] **ARCHIVAL** -- **move** the ~2,000 superseded lines per the Preserved-Assets Accounting table
      above **out of the CI-built `Cslib/` tree** and into the archive path below. **Never `rm` a
      block without first confirming it exists at its archive path.** Blocks to move:
      `modalWorldBoundS5`/`modalUniverseS5` + lemmas (:60-204); `blockingWorldS5`,
      `successorBirthContentS5`, `modalApplyOneS5g` (:888-1051); `blockingWorldS5Keyed`,
      `modalStepBranchS5gKeyed` (:1424-1549); `S5LoopInv` + the ~11 `modalStepBranchS5g_preserves_*`
      (:1566-2723); `modalKnownWorlds_length_le_worldBoundS5`, `S5LoopInv.worldBound` (:2724-2830).
      **KEEP IN THE LIVE TREE** `modalApplyOneS5_rankStep_not_dischargeable` (:2995) and the Phase 3
      refutation sibling -- these are landed *documentation of dead routes*, still doing active work.

- [x] **Archive convention (CONCRETE -- follow exactly)**. Archive root:
      **`specs/515_s5_universal_rule_termination_unblock_504/archive/`**, one file per retired
      cluster:
      - `archive/01_universe-s5-worldbound.lean` (:60-204)
      - `archive/02_unkeyed-guard-s5g.lean` (:888-1051)
      - `archive/03_keyed-guard-stepper.lean` (:1424-1549)
      - `archive/04_s5loopinv-preservation.lean` (:1566-2723)
      - `archive/05_birthkey-pigeonhole-worldbound.lean` (:2724-2830)

      **Why this path, and why it follows existing repo precedent** [VERIFIED]: this repo already
      keeps task-scoped `.lean` files under `specs/{NNN}_{SLUG}/` -- `probes/` holds live probes
      across tasks 508, 509, 512, 515, 517, and `specs/301_temporal_tableau/.wip-Soundness.lean` /
      `.wip-Completeness-truthlemma-attempt.lean` are **retired WIP Lean kept beside their task**.
      `archive/` is the same convention, named for retirement rather than experiment. There is **no
      pre-existing `archive/` directory for Lean code** (`specs/archive/` is the task-archival
      directory for completed *task dirs*, an unrelated mechanism -- **do not put code there**), so
      this phase establishes the convention. **Check `git log` for any archival precedent landed
      between this plan and execution and follow it instead if one exists.**

- [x] **Provenance header on every archived block** -- required, one per block:
      ```
      -- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:{FIRST}-{LAST}
      -- Retired: {ISO date}, task 515 phase 14 (plan v4)
      -- Superseded by: {the replacing declaration(s) and their file}
      -- Why retired: {one-line reason from the Preserved-Assets Accounting table}
      -- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
      ```
      Example for `03_keyed-guard-stepper.lean`: *Superseded by*: `modalApplyOneS5w` +
      `modalMaxWorld_lt_worldBound_of_S5w` (`S5Simplification.lean`); *Why retired*: correct
      (0/700 differential errors) but **no driver runs it**, and `modalExpMeasure_step_lt_gen` is
      stated for `modalStepBranchGen`, so a keyed driver could consume neither the measure engine nor
      `modalExpandBranchesGen_hintikka`. **Retired on cost, not correctness.**

- [x] **Archived files are NOT built and NOT imported.** They carry no `import Cslib.Init`, are not
      added to `Cslib.lean`, and live outside `Cslib/` -- so `checkInitImports`, `mk_all`, and
      `lake build` never see them. This is the point: superseded code in the built tree **rots**.
      Note the archived blocks will **not compile as-is** once lifted out of context; that is
      expected and acceptable for an archive, and the provenance header's `git` coordinates are the
      authoritative way to recover a compiling version. State this in each header.

- [x] **CI must stay green with the code out of the tree** -- confirm explicitly, as a phase task,
      not as an afterthought: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake lint`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`. `shake` in
      particular may now report newly-unused imports in `S5Simplification.lean` once ~2,000 lines
      leave; action those. Expect `S5Simplification.lean` at ~1,000 lines afterwards.
- [x] Confirm the Phase 3 docstring corrections survived the archival (:40-45, :1071-1073,
      `FrameCompleteness.lean:571-580`) -- line numbers will have shifted; re-locate by content.
- [x] Land a `#eval`-backed **regression test** in `CslibTests`: the exact S5 oracle from the research
      session (3,963-formula corpus, depth 2 over `{p,q,⊥}`). **The cheapest correctness net available
      and route-independent** (R5). *(deviation: altered -- hosted in `probes/s5-decision-regression.lean`
      (run via `lake env lean`), NOT `CslibTests`, and a curated 14-check corpus rather than the 3,963
      generator, which was an ephemeral research scratch never landed as a reusable artifact. Reason:
      every file reachable from the `CslibTests` `module` barrel must itself be a `module`, and the
      `Cslib` lib is not built with `precompileModules := true`, so a `module`-mode `#guard`/`#eval` of
      the tableau fails to link native symbols (`modalFuel._redArg`). The non-`module` probe executes
      cleanly (exit 0, all 14 checks pass) and matches the repo's existing task-scoped probe convention.
      Correctness is anyway established by `modalTableauS5_sound`/`modalTableauS5_complete`; per R5 the
      corpus is only the safety net, not the proof.)*
- [x] BibKey docstrings: **Gore1999** (`references.bib:987`, **cite by TR pagination**) for the
      divergence prediction (TR p.48) and the linear model graph (TR pp.44-45, `|W| = 1 + m`);
      **Blackburn2001** (`references.bib:65`) §6.6 p.382 for the `m+1` selection-of-points bound and
      S5's NP-completeness. *(Note: Blackburn Ex. 6.6.4 is left as an exercise -- it attests the
      architecture, it is not formalizable as-is. Do not cite Ladner 1977: the local PDF is a
      919-byte HTML error page.)*
- [x] Full CI: `lake build` / `test` / `checkInitImports` / `lint-style` / `shake`.

> **NEVER ARCHIVE AHEAD OF THE REPLACEMENT.** Archival runs **LAST** in the S5 chain, only after the
> replacement chain (Phases 1-13) is green. If this plan lands `[PARTIAL]` before Phase 14, the
> superseded code simply **stays where it is** -- inert, in place, and harmless. This is v3's
> sequencing rule, reworded for the archival contract and unchanged in substance. **Archival is a
> move, so it is cheaply reversible even if performed in error** -- but the sequencing still holds:
> do not disturb code whose replacement is not yet green.

**Timing**: 3 hours (was 2 in v3; archival with per-block provenance headers and a `shake` re-run
costs more than `rm` did -- budgeted honestly rather than inherited)

**Depends on**: 3, 5, 12, 13

**Files to modify**: `Cslib/Logics/Modal/Tableau/S5Simplification.lean`,
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`, `CslibTests/`,
`specs/515_s5_universal_rule_termination_unblock_504/archive/` (new)

**Verification**: full CI green **with the archived code out of the tree** (`lake build`,
`checkInitImports`, `lint-style`, `lint`, `test`, `shake` -- all six, explicitly);
`lean_verify` on `modalTableauS5_complete` and `instDecidableS5Valid`; `instDecidableS5Valid`
typechecks **and evaluates**; no `RuleApplicationSpec modalApplyOneS5` witness reintroduced; no rank
axiom; `S5Simplification.lean` down to ~1,000 lines; **every archived block present at its archive
path with a complete provenance header, and `git status` showing the archive files as ADDED (not
just deletions)** -- a diff that only removes lines is a demolition, and is a phase failure.

---

### Phase 15: GATE -- Euclidean route feasibility probe (rooted normal form + `EuclGen` shape) [COMPLETED]

**GATE VERDICT: PASSED (go).** All three load-bearing claims confirm in scratch. Probe:
`probes/phase15-euclidean-route-gate.lean` (run via `lake env lean`, exit 0, zero `sorry`; all six
theorems report only the standard `[propext, Classical.choice, Quot.sound]` axiom subset --
`instRightEuclideanEuclGen`, `euclGen_least`, `rooted_cluster_universal`, and
`kb5_root_reflexive_if_has_succ` depend on **no** axioms at all; `rooted_cluster_isEquiv` uses only
`Classical.choice`; `kb5_per` uses only `propext`/`Quot.sound`).

- **(a) CONFIRMED**: `EuclGen` (inductive `base`/`eucl`) is right-Euclidean directly via the `eucl`
  constructor (`instRightEuclideanEuclGen`), embeds `r` (`euclGen_mono`), and satisfies the **least
  property** `[RightEuclidean s] → (∀ a b, r a b → s a b) → EuclGen r a b → s a b` by induction on
  `EuclGen` (`euclGen_least`, no axioms). Warrant recorded: Euclideanness is closed under arbitrary
  intersection and the full relation is Euclidean, so the least Euclidean relation containing `r`
  exists; `EuclGen` is its inductive realization and `euclGen_least` is that characterization.
- **(b) CONFIRMED**: rooted normal form `R(w) × R(w) ⊆ R` is literally `rightEuclidean` at the root
  (`rooted_cluster_universal`, no axioms). The landed `RightEuclidean.equiv_cod : IsEquiv (cod r) r`
  is consumed directly (`rooted_cluster_isEquiv`) -- the single biggest cost reducer applies as
  claimed; no re-derivation needed.
- **(c) CONFIRMED**: symmetric + right-Euclidean is a PER -- `kb5_per` derives `IsTrans` via the
  landed `symm_rightEuclidean_iff_trans`. The dichotomy's non-trivial branch (a rooted KB5 frame
  with any root successor is a full cluster containing the root) is witnessed by
  `kb5_root_reflexive_if_has_succ` (root has a successor ⟹ `r w w`, no axioms); the alternative is
  the edge-isolated root, which is exactly why `□p → p` fails at KB5.
- **rule shape**: the mint-arm shape claim is structural (prose), backed at the Lean level by
  `EuclGen.eucl` giving right-Euclideanness directly -- the closure's successor structure is the S5w
  cluster shape, so Phases 4/6/7's termination argument (`usedTags`, `S5wWorldInv`,
  `modalOps_lt_worldBound`) ports directly rather than being re-derived.
- **File placement decision for Phase 17** (the task heading asks Phase 15 to decide): the
  normal-form content proved here (`rooted_cluster_universal`, `rooted_cluster_isEquiv`, `kb5_per`)
  is **relation-generic** -- it needs only the `RightEuclidean`/`cod`/`Std.Symm` API, no tableau
  types. Land it **beside `EuclGen` in `Cslib/Foundations/Relation/Euclidean.lean`**, not a new
  tableau-local file. (Tableau-specific rooted-frame extraction, if any, still belongs in the Tableau
  dir; but the structure theorems are Foundations-tier.)

**Line estimate for Phases 16-23**: `EuclGen` + the three structure theorems above are ~40 lines of
additive `Euclidean.lean` content (Phases 16-17). The remaining Euclidean-route cost (Phases 18-23:
root-aware `modalApplyOneFive`/`modalApplyOneKb5`, `extractModelFive`,
soundness/completeness/decidability) is the genuinely new surface; the termination half ports from
Phases 1-7 (mint arms shape-identical to `modalApplyOneS5w`). Go: proceed to Phase 16
(`Relation.EuclGen`).

**Goal**: **GATE**, on the same cheap-and-early pattern as Phases 0 and 8. Confirm or falsify the
three load-bearing claims of the Euclidean route **in scratch, before any file is written**. This
phase writes **no** production Lean. It guards ~23.5 hours.

**Tasks**:
- [x] Confirm **(a) the closure exists and is inductively definable**. In scratch, define
      ```lean
      inductive EuclGen (r : α → α → Prop) : α → α → Prop
        | base {a b} : r a b → EuclGen r a b
        | eucl {a b c} : EuclGen r a b → EuclGen r a c → EuclGen r b c
      ```
      and confirm `RightEuclidean (EuclGen r)` and the least property
      `RightEuclidean s → (∀ a b, r a b → s a b) → EuclGen r a b → s a b` both go through.
      **The mathematical warrant** (record it): Euclideanness is closed under **arbitrary
      intersection** -- if `R1`, `R2` are Euclidean and `R = R1 ∩ R2`, then `R a b` and `R a c` give
      `R1 b c` and `R2 b c`, hence `R b c` -- and the **full** relation is Euclidean, so the family
      intersected over is non-empty. The least Euclidean relation containing `r` therefore **exists**;
      `EuclGen` is its inductive realization, and the least property above is the intersection
      characterization in usable form.
- [x] Confirm **(b) the rooted normal form**. Verify in scratch that for a right-Euclidean `r` and a
      root `w`, `R(w) × R(w) ⊆ R` follows immediately from `rightEuclidean : r w a → r w b → r a b`
      -- i.e. **the successors of the root form a universal cluster**, and a rooted Euclidean frame
      is exactly **root + cluster**. **Consume, do not re-derive**:
      `Relation.RightEuclidean.equiv_cod : IsEquiv (cod r) r` (`Euclidean.lean:124`) is **already
      landed** and gives the cluster's `IsEquiv` for free, supported by `rightTotal_cod` (:121),
      `cod_subset_dom` (:113), `refl_cod : r a b → r b b` (:45). **This is the single biggest cost
      reducer in the chain -- confirm it applies before building anything.**
- [x] Confirm **(c) the KB5 shape**. `kb5FC = Std.Symm r ∧ RightEuclidean r`, and symmetric +
      Euclidean gives **transitive** (`Relation.symm_rightEuclidean_iff_trans`, `Euclidean.lean:236`).
      So a KB5 frame is a **partial equivalence relation** (symmetric + transitive): an equivalence
      on `dom r`, plus possibly edge-isolated points. A **rooted** KB5 frame is therefore either the
      edge-isolated one-world frame **or** a full cluster containing the root -- which is exactly why
      `□p → p` fails at KB5 (the isolated root; see the probe's `boxImp_not_kb5Valid`). Confirm this
      dichotomy, since Phase 22's rule shape depends on it.
- [x] Pin down the **rule shape** for `modalApplyOneFive`: identical to `modalApplyOneS5w` except
      **root-aware** -- `T(□φ)@0` propagates to the cluster but **not** to `0` itself (no reflexivity
      at the root), while `T(□φ)@w` for `w ≠ 0` propagates universally within the cluster. Confirm
      the **mint arms are shape-identical to `modalApplyOneS5w`'s**, since that is what lets Phases
      4/6/7's termination argument (`usedTags`, `S5wWorldInv`, `modalOps_lt_worldBound`) port
      directly rather than be re-derived.
- [x] Record a written go/no-go with a line estimate for Phases 16-23.

**Timing**: 1.5 hours

**Depends on**: 14

**Files to modify**: none (scratch probe only)

**Verification**: a scratch snippet demonstrating (a), (b), (c) and the rule shape -- or a documented
counterexample and a `[BLOCKED]` record.

**Blocked-branch**: a no-go here is **cheap and valuable** -- it saves Phases 16-23 (~23.5h), and
Phases 0-14 are already green, committed, and shipped (the full S5 deliverable). Record the exact
failing claim and invoke fallback 4. **A no-go does NOT vindicate v3's impossibility claim** and must
not be recorded as though it did: `probes/five-s5-separation.lean` refutes that claim independently.
A no-go means *this* decomposition is wrong, not that 5/KB5 is unreachable.

---

### Phase 16: `Relation.EuclGen` -- the least-Euclidean closure operator [COMPLETED]

**Goal**: Land the closure operator whose absence v3 mistook for a mathematical obstruction. **This
is the "bespoke construction" `FrameCompleteness.lean:583-585` and `S5Simplification.lean:3029-3034`
both name as the cost.** It is missing library infrastructure; this phase supplies it.

**Tasks**:
- [x] Land in `Cslib/Foundations/Relation/Euclidean.lean`, beside the existing `RightEuclidean` API:
      ```lean
      inductive EuclGen (r : α → α → Prop) : α → α → Prop
        | base {a b} : r a b → EuclGen r a b
        | eucl {a b c} : EuclGen r a b → EuclGen r a c → EuclGen r b c

      instance : RightEuclidean (EuclGen r)                      -- by the `eucl` constructor
      theorem EuclGen.mono (h : r a b) : EuclGen r a b           -- `base`
      theorem EuclGen.least (hs : RightEuclidean s)
          (hle : ∀ a b, r a b → s a b) : EuclGen r a b → s a b   -- induction on EuclGen
      ```
- [x] Record the **structural precedent** in the docstring: `Relation.SymmGen` / `Relation.EqvGen` /
      `Relation.ReflGen` in the sibling `Cslib/Foundations/Relation/Confluence.lean` are exactly this
      pattern (see `SymmGen.to_eqvGen` :52, `reflTransGen_compRel : ReflTransGen (SymmGen r) = EqvGen r`
      :374 for a worked closure-characterization precedent). `EuclGen` is the Euclidean member of that
      family. **This placement is what the B/S5 routes already rely on for their closures**, so it is
      precedent-consistent rather than novel.
- [x] Record the **intersection warrant** from Phase 15 in the docstring: `EuclGen r` is the least
      Euclidean relation containing `r`, which exists because Euclideanness is closed under arbitrary
      intersection and the full relation is Euclidean. `EuclGen.least` **is** that characterization.
- [x] **R11 discipline**: this addition is **purely additive**. Touch **no existing declaration** in
      `Euclidean.lean`.

**Timing**: 2.5 hours

**Depends on**: 15

**Files to modify**: `Cslib/Foundations/Relation/Euclidean.lean`

**Verification**: full CI green; **the whole `Foundations/` tree compiles unmodified**; `shake`
reports no new suggestions; `lean_verify` on `EuclGen.least` (expect
`propext`/`Classical.choice`/`Quot.sound` at most).

**Blocked-branch**: if the least property resists, `[BLOCKED]` with the exact `lean_goal`. If the
addition perturbs an existing `Euclidean.lean` consumer (R11), move `EuclGen` local to the Tableau
directory and re-scope upstreaming to a follow-up -- **that is a relocation, not a `[BLOCKED]`**.

---

### Phase 17: The rooted normal form -- root + universal cluster [COMPLETED]

**Goal**: Land the structure theorem that makes K5 **adjacent to S5 rather than beyond it**: a rooted
Euclidean frame is a root plus a universal cluster. **This is the phase that converts the S5 cluster
machinery into 5/KB5 leverage.**

**Tasks**:
- [x] Land the cluster-is-universal fact for a rooted Euclidean frame: for right-Euclidean `r` and
      root `w`, `∀ a b, r w a → r w b → r a b` (immediate: this **is** `rightEuclidean`), i.e.
      `R(w) × R(w) ⊆ R`.
- [x] **Consume the landed `Relation.RightEuclidean.equiv_cod : IsEquiv (cod r) r`
      (`Euclidean.lean:124`) -- do NOT re-derive it.** It supplies the cluster's `IsEquiv` directly.
      Supporting: `rightTotal_cod` (:121), `cod_subset_dom` (:113), `refl_cod` (:45).
- [x] Land the decomposition for `EuclGen`-closed rooted frames: the carrier splits as
      `{root} ∪ cod (EuclGen r)`, with `EuclGen r` an equivalence **on the cluster** and the root
      related **into** the cluster but not necessarily to itself. **The root's non-reflexivity is the
      entire difference from S5** -- and is exactly what `□p → p` detects
      (`probes/five-s5-separation.lean`). *(deviation: altered -- rendered via the relation-generic
      `rooted_mem_cod` (root successors ⊆ cluster) + `rooted_cluster_isEquiv` (cluster is an
      equivalence), which apply to `EuclGen r` directly since it carries the `RightEuclidean`
      instance. A bespoke `EuclGen`-specific `IsEquiv (cod (EuclGen r)) (EuclGen r)` restatement was
      dropped: it added nothing over the generic theorems and hit a subtype-coercion elaboration
      snag. The non-reflexivity of the root is the ABSENCE of `r w w`, so it is not a theorem to
      land; the missing-reflexivity is documented in the module docstring.)*
- [x] Land the KB5 specialization from Phase 15(c): symmetric + Euclidean is a **PER**, so a rooted
      KB5 frame is either edge-isolated at the root or a full cluster containing it. Route via
      `Relation.symm_rightEuclidean_iff_trans` (`Euclidean.lean:236`).

**Timing**: 2.5 hours

**Depends on**: 16

**Files to modify**: `Cslib/Foundations/Relation/Euclidean.lean` (or a new
`Cslib/Logics/Modal/Tableau/EuclideanNormalForm.lean` if the content is tableau-specific rather than
relation-generic -- **Phase 15 decides this; do not guess**)

**Verification**: full CI green; `lean_verify` on the decomposition theorem; `equiv_cod` consumed,
not duplicated.

---

### Phase 18: `modalApplyOneFive` -- the root-aware rule + termination reuse [COMPLETED]

**POST-HOC CAVEAT -- propagation gap RESOLVED in v5 (Route 1); mint-arm gap RESOLVED-BY-DECISION in
v6 (Route (a), `reports/08_*`, see Phases 19a/19b below)**: the
`RuleApplicationSpecCore modalApplyOneFive` result landed here is genuinely correct and **stays
landed** -- it is a purely structural/syntactic fact (world-bound catalog membership, Hintikka
scaffolding) independent of frame semantics, and this phase remains `[COMPLETED]`. **TWO distinct
semantic soundness gaps were later found downstream of this phase, both now resolved-by-decision and
both preserved as records in Phase 19a/19b below** -- (i) the Route-1 *propagation* gap (v5) and (ii)
the *mint-arm witness-reuse* gap (v6). Neither demotes this phase: the mint arms and propagation
helpers landed here are structurally/syntactically correct; what changes is a root-aware **guard** on
their semantic use, installed in Phase 19a. The propagation
design as first landed (`modalFiveBoxAll`/`modalFiveDiaNegAll` ignoring the trigger world `_w`,
uniformly propagating to `modalKnownWorlds \ {0}` regardless of whether the trigger is the root or a
non-root world) **was confirmed semantically unsound** at `fiveFC` for root-triggered propagation
reaching a second-or-later-generation world (machine-checked `Fin 3` counterexample; full diagnosis
preserved in Phase 19's "Resolved blocker record"). **The remediation is decided: Route (1),
root/non-root asymmetric propagation** (`reports/07_*`). The corrected shape is a **bounded refinement**
of what this phase landed -- `modalFiveBoxAll`/`modalFiveDiaNegAll` gain an `acc` parameter and a
`hasEdge 0 w'` guard on the **root arm only**, making the root arm's output a **strict subset** of the
current output; the world-bound / catalog-membership spec fields therefore get **strictly easier**, the
mint-arm fields are **untouched**, and `modalApplyOneFive_specCore` is **re-verified** (not re-proved
from scratch). That refinement + the re-verification is executed at the **head of Phase 19a**, where the
soundness proof consumes it -- so this phase is not demoted and nothing it committed is discarded. **Do
not treat the *original* uniform propagation shape as final** -- Phase 19a installs the root/non-root
split before soundness is attempted.

**Mint-arm gap (v6, `reports/08_*` + handoff 10).** After Route 1 landed, the
`modalStepBranchFive_preserves_satIn` witness-reuse branch exposed a *second, independent* gap in the
**mint arms** (`T(◇φ)@w`/`F(□φ)@w`), which Route 1 deliberately left untouched. `modalApplyOneFive`'s
mint arms call `witnessWorldS5` **verbatim, unguarded** -- it searches all known worlds (root
included) for a syntactic `⟨s,φ,w'⟩` with no tie to the trigger's root/non-root identity or to any
recorded edge; on a hit the rule adds `sf.label → w'` and soundness needs `m.r (f sf.label) (f w')`,
which `RightEuclidean` does not force when either endpoint is the root. **Decision: Route (a)** --
exclude root `0` as a reuse witness and have root-triggered mint arms mint FRESH. **Unlike the Route-1
propagation refinement, this is NOT a bounded local re-verification**: the guard changes the mint-arm
output, so the landed tag-injection termination chain must be **re-derived** under a source-split
invariant (Phase-6/7-scale). That is why Phase 19 is split into **Phase 19a** (guarded mint arm +
termination re-derivation) and **Phase 19b** (`modalTableauFive_sound` assembly). This phase's
`modalApplyOneFive_specCore` still stands; the mint-arm world-bound fields are re-stated (not merely
re-verified) in Phase 19a. **Do not treat the *original* unguarded mint arms as final** -- Phase 19a
installs the root-aware guard before mint-arm soundness is attempted.

**Goal**: Land the 5 rule and its termination. **The termination half is a PORT, not new work** --
this is the payoff for putting these phases after the S5 chain.

**Tasks**:
- [x] Land `modalApplyOneFive : RuleApply Atom` -- **plain, NOT φ₀-parametrized** (report §8 item 3
      applies here verbatim: `hOutputsSubsetUniverse` at `FmpMeasure.lean:3241` binds `φ0`
      universally **inside** the hypothesis, so a φ₀-parametrized rule can never discharge it, for
      the 5 route exactly as for the S5 route).
- [x] The rule is `modalApplyOneS5w` **with root-awareness on the propagation arms**: `T(□φ)@0`
      propagates to the cluster but **not** to `0`; `T(□φ)@w` for `w ≠ 0` propagates universally
      within the cluster. Mirror for `F(◇φ)`. **The mint arms (`T(◇φ)@w`, `F(□φ)@w`) are
      shape-identical to `modalApplyOneS5w`'s** -- same witness-reuse test, same `.linear [witness]`
      output, same `acc.addEdge`. *(Landed as `modalFiveBoxAll`/`modalFiveDiaNegAll` -- the
      root-exclusion reduces to a single extra `if w' == 0 then none else …` filter clause added
      uniformly to both propagation helpers, regardless of the trigger world; this covers both the
      `T(□φ)@0` and `T(□φ)@w, w≠0` cases identically, since neither ever legitimately propagates
      back onto the root. `modalApplyOneFiveProp` mirrors `modalApplyOneS5` verbatim, substituting
      the two root-aware helpers for `modalS5BoxAll`/`modalS5DiaNegAll`; `modalApplyOneFive` mirrors
      `modalApplyOneS5w` verbatim, reusing `witnessWorldS5` directly (already rule-independent, no
      clone needed) and falling through to `modalApplyOneFiveProp`.)*
- [x] **The three design constraints from Phase 1 carry over UNCHANGED and are still each
      load-bearing**: `.linear [witness]` **not** `.linear []` (`freshLocal`'s right disjunct needs a
      cons); `.linear [witness]` **not** `.persistent []` (instant infinite loop, `Saturation.lean:141`);
      **no `hasEdge` guard** (R6 -- inverts the `exfalso` conjunct-3/4 discharge at
      `CompletenessLoop.lean:1049-1060` from a refutation into a proof obligation). Do not
      "optimize" any of them here either. *(Verified: `modalApplyOneFive`'s two mint arms are
      textually identical to `modalApplyOneS5w`'s -- same `.linear [witness]`/`acc.addEdge` shape,
      same guard-less dispatch.)*
- [x] **PORT the termination argument from Phases 4/6/7 -- do not re-derive it**: `modalOps`,
      `modalOps_lt_worldBound`, `mintTags`, `S5wTagInv`, `usedTags`, `usedTags_mono`, `S5wWorldInv`,
      `modalMaxWorld_lt_worldBound_of_S5w`. The counting crux is **identical**, because it depends
      only on the mint arms, which are shape-identical. Generalize the Phase 6/7 lemmas over the rule
      if that is cheaper than cloning them -- **Phase 15's estimate decides**. *(Landed by direct
      IMPORT/reuse, zero new proof: `FiveSimplification.lean` imports `S5Simplification.lean` and
      consumes `modalOps`/`mintTags`/`S5wTagInv`/`usedTags`/`usedTags_mono`/`S5wWorldInv`/
      `modalMaxWorld_lt_worldBound_of_S5w` unchanged -- none of these mention the rule in their
      statement, confirming the plan's prediction. `witnessWorldS5` is likewise reused directly, not
      cloned. Deviation: the rule-specific step-preservation theorem
      `modalStepBranchS5w_preserves_worldInv` (the one genuinely rule-specific piece of the chain,
      consumed only by `ModalLoopAuxS5w_stepPreserved` in `CompletenessLoop.lean`, Phase 21
      territory) is DEFERRED to Phase 21, where its Five-analogue (`ModalLoopAuxFive_stepPreserved`)
      is actually needed -- landing it here would be premature scaffolding with no phase-18 consumer
      per the plan's own Verification bullet.)*
- [x] **R8 carries over**: do **not** define a `birth` function as "the least world carrying the
      pair". The `usedTags`-cardinality formulation sidesteps it by never naming a witness world.
      *(Satisfied vacuously: no `birth` function is defined anywhere in `FiveSimplification.lean`.)*
- [x] Land `modalApplyOneFive_specCore : RuleApplicationSpecCore modalApplyOneFive`, reusing Phase 9's
      split structure. **K/T/B/S5 pay nothing.** *(Landed; all nine Core fields discharged along the
      two-layer agreement chain `modalApplyOneFive → modalApplyOneFiveProp → modalApplyOne`, mirroring
      `modalApplyOneS5w_specCore` field-for-field. Zero edits to any S5Simplification.lean/
      GenericDriver.lean declaration.)*

**Timing**: 3 hours

**Depends on**: 17

**Files to modify**: `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (new; mirrors
`S5Simplification.lean`'s structure), `Cslib/Logics/Modal/Tableau/S5Simplification.lean` (only if
Phase 6/7 lemmas are generalized over the rule) *(not touched -- reused via import instead)*

**Verification**: full CI green (lake build 3240 jobs, checkInitImports exit 0, lint-style clean,
lint clean for this file (repo-wide PrimeExclusion.lean baseline unchanged), shake clean for this
file (repo-wide exit 1 baseline unchanged), test green); axioms confirmed via `lake env lean` on
`modalApplyOneFive`/`modalApplyOneFive_specCore`/`modalApplyOneFive_fresh_local`/`modalTableauFive`
-- all in `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no new axioms; **`lake exe
mk_all --module`** run (single-line addition to `Cslib.lean`); **zero edits to any K/T/B/S5
declaration's statement** (confirmed: `S5Simplification.lean`/`GenericDriver.lean` untouched, only
imported).

---

### Phase 19a: Guarded mint arm + termination bound re-derivation [COMPLETED -- mint-arm guard LANDED (`56a84d07`); termination bound re-derivation LANDED (`2c7abe73`)]

**Goal**: Close BOTH Phase-19 soundness gaps at the rule/termination level, so that Phase 19b's
`modalTableauFive_sound` assembly discharges cleanly. Two gaps, two fixes: (i) the **propagation-arm**
gap -- install the **Route (1)** root/non-root asymmetric propagation fix in the Phase 18 helpers,
re-verify `modalApplyOneFive_specCore` (**LANDED in v5**, `4ae8eac5`; retained here as the landed
half of 19a); and (ii) the **mint-arm witness-reuse** gap -- install the **Route (a)** root-aware
mint-arm guard AND **re-derive the landed tag-injection termination chain** under a source-split
invariant (**the new, un-started, Phase-6/7-scale half of 19a**). Mirrors Phase 13's soundness
groundwork at the Euclidean frame class, with the root/non-root split the Euclidean class requires --
but with a genuine termination re-derivation the S5 chain never needed.

**THIS PHASE DOES NOT FIT A SINGLE DISPATCH** (`reports/08_*` critical scoping fact). The termination
re-derivation touches landed, committed, CI-green assets (`mintTags`/`usedTags`/`S5wTagInv`/
`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`, Phases 6/7), so it MUST be executed as
**sorry-free sub-milestones, each re-verified CI-green and committed** (per `git-workflow.md`'s
commit-per-green-substep mandate), under a **KILL budget** (below). Do not attempt it in one pass.

**DECISION -- PROPAGATION arm (made in `reports/07_*`; DO NOT re-litigate; LANDED in v5)**: **Route (1)**,
root/non-root asymmetric propagation. Route (2) (completeness cross-check) **converges** with Route (1)
rather than competing (see Phase 20's `EuclGen` note).

**DECISION -- MINT arm (made in `reports/08_*` by adversarial research; DO NOT re-litigate)**: **Route (a)**
-- a root-aware mint-arm guard (exclude root `0` as a reuse witness; root-triggered mint arms mint
FRESH) + termination-bound re-derivation under the source-split invariant. **Route (b)
(Euclidean-closure / model-repair) is PROVABLY DEAD** -- (1) in the soundness direction `m` already
satisfies `fiveFC` so `EuclGen m.r = m.r` (closure vacuous, adds no reuse edge), and (2)
"add-pair-then-close" falsifies box formulas by anti-monotonicity, so the "closure preserves
satisfaction" lemma it needs is FALSE (`reports/08_*` Kill 1 & Kill 2; recorded as Rejected Alternative
item 12). **Fallback 4 (S5-only)** is a last resort NOT warranted on soundness grounds -- Route (a) is
sound and stays linear -- but IS the terminus if 19a's termination re-derivation blows its KILL budget.

**RESOLVED BLOCKER RECORD #1 -- PROPAGATION gap (RESOLVED in v5 via Route 1; diagnosis preserved for
provenance)**: v4 recorded a `[BLOCKED]` here, hit at the design-analysis stage before any Lean proof
was attempted. The diagnosis is retained verbatim so a future dispatch sees both the gap and why the
fix closes it -- it is **not** deleted. The remediation (Route 1) is the LANDED half of **Tasks**.

- **Root cause (confirmed against landed code)**: The S5 soundness discharge
  `accReachableInv_related_s5` (`FrameSoundness.lean:1385`), built on `reachable_imp_related_s5`
  (`:1378`), consumes frame **reflexivity** in its induction base case (`hFC.1.refl (f 0)`, the first
  conjunct of `s5FC`). `fiveFC := Relation.RightEuclidean r` (`:1282`) has **no reflexivity
  conjunct**, so that base case is unavailable -- and it is genuinely **false** at the frame level.
- **What failed**: Phase 18's `modalFiveBoxAll`/`modalFiveDiaNegAll` propagate a box-positive/
  diamond-negative formula from **any** trigger world `w` (root or non-root) to **every** known
  non-root world, uniformly, ignoring `w`. Attempting to state the semantic soundness obligation
  this needs (mirroring `accReachableInv_related_s5`'s shape, per the task list) exposed that this
  uniform design is very likely **semantically unsound** for a pure Euclidean (not reflexive, not
  necessarily symmetric) relation, specifically for **root-triggered propagation reaching a
  second-or-later-generation world** (a world minted from a non-root trigger, not directly from
  the root).
- **What was tried**: A full derivation (not merely asserted) of the semantic argument needed, with
  a **computer-verified counterexample** confirming the concern is real, not a reasoning error:
  - Relation `r` on `Fin 3`: `r 0 1`, `r 1 1`, `r 1 2`, `r 2 1`, `r 2 2` (all else false).
  - Verified in Lean (`decide`, `Cslib/Foundations/Relation/Euclidean.lean`'s `RightEuclidean`):
    `r` **is** `RightEuclidean`, and **`¬ r 0 2`** -- confirmed by `lake env lean` on a scratch
    file, `decide`-checked, no axioms beyond kernel computation.
  - Concretely: `0` is the root, `{1, 2}` form a genuine Euclidean cluster (`1`/`2` mutually
    related, both reflexive) reached via `0 → 1 → 2` (world `2` minted from world `1`, **not**
    from the root), yet **`0` does not relate to `2`**. A model built on this frame satisfying
    `M, f(0) ⊨ □φ` imposes **no constraint whatsoever on `f(2)`** -- `2` is simply not a successor
    of `0` in this (genuinely Euclidean) model.
  - The realizing tableau scenario is not exotic: `φ₀ = ◇◇p` (the same shape as the standing
    `s5RankCounterFormula` test formula used earlier in this file) forces exactly this
    root→world1→world2 generation structure via ordinary diamond-positive mints.
  - Traced why the natural fix ("track that every known non-root world is directly root-related")
    fails to close inductively: when a **non-root** trigger `w1` mints `w2` (edge `w1 → w2`), the
    only Euclidean instance available combines facts sharing `w1` as source (giving `w2` related
    to *other things `w1` already relates to*, which **does** correctly re-derive full mutual
    relatedness among non-root cluster members -- this part of the design is fine); but it never
    produces `r(0, w2)` (no instance shares `0` as a common source with the new edge). This is not
    a proof gap that more tactic effort closes -- it is a genuine model-theoretic gap: `r(0,w2)` is
    **independent** of `r(0,w1) ∧ r(w1,w2)` under `RightEuclidean` alone (the counterexample above
    is the witness).
  - Considered redirecting every mint's edge to originate from the root (`acc.addEdge 0 w'` instead
    of `acc.addEdge sf.label w'`) so every minted world is a genuine direct root successor by
    construction. Rejected for now: this conflicts with `RuleApplicationSpecCore.freshLocal`'s
    contract (`GenericDriver.lean`), which requires *exactly one* edge added, `sf.label → wsf.label`
    -- already discharged, verified, and committed for `modalApplyOneFive` in Phase 18. Redefining
    the mint edge would invalidate Phase 18's landed `modalApplyOneFive_specCore` and would need to
    be re-verified from scratch, and it is not obviously compatible with the reused S5w termination
    machinery (`witnessWorldS5`, `modalApplyOneS5w_step`-style counting), which is keyed on
    `sf.label` throughout.
- **Why it's stuck**: The propagation design needs to distinguish root-triggered propagation
  (semantically must be restricted to `acc.successorsOf 0`, i.e. genuine direct root successors --
  standard K-style propagation, **not** `modalKnownWorlds \ {0}`) from non-root-triggered
  propagation (can safely remain universal across the full non-root cluster, since that direction
  **is** justified inductively via `RightEuclidean.rightEuclidean` with the trigger itself as the
  common source). This is a different rule than the one Phase 18 landed and verified
  (`modalFiveBoxAll`/`modalFiveDiaNegAll` currently ignore the trigger world `_w` entirely, by
  design, mirroring `modalS5BoxAll`'s S5-specific unconditional-propagation shape -- which **is**
  sound for `s5FC` because `s5FC` is an equivalence relation with transitivity, and pure `fiveFC`
  is not).
- **How Route (1) closes it (adversarial check passed in `reports/07_*`)**: split by trigger. The
  **root** direction is restricted to realized edges (`acc.successorsOf 0`); the **non-root** direction
  is justified with the trigger itself (or a common root successor) as the Euclidean source, inside the
  cod-equivalence. Neither arm leans on the false `m.r (f 0) (f w2)`. The suspected "relocation of the
  unsoundness" does **not** happen.

**Tasks -- LANDED half (Route 1 propagation fix; the propagation diagnosis above is resolved by
these steps, all committed in v5)**:

- [x] **Install the root/non-root split in the Phase 18 helpers** (`FiveSimplification.lean`). Give
      `modalFiveBoxAll`/`modalFiveDiaNegAll` an `acc` parameter and add a single `hasEdge 0 w'` guard
      on the **root arm** (`w == 0`): the root trigger keeps only `w'` with `acc.hasEdge 0 w'` (direct
      successors); the non-root trigger (`w ≠ 0`) keeps the current universal `modalKnownWorlds b \ {0}`
      cluster propagation **unchanged**. Keep the `filterMap over modalKnownWorlds b` skeleton so the
      root case is the **same list filtered by an extra `hasEdge 0 w'` predicate** -- the emitted set
      stays a **subset** of the current one. Membership lemmas `modalFiveBoxAll_mem`/`_mem` keep their
      conclusion verbatim (`x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0 ∧ x ∉ b`); one extra `by_cases`
      on the new guard.
- [x] **Thread `acc` through `modalApplyOneFiveProp`** so the propagation arms receive it. The mint
      arms (`T(◇φ)@w`, `F(□φ)@w`) are **UNTOUCHED** -- same witness-reuse test, same `.linear [witness]`,
      same `acc.addEdge sf.label w'`. The three Phase 1 design constraints (`.linear [witness]` not
      `.linear []`; not `.persistent []`; **no `hasEdge` guard on the mint/reuse arm**, R6) are
      preserved: the new guard sits on the **propagation** arm's target-list filter, not on the
      minting-vs-notApplicable dispatch.
- [x] **Re-verify `modalApplyOneFive_specCore`** under the revised helpers. The world-bound /
      catalog-membership fields (`hOutputsSubsetUniverse`, the `modalKnownWorlds` fields) get **strictly
      easier** -- the root arm's output is now a **subset** of what was already proven in bounds. The
      **mint-arm fields are untouched**. This is a re-verification, not a fresh proof.
- [x] **`GenericDriver.lean` is NOT touched.** `RuleApplicationSpecCore.freshLocal`'s one-edge mint
      contract is unchanged (the propagation arms emit `.persistent` formulas and add no edges), so the
      earlier-rejected "redirect mint edges to the root" idea is **not** Route 1 and stays discarded.
      **Termination is unaffected**: `modalOps`/`mintTags`/`S5wTagInv`/`usedTags`/`S5wWorldInv`/
      `modalMaxWorld_lt_worldBound_of_S5w` depend only on the **mint arms**, which Route 1 leaves alone;
      restricting propagation output to a subset cannot raise the world count.
- [x] **Land `accReachableInv_related_five`** (`FrameSoundness.lean`) -- the root/non-root discharge,
      the analogue of `accReachableInv_related_s5` (`:1385`) but **consuming
      `rooted_cluster_isEquiv.refl` on `cod r`** (the landed Phase 17 lemma
      `Relation.rooted_cluster_isEquiv : IsEquiv (cod r) r`) **instead of frame reflexivity** (`hFC.1`).
      Every non-root known world is a mint target, hence `f w ∈ cod m.r` by the landed
      `Relation.rooted_mem_cod`; two non-root known worlds are then related by one Euclidean composition
      **inside `cod`**, where reflexivity is recovered from the cod-equivalence. The root case is the
      standard K realized-edge argument on `acc.successorsOf 0`. Reuse the landed `accReachableInv`
      definition, `accReachableInv_initial`, and its step-preservation **unchanged** (edge-tracking is
      frame-condition-independent). *(deviation: altered -- landed as two lemmas,
      `reachable_imp_cod_related_five` (anchors a known non-root world to a direct root successor's
      image via `ReflTransGen` induction, symmetrizing inside `cod m.r` via `rooted_cluster_isEquiv`)
      + `accReachableInv_related_five` (combines two such anchors sharing `f 0` as common
      `RightEuclidean` source); required adding a previously-missing
      `import Cslib.Foundations.Relation.Euclidean` to `FrameSoundness.lean`. Verified sorry-free,
      CI-green, committed at `4ae8eac5`.)*
**Tasks -- NEW half (Route (a) mint-arm guard + termination re-derivation; the mint-arm diagnosis
below is resolved by these steps; execute as sorry-free CI-green sub-milestones with the KILL budget)**:

- [x] **Install the root-aware mint-arm guard** (`FiveSimplification.lean`). In the mint arms' use of
      `witnessWorldS5` (`T(◇φ)@w`, `F(□φ)@w`): (i) **exclude root `0` as a reuse witness** -- the
      candidate search skips `w' = 0`; (ii) **root-triggered mint arms mint FRESH** (`sf.label = 0` ⇒
      no reuse, mint a new world), equivalently reuse only under `acc.hasEdge 0 w'`. This is the
      **same root asymmetry** Route 1 installed for propagation, now on the mint arms. Note this is a
      *narrowing* of when reuse fires (Rejected-Alternatives item 8's "no `hasEdge` guard on the reuse
      arm" R6 concern is about a *blanket* guard that makes `.notApplicable` reachable on a mint shape;
      this guard instead **falls through to a FRESH mint**, never to `.notApplicable`, so the
      `exfalso` conjunct-3/4 discharge at `CompletenessLoop.lean:1049-1060` is preserved -- verify this
      explicitly as the guard's first sub-milestone). *(LANDED, `56a84d07`: introduced
      `witnessWorldFive` (root-`0`-excluding refinement of `witnessWorldS5`) and guarded both mint
      arms of `modalApplyOneFive` with `if sf.label == 0 then modalApplyOneFiveProp .. else match
      witnessWorldFive .. with ..`, falling through to `modalApplyOneFiveProp` on both branches, never
      to `.notApplicable`. All downstream consumers of the old `cases hw : witnessWorldS5 ..` pattern
      (`_fresh_local`, `_branchingLength`, `_persistentFresh`, `_outputsSubsetUniverse`,
      `_diaPosWitness'`/`_boxNegWitness'`, `_agree_or_reuse`) rewritten against two new case-split
      helpers, `modalApplyOneFive_diaPos_eq_or_reuse`/`_boxNeg_eq_or_reuse`, and re-verified.
      `modalApplyOneFive_specCore` re-verified under the guarded rule. Sorry-free; axioms confirmed
      via `lake env lean` + `#print axioms` as `[propext, Classical.choice, Quot.sound]` only (no
      `sorryAx`, no new axiom). Full `lake build` (777/777), `checkInitImports`, `lint-style`,
      `lake lint --builtin-lint` (zero new warnings for this file; only the pre-existing
      PrimeExclusion.lean baseline error and one pre-existing, untouched `flexible`-tactic info at
      line 510), `lake shake` (no import-removal suggestion for this file), and `lake test` all
      green.)*
- [x] **RE-DERIVE the tag-injection termination chain under the source-split invariant**
      (`FiveSimplification.lean`, and any `S5wWorldInv`/`S5wTagInv` consumers). The landed bound rests
      on "≤1 mint per `(sign, subformula)` tag"; under the guard it refines to "**≤1 mint per tag PER
      SOURCE-CLASS {root, non-root}**". Re-state and re-prove `mintTags`/`usedTags`/`usedTags_mono`/
      `S5wTagInv`/`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w` (or Five-analogues thereof) for
      the source-split invariant. The root contributes ≤1 mint per tag (bounded by the root's own
      diamond/negated-box subformulas, ≤ `|modalSubfmls φ₀|`); the non-root cluster contributes ≤1 per
      tag as before; new world bound ≈ `2·|modalSubfmls φ₀|` -- **a larger constant, still LINEAR**,
      decidability unaffected. Excluding root-as-witness never forces a second mint of an
      already-minted tag: a formula at the *root* was never minted (root formulas arrive by
      decomposition, not via `witnessWorldS5`), so minting fresh for it is that tag's *first* mint in
      the root source-class (`reports/08_*`).

      **LANDED, `2c7abe73` (task 515 phase 19a.2)**: `mintTags`/`S5wTagInv` (and their
      tag-membership corollaries `modalApplyOneS5w_diamondPos_tag_mem`/`_boxNeg_tag_mem`) are
      genuinely rule-independent -- they reference neither `witnessWorldS5` nor `witnessWorldFive` --
      so they are reused **verbatim** from `S5Simplification.lean` (now `public import`ed), per the
      shared-declaration constraint (S5Simplification.lean's `mintTags`/`usedTags`/`usedTags_mono`/
      `S5wTagInv`/`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w` themselves are untouched -- the S5
      chain still consumes them verbatim). Only the witness-reuse-*specific* pieces needed Five-local,
      source-split analogues, all additive in `FiveSimplification.lean`:
      `usedTagsFiveNonRoot`/`usedTagsFiveRoot` (source-split `usedTags`, each a `Finset` filter of the
      reused `mintTags φ₀`) + their monotonicity lemmas (`usedTagsFiveNonRoot_mono`/
      `usedTagsFiveRoot_mono`, mirroring `usedTags_mono`); `witnessWorldFive_none_not_mem_usedTagsFiveNonRoot`
      (the non-root reuse-miss case, direct analogue of `witnessWorldS5_none_not_mem_usedTags`);
      `diamondPos_root_mem_usedTagsFiveRoot`/`boxNeg_root_mem_usedTagsFiveRoot` (the
      root-trigger-always-fresh case -- no "unused" precondition needed, since the root arm fires
      unconditionally and is witnessed directly by the trigger's own presence on the branch);
      `FiveWorldInv` (source-split `S5wWorldInv`, summing both source-class counts); and
      `modalMaxWorld_lt_worldBound_of_FiveWorldInv` (the final chain, giving `modalMaxWorld b <
      modalWorldBound φ₀` at the larger-but-linear `2·modalOps φ₀` constant, matching
      `outputsSubsetUniverse`'s `hW` hypothesis shape exactly, via the new arithmetic companion
      `two_mul_modalOps_lt_worldBound`). Verified: scoped + full `lake build` (3240/3240) green,
      `checkInitImports` exit 0, `lint-style` clean, `lake lint`/`lake shake` (full-repo scans) report
      zero new warnings/import-suggestions attributable to this file (only pre-existing baselines
      elsewhere), `lake test` exit 0, zero `sorry`/`admit` in the file, axioms confirmed via
      `lake env lean` + `#print axioms` on every new declaration as `[propext, Classical.choice,
      Quot.sound]` (or a subset) only -- no `sorryAx`, no new custom axiom.

      **Scope note (not a deviation -- this is the literal scope of this checklist item and of the
      corresponding continuation-handoff task list)**: this lands the *static* source-split
      structures and the final arithmetic bound, mirroring `S5wWorldInv`/
      `modalMaxWorld_lt_worldBound_of_S5w`'s own shape (which likewise take the world-bound invariant
      as a hypothesis rather than proving it holds at every reachable branch). The *inductive*
      step-preservation proof establishing `FiveWorldInv` holds across the whole fuel-driven
      expansion (the source-split analogue of `S5wTagInv_S5wWorldInv_step`) is Phase 19b-scale work,
      for whatever call site eventually maintains it across the fuel induction -- consistent with
      `reports/08_*`'s own scoping and with the fact that `FiveSimplification.lean`'s
      `outputsSubsetUniverse` field already takes its world-bound fact as a raw hypothesis parameter,
      discharged nowhere in this file yet (recorded in handoff 11, unaffected by this dispatch).
      `modalApplyOneFive_specCore` re-verified unconditionally (untouched by this dispatch's edits);
      zero edits to any K/T/B/S4/S5 declaration's statement; the S5 surface and the five green
      Route-1/soundness building-block lemmas remain valid and unmodified.
- [x] **Re-verify `modalApplyOneFive_specCore`** under the guarded mint arms. The mint-arm world-bound
      fields **loosen on the reuse side** (reuse fires less often) but **gain the root-class allowance**
      on the mint side -- net linear. `GenericDriver.lean`'s `freshLocal` one-edge contract is
      untouched (the guard only *narrows* when reuse fires; on a fresh mint the existing one-edge
      `sf.label → wsf.label` contract holds unchanged). *(LANDED, `56a84d07`: `modalApplyOneFive_specCore`
      is a `where`-record built entirely from the sub-lemmas re-verified in the previous task
      (`modalApplyOneFive_fresh_local`, `_outputsSubsetUniverse`, `_persistentFresh`,
      `_branchingLength`, `_localShapeInvariance`, `_boxPosNotExpanding`, `_diaNegNotExpanding`,
      `_boxNegWitness'`, `_diaPosWitness'`); it typechecks unconditionally once those sub-lemmas do,
      confirmed by the full green `lake build`. Note: `outputsSubsetUniverse`'s statement only takes
      the world-bound fact `hW : modalMaxWorld b < modalWorldBound φ0` as a **hypothesis parameter**
      (`RuleApplicationSpecCore`'s generic shape) -- it does not itself derive `hW` from
      `S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`, and no site in `FiveSimplification.lean`
      currently discharges `hW` via that chain (the doc-comment references at the top of this file are
      a forward-looking design note, not yet a wired proof obligation). So this re-verification is
      genuinely unconditional on the termination re-derivation: it neither needs nor uses the
      old *or* the new source-split bound. The source-split re-derivation (previous task, still open)
      remains necessary work, but for supplying `hW` at whatever call site eventually maintains it
      across the induction (Phase 19b's soundness/termination assembly), not for this specCore
      re-verification itself.)*

**DECIDED BLOCKER RECORD #2 -- MINT-ARM witness-reuse gap (RESOLVED-BY-DECISION in v6 via Route (a);
diagnosis + countermodels preserved verbatim for provenance)**: discovered while building the bespoke
`modalTableauFive_sound` fuel-induction assembly (Phase 19b), *after* Route 1 landed. **Five green,
committed, still-valid building-block lemmas were landed en route and are REUSABLE, not to be
re-derived**: `modalApplyOneFiveProp_knownWorlds_step`, `modalApplyOneFive_agree_or_reuse`
(`FiveSimplification.lean`), `modalStepBranchFive_preserves_accReachableInv`, `FiveSoundInv`,
`modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn` (`FrameSoundness.lean`) -- all CI-green
(handoff 10). They are **structural / propagation** facts; the mint-arm guard does **not** invalidate
them. Attempting the next item, `modalStepBranchFive_preserves_satIn`'s **witness-reuse** branch (the
direct analogue of `modalStepBranchS5Gen_preserves_satIn`'s "Witness reuse" case, `FrameSoundness.lean`
around `modalS5BoxAll_soundIn`), exposed a **second, independent** semantic gap in the **mint arms**
(`T(◇φ)@w`/`F(□φ)@w`, i.e. `witnessWorldS5`-driven reuse), which Route (1) explicitly left untouched
(`reports/07_*`: "Mint-arm fields are untouched"). **Route (a) (Tasks above) resolves it; the diagnosis
and countermodels are preserved below.**

  - **What failed**: `modalApplyOneFive`'s two mint arms call `witnessWorldS5 b s φ`
    (`S5Simplification.lean:521`) **verbatim, unguarded** -- it searches **all** of
    `modalKnownWorlds b` (root included) for an existing `⟨s, φ, w'⟩`, with **no restriction** tying
    the found `w'` to the trigger `sf.label`'s identity (root or not) or to any recorded edge. When
    reuse fires, the rule adds edge `sf.label → w'` and the soundness proof (mirroring S5's, which
    keeps the **same** model `(W, m, f)` unchanged) needs `m.r (f sf.label) (f w')` to discharge the
    new edge's `hacc` obligation. S5 gets this for free from `accReachableInv_related_s5` (**any**
    two known worlds are related under an equivalence relation). The Route-1 replacement,
    `accReachableInv_related_five`, requires **both** endpoints non-root (`hwne`/`hw'ne`); it proves
    nothing when either `sf.label = 0` or `w' = 0`.
  - **What was tried**: A full derivation of both root-involving sub-cases, with an explicit
    adversarial-model check (not merely asserted):
    - **Root trigger** (`sf.label = 0`, arbitrary `w'` found by `witnessWorldS5`, no `hasEdge`
      guarantee): needs `m.r (f 0) (f w')`. `RightEuclidean` only forces relatedness between
      targets **sharing a common source**; there is none linking `f 0` and an arbitrary known
      `f w'` absent a recorded edge. A concrete adversarial `RightEuclidean` relation realizing the
      failure: two disjoint "islands" `r = {(a,b), (b,b)} ∪ {(c,d), (d,d)}` on `Fin 4` (`a=f 0`\-side,
      `c,d` an unrelated component) -- each island trivially satisfies `RightEuclidean` in isolation
      (no cross-pairs share a source), yet `¬ r a d`. A model built on this frame can satisfy
      `Satisfies m (f 0) (.diamond φ)` via `b` while **independently** satisfying `φ` at an unrelated
      `f w' = d`, with `r (f 0) (f w')` false throughout -- the exact shape `witnessWorldS5` cannot
      rule out (it only checks the branch's **syntactic** formula list, never the semantic model).
    - **Root witness** (`w' = 0`, arbitrary non-root trigger, i.e. some earlier propositional
      decomposition put a positive formula at world `0` that a later, unrelated diamond trigger's
      `witnessWorldS5` search then reuses): needs `m.r (f w) (f 0)`. Worse than the root-trigger
      case: `reachable_imp_cod_related_five`'s conclusion never targets `f 0` as an endpoint (only a
      **direct successor** of it), and world `0` has in-degree zero in `acc` in a well-formed rooted
      tableau (nothing ever emits an edge *into* the root), so there is no `hacc`-realized edge to
      fall back on either.
    - Considered whether a genuinely reachable tableau derivation exercises this: yes -- e.g.
      `φ₀ := χ → ψ` with `χ` chosen to literally **be** the body of a `.diamond` subformula
      processed later at an unrelated, non-root world (the imp-rule's alpha-decomposition of
      `F(χ → ψ)@0` unconditionally adds `T(χ)@0`, positive, at the root -- ordinary, not exotic).
    - Considered model-repair (redefining `f` or Euclidean-closing `m.r ∪ {(f w, f w')}` to patch the
      missing pair) as an alternative to needing the raw relatedness fact. Rejected as out of scope
      for this dispatch: naive union does not preserve `RightEuclidean` (needs a genuine closure,
      `Relation.EuclGen`-shaped, already used for **completeness** in Phase 20/`EuclGen`, not
      soundness), and would additionally need a fresh "closure preserves already-satisfied
      box/diamond formulas" lemma that does not exist anywhere in the codebase yet.
    - Considered a rule-level fix mirroring Route (1) (guard `witnessWorldS5`'s search: require
      `acc.hasEdge 0 w'` when the trigger is root; exclude `0` from candidacy as a witness
      altogether). Rejected as **not a bounded patch**: the termination argument
      (`modalMaxWorld_lt_worldBound_of_S5w`, Phase 6/7) relies on **at most one mint per
      `(sign, subformula)` tag** -- a guard that sometimes *rejects* an otherwise-valid reuse for a
      tag **already** minted once (specifically when the trigger/witness combination happens to
      cross the root boundary) would let that **same tag mint a second time** from a different
      trigger, which is exactly the invariant the tag-injection world-bound proof needs to stay
      intact. Any such guard requires re-deriving the termination bound alongside the soundness fix,
      not a local patch to `FiveSimplification.lean`/`FrameSoundness.lean` alone.
  - **Why it's stuck (now RESOLVED by Route (a))**: This is a genuine model-theoretic gap (parallel
    in kind, but independent in location, to the one Route (1) fixed for propagation), not a
    proof-search or tactic problem -- the counterexample sketch above is realizable. `reports/08_*`
    adjudicated the two candidate closures: **(a) a rule-level guard to the mint arms whose
    interaction with the already-landed termination proof is re-derived** (ADOPTED -- the 19a Tasks
    above), versus **(b) a "Euclidean-closure preserves satisfaction" model-repair argument** (KILLED:
    closure is vacuous in the soundness direction, `EuclGen m.r = m.r`; and add-pair-then-close
    falsifies box formulas by anti-monotonicity -- see Rejected-Alternatives item 12).
  - **RESOLUTION (Route (a), `reports/08_*`)**: the earlier "Considered a rule-level fix... Rejected as
    **not a bounded patch**" observation above was **correct** and is exactly why 19a is its own
    Phase-6/7-scale phase rather than a local patch: the guard IS adopted, and the termination bound IS
    re-derived alongside it under the source-split invariant. No fresh `/research` is outstanding --
    `reports/08_*` IS that research. Proceed straight to the 19a Tasks; this diagnosis is preserved
    verbatim, the same way the (now-resolved) Route-1 propagation diagnosis above was preserved.
  - **Prohibited workarounds**: do NOT use `sorry`, do NOT weaken `fiveFC`/`kb5FC`, do NOT restrict
    `modalTableauFive_sound`'s statement, do NOT silently guard `witnessWorldS5` without re-deriving
    the termination bound (that re-derivation IS the second 19a Task).

**KILL BUDGET (19a)**: the termination re-derivation is the real risk. If re-deriving
`modalMaxWorld_lt_worldBound_of_S5w` (or its Five source-split analogue) under the "≤1 mint per tag
per source-class" invariant **cannot be completed sorry-free within a bounded set of committed
sub-milestones** (soft ceiling ~800 lines across the re-stated chain), STOP, record the exact
`lean_goal` open state and the measured line count, and invoke **Fallback 4** (permanent S5-only
delivery; the 5/KB5 chain resumes via a follow-up carrying the open goal -- **never** re-narrated as
impossible). Do not paper over with `sorry`, a weakened `fiveFC`, or an un-reproved bound.

**Prohibited workarounds**: do NOT weaken `fiveFC`/`kb5FC`'s definitions, do NOT restrict
`modalTableauFive_sound`'s statement to a special case of `φ₀`, do NOT introduce `sorry` or an axiom
to paper over the gap, do NOT ship the guard without the re-derived termination bound.

**Timing**: 6 hours (Phase-6/7-scale: the LANDED Route-1 propagation half is committed; the NEW half
is the mint-arm guard + a from-scratch re-derivation of the tag-injection termination chain under the
source-split invariant, executed as sorry-free CI-green sub-milestones -- does NOT fit one dispatch).

**Depends on**: 18

**Files to modify**: `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (mint-arm guard +
source-split termination re-derivation + `modalApplyOneFive_specCore` re-verification),
`Cslib/Logics/Modal/Tableau/S5Simplification.lean` (only if a shared `S5wTagInv`/`S5wWorldInv`
consumer needs a source-split generalization rather than a Five-local clone). **`GenericDriver.lean`
NOT touched** (the `freshLocal` one-edge contract is unchanged; the guard only narrows when reuse
fires and otherwise mints fresh under the existing one-edge shape).

**Verification**: full CI green at every committed sub-milestone; the re-derived world bound is
**linear** (≈ `2·|modalSubfmls φ₀|`) and sorry-free; `modalApplyOneFive_specCore` typechecks under the
guarded mint arms; **zero edits to any K/T/B/S4/S5 declaration's statement**; the S5 surface
(`modalTableauS5*`, `extractModelS5*`, `modalTruthLemmaS5`, `instDecidableS5Valid`) untouched; the
five green building-block lemmas (DECIDED RECORD #2) remain valid and unmodified.

**Blocked-branch**: if the termination re-derivation blows the KILL BUDGET, `[BLOCKED]` with the exact
`lean_goal` + measured line count, then **Fallback 4**. No `sorry`.

---

### Phase 19b: `modalTableauFive_sound` bespoke assembly [COMPLETED]

**Goal**: Land `theorem modalTableauFive_sound (φ) (h : modalTableauFive φ = .closed) : fiveValid φ`
at `fiveFC`, the bespoke per-step-satisfiability + fuel-induction assembly consuming the (now sound)
mint/propagation lemmas from Phase 19a. Mirrors `FrameSoundness.lean`'s S5 bespoke chain
(`S5SoundInv` … `modalStepBranchS5_preserves_satIn` … `modalTableauS5_sound`, ~860 lines) at the
Euclidean frame class.

**Depends on Phase 19a** (both the Route-1 propagation fix AND the Route (a) guarded mint arm +
re-derived termination bound must be landed first -- the witness-reuse branch of
`modalStepBranchFive_preserves_satIn` only discharges once every reuse edge is guaranteed either a
genuine `m.r` edge (non-root/non-root, via `accReachableInv_related_five`) or a freshly-minted
successor (root-class, via the guard)).

**Reusable GREEN building blocks (landed across the last two dispatches; consume, do NOT re-derive)**:
`accReachableInv_related_five` + `reachable_imp_cod_related_five` (the root/non-root cod-equivalence
discharge, `4ae8eac5`); `modalApplyOneFiveProp_knownWorlds_step`, `modalApplyOneFive_agree_or_reuse`
(`FiveSimplification.lean`); `modalStepBranchFive_preserves_accReachableInv`, `FiveSoundInv`,
`modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn` (`FrameSoundness.lean`). The mint-arm guard from
19a does **not** invalidate any of them.

**Tasks**:
- [x] **Land the bespoke per-step satisfiability theorem** `modalStepBranchFive_preserves_satIn` (the
      Five analogue of `modalStepBranchS5Gen_preserves_satIn`), dispatching: the **propagation** case
      through `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn` + `accReachableInv_related_five`;
      the **witness-reuse** (mint) case through the 19a guard -- every reuse edge is now either a
      genuine `m.r` edge (non-root/non-root) or a fresh mint (root-class), so the previously-open
      `m.r (f sf.label) (f w')` obligation discharges. *(This is the item handoff 10 could not land;
      19a's guard is its precondition.)* **Landed** in `FrameSoundness.lean`, stated directly and
      non-generically over `modalApplyOneFive` (no `RuleApply`/spec-class abstraction needed, since
      Five has only the one shipped rule). Two small additive strengthenings were also landed in
      `FiveSimplification.lean` (`modalApplyOneFive_diaPos_eq_or_reuse_ne_root`/
      `_boxNeg_eq_or_reuse_ne_root`/`_agree_or_reuse_ne_root`) exposing `sf.label ≠ 0 ∧ sf'.label ≠ 0`
      at a reuse call -- needed because `accReachableInv_related_five` (unlike S5's
      `accReachableInv_related_s5`) requires both endpoints of a reuse edge to be non-root, a fact the
      already-landed `modalApplyOneFive_agree_or_reuse` did not expose.
- [x] **Assemble the fuel induction into `modalTableauFive_sound`**, mirroring the S5 bespoke chain
      `FrameSoundness.lean`'s `S5SoundInv` → `modalTableauS5_sound` (~860 lines). The fully-generic and
      S5-specific per-step theorems are structurally inapplicable to `modalApplyOneFive` (no
      `accReachableInv` slot; `modalApplyOneFive` does not satisfy `S5SoundSpec`), so a bespoke
      Five-specific chain is required -- estimated ~800-1100 new lines (handoff 09 scoping). Consume the
      reusable green blocks above; do not re-derive them. **Landed**: `modalExpandBranchesFive_closed_unsatIn`
      (direct, non-generic fuel induction threading `FiveSoundInv`) + `modalTableauFive_sound` capstone,
      both in `FrameSoundness.lean`. Note: unlike Phase 19a's termination-bound machinery
      (`FiveWorldInv`), the soundness assembly needs **no** world-bound hypothesis at all -- mirrors
      `S5SoundInv`'s own omission of a world-bound term exactly, since `outputsSubsetUniverse`/`hW` is
      Hintikka/completeness-side machinery (Phase 21), not soundness-side.
- [x] **KILL CONDITION**: if the bespoke assembly resists sorry-free beyond a bounded set of committed
      sub-milestones, `[BLOCKED]` with the exact `lean_goal` -- but note this is mechanical
      fuel-induction boilerplate on a now-sound rule, not a design gap (both soundness gaps are closed
      by 19a). Escalate only if the mechanical assembly itself is intractable. **Not triggered** --
      the bespoke assembly built sorry-free on the first attempt, well within budget (~640 new lines
      across the two files, vs. the ~800-1100 estimate).

**Prohibited workarounds**: do NOT weaken `fiveFC`/`kb5FC`'s definitions, do NOT restrict
`modalTableauFive_sound`'s statement to a special case of `φ₀`, do NOT introduce `sorry` or an axiom.

**Timing**: 5 hours (~800-1100-line bespoke assembly, mirroring Phase 13's ~860-line/3h S5 chain plus
the Five-specific per-step satisfiability theorem; may require two dispatches).

**Depends on**: 19a

**Files to modify**: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (`modalStepBranchFive_preserves_satIn`
+ the fuel-induction chain + `modalTableauFive_sound`).

**Verification**: full CI green; `lean_verify` on `modalTableauFive_sound` (expect
`propext`/`Classical.choice`/`Quot.sound` only); **zero edits to any K/T/B/S4/S5 declaration's
statement**; the S5 surface (`modalTableauS5*`, `extractModelS5*`, `modalTruthLemmaS5`,
`instDecidableS5Valid`) untouched.

**Blocked-branch**: `[BLOCKED]` with the exact `lean_goal` open state; earlier green phases (incl.
19a) preserved; downstream (21) transitively `[BLOCKED]`. No `sorry`.

---

### Phase 20: `extractModelFive` + the Euclidean truth lemma [COMPLETED]

**Design UNCHANGED by the v6 re-scope** -- this phase is the completeness/countermodel side and is
**independent of the soundness re-derivation**; it depends only on Phases 17/18 and runs in parallel
with Phase 19a (wave 13). **Both root/non-root splits -- Route (1) for propagation AND Route (a) for
the mint arms -- are consistent with -- indeed anticipated by -- this phase's `EuclGen` structure**:
`EuclGen`'s `eucl` constructor only combines two derivations **sharing the same first argument**, so
`EuclGen (acc.hasEdge)` relates the root `0` only to its `base`-case **direct successors**
(`acc.successorsOf 0`) and never manufactures `EuclGen r 0 2` from `EuclGen r 0 1` and
`EuclGen r 1 2`. That is exactly the asymmetric shape Route 1 installs for propagation soundness and
Route (a) installs for mint-arm soundness, so the same shape serves **both** soundness halves and the
completeness half (the strong consistency signal recorded in `reports/07_*` and `reports/08_*`,
"Convergence with completeness").

**Goal**: The countermodel half. Extract a **root + universal cluster** model from an open branch and
prove its truth lemma. **This is the phase `Relation.EuclGen` exists to serve.**

**Tasks**:
- [x] Land `extractModelFive` -- mirroring `extractModelS5` (`FrameCompleteness.lean:499-531`), but
      taking the model's relation as the **`Relation.EuclGen` closure** of `acc.hasEdge` rather than
      the `Relation.EqvGen` closure. **This is the one-word substitution the whole chain was built
      for**: `EqvGen` forces reflexivity (hence S5); `EuclGen` does not (hence 5).
- [x] Land `extractModelFive_rightEuclidean : RightEuclidean (extractModelFive b acc).r` -- immediate
      from Phase 16's `instance : RightEuclidean (EuclGen r)`.
- [x] Land the Euclidean truth lemma `modalTruthLemmaFive`, mirroring `modalTruthLemmaS5`
      (`FrameCompleteness.lean:2048`). Consume Phase 17's normal form for the box/diamond cases: the
      cluster case is **structurally the S5 case** (`equiv_cod` gives the cluster its `IsEquiv`), and
      the **root case is the only genuinely new one**. *(deviation: altered -- the root case turned
      out to need one further genuinely-new ingredient beyond what the phase note anticipated: a new
      abstract hypothesis `accTargetsNeRoot acc` (raw tableau edges never target the root),
      threaded through `modalTruthLemmaFive`/`modalOpenBranchFive_countermodel` alongside
      `hSrc`/`hTgt`. Without it the universal-propagation direction is false in general -- a
      counterexample edge `acc.hasEdge w 0` witnesses a model relation `r w 0` that
      `modalFiveBoxAll`'s root exclusion can never certify a matching branch formula for. Like
      `hSrc`/`hTgt`, discharging this hypothesis for a genuine tableau run (mint targets are fresh
      hence positive; Phase 19b's `modalApplyOneFive_agree_or_reuse_ne_root` shows reuse targets are
      non-root too) is deferred to Phase 21's `modalTableauFive_complete`, not re-derived here.)*
- [x] Land the `modalOpenBranchFive_countermodel` analogue, consuming **Phase 5's
      `modalExpandBranchesGen_openBranch_accTargetsKnown`** as its `hTgt` argument -- Phase 5 was
      promoted early precisely because **every route needs it**, and this is the second route that
      needs it. *(deviation: altered -- mirrors `modalOpenBranchS5_countermodel`'s own shape exactly:
      `hTgt` (and the new `hRoot`) are taken as abstract hypotheses of the theorem, not invoked
      internally; Phase 5's lemma is the witness Phase 21 will supply at the real open-branch call
      site, exactly as it already does for `modalTableauS5_complete`.)*
- [x] Note: `extractModelS5_rightEuclidean` (landed, task 504) stays **untouched**. It is a genuinely
      independent fragment and is **not** superseded by `extractModelFive`. Confirmed: this dispatch
      touched only `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive new section) and
      `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (four additive `_mem_of` introduction
      lemmas for `modalFiveBoxAll`/`modalFiveDiaNegAll`, needed by the truth lemma's box/diamond
      cases); no existing S5 declaration was edited.

**Timing**: 3.5 hours

**Depends on**: 18 (and 17)

**Files to modify**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

**Verification**: full CI green; `lean_verify` on `modalTruthLemmaFive`; `extractModelS5*` and
`modalTruthLemmaS5` **unmodified**.

**Blocked-branch**: `[BLOCKED]` with the exact `lean_goal` at the failing truth-lemma case. No
`sorry`.

---

### Phase 21: `modalTableauFive_complete` + `Decidable (fiveValid φ)` [PARTIAL]

**Unblocked (design unchanged)** -- consumes Phase 19b's `modalTableauFive_sound` (built on 19a's
Route-1 propagation + Route (a) mint-arm soundness) and Phase 20's countermodel.

**Goal**: The **first half of the re-scoped deliverable** the task description asks for and v3
proposed to strike.

**Tasks**:
- [x] **(deviation: added -- new scope item, not in the original four bullets)** Land the
      `accTargetsNeRoot` top-loop preservation pair `modalApplyOneFive_edge_target_ne_root` +
      `modalStepBranchFive_preserves_accTargetsNeRoot` (single-step) and
      `modalStepBranchFive_preserves_accTargetsKnown_and_NeRoot` +
      `modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot` (joint top-loop, bundled
      with `accTargetsKnown` since `accTargetsNeRoot`'s single-step preservation needs
      `accTargetsKnown` as an ambient invariant across the same induction -- the same "necessary
      THIRD hypothesis" pattern `S5Simplification.lean`'s `modalStepBranchS5w_preserves_worldInv`
      documents for `S5wWorldInv`). Landed in `FrameCompleteness.lean`, green, sorry-free, axioms
      `[propext, Classical.choice, Quot.sound]` only. This discharges Phase 20's `accTargetsNeRoot`
      abstract hypothesis for a real `modalTableauFive`/`modalExpandBranchesFive` run.
- [ ] **(deviation: blocked -- see note below)** Land
      `theorem modalTableauFive_complete (φ) (h : fiveValid φ) : modalTableauFive φ = .closed`,
      from the Phase 12 parametric lift (instantiated at `modalApplyOneFive`'s `Aux`) + Phase 20's
      countermodel + Phase 5's `hTgt`.
- [ ] **(deviation: blocked -- see note below)** Land a `hintikka_congr` analogue for the Five rule
      if the propagation arms require it -- Phase 2's proof works because `modalHintikkaSetGen`'s
      conjunct 2 returns **literal `True`** at `.neg, .box _` and `.pos, .diamond _`
      (`Saturation.lean:460-480`), which is a fact about the **driver**, not about S5. **Check
      whether it transfers before assuming it does**: the Five rule differs on the *propagation*
      arms, which is exactly where Phase 2's argument had no work to do for S5.
      **Investigation finding (this dispatch)**: no bridging lemma is needed at all --
      `modalTableauFive` already runs `modalApplyOneFive` directly (unlike S5's
      `modalTableauS5`/`modalApplyOneS5w` split), and `modalOpenBranchFive_countermodel` already
      takes `modalHintikkaSetGen modalApplyOneFive b acc` directly as `hH`. This task item is
      **moot**; the real blocker is the missing `Aux` instantiation (next bullet's note).
- [ ] **(deviation: blocked -- see note below)** Land `instance instDecidableFiveValid (φ) :
      Decidable (fiveValid φ)`, mirroring `instDecidableS5Valid` (Phase 14) and
      `instDecidableTValid` (`FrameCompleteness.lean:1281`).
- [ ] **(deviation: blocked -- see note below)** Confirm against the probe:
      `instDecidableFiveValid` must **not** be derivable from `instDecidableS5Valid` --
      `fiveValid_ssubset_s5Valid` proves it cannot be. If a proof appears to route through
      `s5Valid`, **it is wrong**; find the error.

**BLOCKER (Phase 21, remaining three items)**:
- **What failed**: `modalTableauFive_complete` needs a fourth ingredient beyond
  `accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot` (all now landed): the Hintikka "wall"
  `modalHintikkaSetGen modalApplyOneFive b a` at the real open branch, supplied by
  `modalExpandBranchesHintikka` (`CompletenessLoop.lean`) instantiated at a bespoke
  `Aux := ModalLoopAuxFive φ0` (mirroring S5's `ModalLoopAuxS5w`). This requires
  `ModalLoopAuxFive_stepPreserved`, which in turn requires the **inductive step-preservation
  proof for `FiveWorldInv` across the fuel-driven expansion** -- explicitly flagged as NOT YET
  BUILT by `FiveSimplification.lean`'s own docstring (lines 1424-1431, written when `FiveWorldInv`
  and `modalMaxWorld_lt_worldBound_of_FiveWorldInv` were landed): *"The inductive step-preservation
  proof establishing `FiveWorldInv` holds across the whole fuel-driven expansion ... is Phase
  19b-scale work, for whatever call site eventually maintains it."* `FiveWorldInv` and its
  arithmetic bound are landed and otherwise unused (`grep` confirms zero consumers before this
  dispatch) -- this is a real, previously-deferred gap, not a regression.
- **What was tried**: Read `S5Simplification.lean`'s full analogous machinery
  (`modalApplyOneS5w_step`, ~230 lines of per-shape case analysis, plus
  `modalStepBranchS5w_preserves_worldInv`, ~100 lines assembling it into the step-preservation
  theorem, plus several supporting private lemmas). Confirmed the K-rank route (`ModalLoopAuxK`,
  fully generic over any `RuleApplicationSpec`-satisfying rule) is **not** available as a
  shortcut: Five's box-positive/diamond-negative propagation shapes have the same
  `rankStep`-defeating shape as S5's universal rule (the documented, mechanized
  `RuleApplicationSpec.rankStep` counterexample, `S5Simplification.lean` "Phase 2 Obstruction"
  section) -- this is precisely why the witness-counting `FiveWorldInv` route was built in the
  first place, so no rank-based shortcut exists.
- **Why it's stuck**: A faithful Five analogue of `modalApplyOneS5w_step` +
  `modalStepBranchS5w_preserves_worldInv` needs the **same** case-work, doubled by the root/
  non-root source-class split `FiveWorldInv` itself introduces (`usedTagsFiveNonRoot` vs.
  `usedTagsFiveRoot`, each needing its own mint-tag-consumption argument, plus the guard's extra
  root/non-root dichotomy at each mint shape). This is genuinely comparable in scale to Phase 19b
  itself (which needed its own multi-dispatch effort per the task's commit history), far beyond
  what this dispatch's explicitly-budgeted new-scope item (the `accTargetsNeRoot` pair, now
  landed) covered, and beyond what could be responsibly attempted -- without risking a rushed,
  under-verified multi-hundred-line proof -- in the remaining budget of this dispatch.
- **What is needed**: A dedicated follow-up phase (recommend inserting "Phase 21b:
  `FiveWorldInv` step-preservation and the Hintikka wall" before the current Phase 22, or
  expanding Phase 21's own timing estimate substantially) to build, in
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (or `FiveSimplification.lean`, matching
  where `FiveWorldInv` itself already lives):
  1. `modalApplyOneFive_step` (mirrors `modalApplyOneS5w_step`, doubled for root/non-root at the
     two mint shapes), establishing the per-call subformula-closure + "known-worlds-or-fresh-mint"
     dichotomy against `usedTagsFiveNonRoot`/`usedTagsFiveRoot` instead of a single `usedTags`.
  2. `modalStepBranchFive_preserves_worldInv` (mirrors `modalStepBranchS5w_preserves_worldInv`),
     assembling (1) into single-step preservation of `S5wTagInv φ₀ b ∧ FiveWorldInv φ₀ b`.
  3. `ModalLoopAuxFive φ₀ b _e _acc := S5wTagInv φ₀ b ∧ FiveWorldInv φ₀ b`,
     `ModalLoopAuxFive_bounds` (trivial, via the already-landed
     `modalMaxWorld_lt_worldBound_of_FiveWorldInv`), `ModalLoopAuxFive_stepPreserved` (from (2)),
     and `modalLoopInvHintikkaFive_initial` (mirrors `modalLoopInvHintikkaS5w_initial`).
  4. Then `modalTableauFive_complete` and `instDecidableFiveValid` assemble exactly as
     `modalTableauS5_complete`/`instDecidableS5Valid` do, now with all four ingredients
     (`accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot`/the Hintikka wall) available.
- **Prohibited workarounds**: Do NOT use `sorry`, `def X := True`, or any vacuous placeholder for
  `ModalLoopAuxFive`/`modalTableauFive_complete`/`instDecidableFiveValid`. Do NOT weaken
  `fiveValid`/`modalTableauFive_sound`/the truth lemma to dodge this gap. Do NOT attempt a
  rank-based (`ModalLoopAuxK`) shortcut -- confirmed unavailable above.

**Timing**: 3 hours (substantially underestimates the remaining `FiveWorldInv` step-preservation
work; recommend re-costing at Phase 19b's own scale for the follow-up phase)

**Depends on**: 19b, 20

**Files to modify**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`

**Verification**: full CI green; `lean_verify` on `modalTableauFive_complete` and
`instDecidableFiveValid`; `instDecidableFiveValid` typechecks **and evaluates**; `#eval` on
`□p → p` returns **not valid** (the probe's separating formula -- a live regression check that the
route is genuinely at `fiveFC` and not silently at `s5FC`).

**Blocked-branch**: `[BLOCKED]` with the exact `lean_goal`. No `sorry`.

---

### Phase 22: KB5 -- `modalApplyOneKb5` + `modalTableauKb5_sound` [NOT STARTED]

**Unblocked (design unchanged)** -- KB5 reuses the **Route-1-corrected + Route-(a)-guarded** Five
pattern (the same root/non-root propagation split AND the same root-aware mint-arm guard). The KB5 PER
normal form (symmetric + Euclidean ⇒ transitive) makes the root/cluster dichotomy even cleaner; the
mint arms carry the Route (a) guard (exclude root as witness; root-triggered mint fresh) and the
source-split termination bound established in Phase 19a.

**Goal**: The KB5 rule and its soundness. **Cheaper than 5**, because Phase 17 established the PER
normal form and Phases 18/19a/19b established the pattern (rule + guard + source-split termination +
bespoke soundness assembly).

**Tasks**:
- [ ] Land `modalApplyOneKb5 : RuleApply Atom`, on Phase 15(c)/17's dichotomy: a rooted KB5 frame is
      either **edge-isolated at the root** or a **full cluster containing the root**. Symmetric +
      Euclidean gives transitive (`Relation.symm_rightEuclidean_iff_trans`, `Euclidean.lean:236`), so
      KB5 frames are PERs -- an equivalence on `dom r` plus isolated points.
- [ ] Port the termination argument from Phase 18 (which ported it from Phases 4/6/7). Mint arms are
      shape-identical again; the same three design constraints (R6, `.linear [witness]`, no guard)
      apply unchanged.
- [ ] Land `modalApplyOneKb5_specCore : RuleApplicationSpecCore modalApplyOneKb5`.
- [ ] Land `theorem modalTableauKb5_sound (φ) (h : modalTableauKb5 φ = .closed) : kb5Valid φ`.
- [ ] **Consider generalizing over the frame condition instead of cloning.** If Phases 18/19a/19b
      reveal that the Five and KB5 rules differ only in a `Std.Symm` obligation, factor the two rules
      over the frame condition rather than writing a third near-copy. **Phase 19a/19b's outcome decides
      this; do not pre-commit.** A three-way clone is acceptable if factoring costs more than it saves --
      **but say which was chosen and why in the phase note.**

**Timing**: 3 hours

**Depends on**: 21

**Files to modify**: `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` (or a sibling
`Kb5Simplification.lean` if not factored), `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`

**Verification**: full CI green; `lean_verify` on `modalTableauKb5_sound`; `mk_all` re-run if a new
file is added.

**Blocked-branch**: `[BLOCKED]` with the exact open goal. **Phase 21 (the 5 deliverable) is already
green and shipped at this point** -- a KB5 stall is a partial, not a loss.

---

### Phase 23: KB5 completeness, `Decidable (kb5Valid φ)`, and final docstring reconciliation [NOT STARTED]

**Unblocked (design unchanged)** -- the capstone; consumes Phases 19a/19b-22.

**Goal**: Close the **second half of the re-scoped deliverable** and reconcile every scope note in
the repo with what was actually delivered.

**Tasks**:
- [ ] Land `theorem modalTableauKb5_complete (φ) (h : kb5Valid φ) : modalTableauKb5 φ = .closed`,
      via `extractModelKb5` (the Phase 20 extraction at the PER normal form) + the Phase 12 lift.
- [ ] Land `instance instDecidableKb5Valid (φ) : Decidable (kb5Valid φ)`.
- [ ] **Reconcile `FrameCompleteness.lean:571-590`** -- replace Phase 3's forward-pointing note
      wholesale. It must now record: 5/KB5 **delivered** via the Euclidean route; the S5 route
      **proven** unreachable (cite `fiveValid_ssubset_s5Valid`, `kb5Valid_ssubset_s5Valid`); the
      `EuclGen` gap **closed** by `Relation.EuclGen` (`Euclidean.lean`). **The "OUT OF SCOPE …
      bespoke construction" paragraph (:581-590) is now FALSE and must go** -- the bespoke
      construction exists.
- [ ] **Reconcile `S5Simplification.lean:3018-3037`** -- the "Scope Note: Pure-K5 / Pure-5 Is Out of
      Scope" block. Its claim that *"Mathlib ships no closure operator that produces a
      Euclidean-but-not-necessarily-equivalence relation"* was true when written and is now
      **obsolete**: `Relation.EuclGen` is that operator. Note that its instruction *"Do **not**
      introduce a custom `EuclGen` closure operator **in this file**"* remains **satisfied and
      correct** -- `EuclGen` lands in `Cslib/Foundations/Relation/Euclidean.lean`, its proper home
      beside the `RightEuclidean` API and mirroring `SymmGen`/`EqvGen`'s placement in
      `Confluence.lean`. **Rewrite the note to point at the delivered route; do not simply delete the
      file-local prohibition, which is still good advice.**
- [ ] **Port the probe into the live tree.** Move `probes/five-s5-separation.lean`'s theorems
      (`fiveValid_ssubset_s5Valid`, `kb5Valid_ssubset_s5Valid`, `s5FC_imp_fiveFC`, `s5FC_imp_kb5FC`,
      `fiveValid_imp_s5Valid`, `kb5Valid_imp_s5Valid`, and the `boxImp_*` supports) into
      `FrameSoundness.lean` or `FrameCompleteness.lean` beside the frame-class defs. They are
      **sorry-free and axiom-free**, they are the standing proof that the two routes are genuinely
      distinct, and they belong in the library rather than cited from a `specs/` probe path. **This
      is the durable record that stops a future dispatch from "simplifying" the Euclidean route into
      the S5 one.**
- [ ] Land a `#eval`-backed regression test in `CslibTests`: `□p → p` is `s5Valid` but **not**
      `fiveValid` and **not** `kb5Valid` -- the probe's separating formula, as a live check.
- [ ] Full CI: `lake build` / `checkInitImports` / `lint-style` / `lint` / `test` / `shake`; `mk_all`
      if files were added.

**Timing**: 3 hours

**Depends on**: 22

**Files to modify**: `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`,
`Cslib/Logics/Modal/Tableau/S5Simplification.lean` (docstring), `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`
(probe port), `CslibTests/`

**Verification**: full CI green; `lean_verify` on `modalTableauKb5_complete` and
`instDecidableKb5Valid`; both new instances **evaluate**; **no docstring in `Cslib/` asserts that
5/KB5 is impossible or that no Euclidean closure operator exists**; the ported separation theorems
close sorry-free and axiom-free in their new home.

---

## Artifacts & Outputs

Expected sorry-free, axiom-free Lean outputs (per phase):

- **P0**: scratch probe result (no file output); go/no-go recorded in the phase note.
- **P1**: `witnessWorldS5`, `modalApplyOneS5w`, `witnessWorldS5_mem`, `modalApplyOneS5w_boxPos_eq`,
  `modalApplyOneS5w_diaNeg_eq`, `modalApplyOneS5w_eq_of_not_mint_shape` (`S5Simplification.lean`).
- **P2**: `hintikka_congr` (`S5Simplification.lean`).
- **P3**: the R7-refutation sibling theorem (`S5Simplification.lean`); corrected docstrings at
  `S5Simplification.lean:40-45`, `:1071-1073`, and `FrameCompleteness.lean:571-580`.
- **P4**: `modalOps`, `modalOps_le_complexity`, `modalOps_lt_worldBound`, `mintTags`,
  `mintTags_card_le_modalOps` (`S5Simplification.lean`).
- **P5**: `modalExpandBranchesGen_openBranch_accTargetsKnown` + the generalized double induction
  (`BDriver.lean`).
- **P6**: `S5wTagInv`, `usedTags`, `usedTags_mono`, `modalApplyOneS5w_outputs_tags`
  (`S5Simplification.lean`).
- **P7**: `S5wWorldInv`, `modalStepBranchS5w_preserves_worldInv`, `modalMaxWorld_lt_worldBound_of_S5w`
  (`S5Simplification.lean`).
- **P8**: R1 go/no-go + `lean_references` enumeration of `modalApplyOneS5_snd_eq` (no file output).
- **P9**: `RuleApplicationSpecCore`, split `RuleApplicationSpec`, `RuleApplicationSpec.toCore`
  (`GenericDriver.lean`); `modalApplyOneS5w_specCore` incl. `diaPosWitness'`/`boxNegWitness'`
  (`S5Simplification.lean`); K/T/B adapters.
- **P10**: `ModalLoopInvHintikka` + the `Aux`/`auxStep`/`auxBound` parametrization
  (`CompletenessLoop.lean`).
- **P11**: `modalStepHintikka_preserves_inv` (`CompletenessLoop.lean`).
- **P12**: `modalExpandBranchesHintikka`; `modalExpandBranchesGen_hintikka` re-derived with its
  **exact existing name and statement** (`CompletenessLoop.lean`).
- **P13**: `modalTableauS5_sound` (statement unchanged) + restated `modalApplyOneS5_snd_eq`
  (`FrameSoundness.lean`, `S5Simplification.lean`).
- **P14**: re-based `modalTableauS5`, `modalTableauS5_complete`, `instDecidableS5Valid`
  (`FrameCompleteness.lean`); ~2,000 lines **archived** to
  `specs/515_s5_universal_rule_termination_unblock_504/archive/01..05_*.lean`, each with a provenance
  header, and removed from `S5Simplification.lean` (**moved, not deleted**); `#eval` regression test
  (`CslibTests/`).
- **P15**: Euclidean route go/no-go + rooted-normal-form confirmation and a line estimate for
  Phases 16-23 (no file output).
- **P16**: `Relation.EuclGen`, `instance : RightEuclidean (EuclGen r)`, `EuclGen.mono`,
  `EuclGen.least` (`Cslib/Foundations/Relation/Euclidean.lean`).
- **P17**: the rooted root+cluster decomposition + the KB5 PER specialization, consuming the landed
  `RightEuclidean.equiv_cod` (`Euclidean.lean:124`).
- **P18**: `modalApplyOneFive`, `modalApplyOneFive_specCore`, and the ported termination chain
  (`FiveSimplification.lean`, new).
- **P19a**: LANDED half (v5): Route-1 propagation helper revision (`modalFiveBoxAll`/`modalFiveDiaNegAll`
  + `acc` param + root-arm `hasEdge 0 w'` guard; re-verified `modalApplyOneFive_specCore`)
  (`FiveSimplification.lean`); `accReachableInv_related_five` + `reachable_imp_cod_related_five`
  (`FrameSoundness.lean`). NEW half (v6, Route (a)): root-aware mint-arm guard (exclude root `0` as
  reuse witness; root-triggered mint fresh) + the source-split tag-injection termination chain
  re-derived (`mintTags`/`usedTags`/`S5wTagInv`/`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`
  Five-analogues under "≤1 mint per tag per {root, non-root}", linear bound ≈ `2·|modalSubfmls φ₀|`)
  + re-verified `modalApplyOneFive_specCore` under the guarded mint arms (`FiveSimplification.lean`).
  `GenericDriver.lean` untouched.
- **P19b**: `modalStepBranchFive_preserves_satIn` + the bespoke fuel-induction chain +
  `modalTableauFive_sound` (`FrameSoundness.lean`), consuming the five green building-block lemmas
  (`modalApplyOneFiveProp_knownWorlds_step`, `modalApplyOneFive_agree_or_reuse`,
  `modalStepBranchFive_preserves_accReachableInv`, `FiveSoundInv`,
  `modalFiveBoxAll_soundIn`/`modalFiveDiaNegAll_soundIn`) unchanged.
- **P20**: `extractModelFive`, `extractModelFive_rightEuclidean`, `modalTruthLemmaFive`,
  `modalOpenBranchFive_countermodel` (`FrameCompleteness.lean`).
- **P21**: `modalTableauFive_complete`, `instDecidableFiveValid` (`FrameCompleteness.lean`).
- **P22**: `modalApplyOneKb5`, `modalApplyOneKb5_specCore`, `modalTableauKb5_sound`.
- **P23**: `modalTableauKb5_complete`, `instDecidableKb5Valid`; reconciled scope notes
  (`FrameCompleteness.lean:571-590`, `S5Simplification.lean:3018-3037`); the separation theorems
  ported from `probes/five-s5-separation.lean` into the live tree; `#eval` separation regression test.
- Implementation summary at `specs/515_*/summaries/05_*-summary.md` on completion, with an honest
  per-phase status ledger (including any `[BLOCKED]`-with-open-goal entries), **the archive manifest
  (every moved block and its new path)**, and **an explicit statement of which of the two capstones
  (S5 at P14, 5/KB5 at P21/P23) landed**. **The 5/KB5 deliverable is NOT dropped in this plan** -- if
  it does not land, it is `[BLOCKED]` with an open goal and a follow-up, never re-narrated as
  impossible.

## Rollback/Contingency

- **Per-phase revert**: each phase commits narrowly and independently; a failing phase is reverted
  with `git revert` of that phase's single commit without disturbing earlier green phases. Never
  `git reset --hard` without a `git-snapshot.sh` snapshot and explicit user request.
- **Zero-debt contract**: no phase lands a `sorry`, a re-added rank axiom, a
  `RuleApplicationSpec modalApplyOneS5` witness, or a weakened K-facing
  `modalExpandBranchesGen_hintikka` statement. If a sub-piece cannot close sorry-free, its phase is
  marked `[BLOCKED]` with the exact `lean_goal` open state, earlier green phases are preserved, and
  downstream phases are transitively `[BLOCKED]`.
- **Four cheap gates, in order**: Phase 0 (30-min kill test, gates everything); Phase 8 (R1 scratch
  probe, gates 9-13); Phase 12b (K/T/B regression gate -- if the re-derivation fails, **stop**, the
  factoring is wrong); Phase 15 (Euclidean route probe, gates 16-23, ~1.5h guarding ~23.5h). Each
  fails **before** the expensive work it guards.
- **Archival is LAST in the S5 chain (Phase 14)**: the ~2,000 superseded lines are **moved** only
  after the replacement chain is green. If the plan lands `[PARTIAL]` before Phase 14, the superseded
  code **stays where it is** -- inert, in place, harmless -- and the archival is a clean follow-up.
  **Never archive ahead of the replacement.**
- **Archival is a MOVE, never a delete** (user decision: *"Code should be archived not deleted"*).
  Reverting Phase 14 restores the code from `specs/515_*/archive/` or from `git log --follow`. A
  Phase 14 diff that only removes lines is a **demolition and a phase failure** -- the archive files
  must appear as ADDED in the same commit.
- **Phases 15-23 sit after Phase 14 by design and never put the S5 deliverable at risk.** The
  archived assets are superseded by the **S5** chain; the Euclidean chain neither consumes nor
  supersedes them, so archiving at Phase 14 rather than at the very end is correct. **Archival makes
  this moot in any case**: if the Euclidean chain ever did want a retired asset, it is one read of
  the archive path away -- which is precisely why archival beats deletion here.
- **Fallback 1 (R2 fails)**: keep the rule; obtain the world bound another way. A phase, not a
  redesign.
- **Fallback 2 (R1 fails), pre-authorized**: atom-quotient semantic FMP -- `Decidable (s5Valid φ)` via
  enumerating quotient models over `Fin k → Bool`; compiled sorry-free and axiom-clean in the research
  session. Delivers **deliverable (4) only** -- not `modalTableauS5_complete`, and **not** 5/KB5 (its
  `qTransfer` needs reflexivity, which `fiveFC`/`kb5FC` lack). A documented `[PARTIAL]`, never the
  primary route.
- **Fallback 3 (R3 fails)**: stop at Phase 12. Phases 0-8 and 13 remain landed, green, and
  independently valuable (the rule, the congruence bridge, the refutation, the linear budget,
  `accTargetsKnown`, and possibly soundness).
- **Fallback 4 (the Euclidean chain stalls)**: land Phases 0-14 green (the full S5 deliverable) and
  mark the stalled Euclidean phase `[BLOCKED]` with its exact `lean_goal`. A genuine partial, not a
  failure. **The 5/KB5 deliverable is not re-struck by this** -- it is resumed by a follow-up task
  carrying the open goal.
- **Escalation**: if the lift and both fallbacks resist within budget, land the task `[PARTIAL]` with
  the rule + congruence + refutation + budget + soundness green and the lift `[BLOCKED]`-with-open-goal.
- **NO task description amendment is requested, and none is needed.** v3 demanded the 5/KB5 "Phase 7
  completion" deliverable be struck as mathematically impossible. **That demand is withdrawn**: the
  premise was refuted (`probes/five-s5-separation.lean` proves only that the *S5 route* cannot reach
  5/KB5, not that 5/KB5 is unreachable), and **the user was offered the strike and explicitly refused
  it**, directing *"write the mathematically correct solution, no matter the cost."* **The task
  description stands unchanged and this plan delivers it in full** (Phases 15-23). Do not re-open
  this.

## Rejected Alternatives (standing do-not-re-attempt record)

Recorded here, not only in the report, so a future dispatch does not re-attempt a dead end -- exactly
as the rank measure was. Full argument at `reports/03_s5-infrastructure-deep-research.md` §8.

> ### READ THIS BEFORE USING THIS LIST -- a REJECTED ROUTE is not a REJECTED DELIVERABLE
>
> **This list rejects ROUTES. It does not reject deliverables.** Item 0 below is the one place those
> two were conflated, and the conflation cost a full plan revision -- v3 turned *"the S5 tableau
> cannot reach 5/KB5"* (**true, now proven**) into *"5/KB5 is mathematically impossible and no
> successor plan can deliver it"* (**false**), and then used the impossibility to justify striking a
> stated deliverable and demanding the user amend the task description. **The user refused.**
>
> This record exists precisely to steer future dispatches, which makes an overclaim here far more
> expensive than one anywhere else in the plan: a "do-not-re-attempt" entry is *designed* to be
> obeyed without re-derivation. **A route is dead when its mechanism provably cannot reach the
> target. A deliverable is dead only when the mathematics says it does not exist -- and for 5/KB5,
> the mathematics says the opposite** (finding 4 (a)-(d); K5/KB5 have the FMP and are decidable).
> When adding to this list: state the **mechanism** that fails and the **target it cannot reach**.
> Never generalize from "this route fails" to "the target is unreachable."

0. **5/KB5 via the S5 tableau** -- *route rejected, PROVEN*. `fiveValid ⊊ s5Valid` and
   `kb5Valid ⊊ s5Valid` (`probes/five-s5-separation.lean`, sorry-free, **zero axioms**;
   `fiveValid_ssubset_s5Valid`, `kb5Valid_ssubset_s5Valid`), witnessed by `□p → p` on the one-world
   **empty** frame. An `s5Valid` decision procedure **cannot** decide `fiveValid`. Do not re-attempt
   plan v2's Phase 9, and do not try to derive `instDecidableFiveValid` from `instDecidableS5Valid`.
   **⚠ THIS IS A ROUTE REJECTION ONLY. "5/KB5 is impossible" IS NOT ON THIS LIST AND MUST NEVER BE
   ADDED TO IT.** 5/KB5 is a **re-scoped, in-scope deliverable of this plan** -- Phases 15-23, via
   the dedicated Euclidean route (`Relation.EuclGen` + the root+cluster normal form, built **on top
   of** the S5 cluster machinery). K5 is **adjacent** to S5, not beyond it. See "Route correction".

1. **Fuel domination (R7)** -- *false statement*. `maxWorld = fuel/2`, unbounded [VERIFIED]. Landed as
   a theorem in Phase 3.
2. **Firing-order / stratification / "create all worlds then fire boxes" / fairness** -- *provably
   impossible*. Divergence is a property of the rule set's **closure**, not its **schedule**. A fair
   schedule forces `T(◇p)@w_max` onto the branch -> the minting arm answers with a new world ->
   divergence. An unfair schedule loses Hintikka conjunct 2. **The strata do not stratify**: firing
   boxes *creates* world-creating formulas. (Also pre-emptively kills the Massacci π-before-ν
   ordering route.)
3. **Static pre-allocation / any φ₀-parametrized rule** -- *type-level impossibility*.
   `hOutputsSubsetUniverse` binds `φ0` universally **inside** the hypothesis
   (`FmpMeasure.lean:3241`) [VERIFIED].
4. **Keyed driver over `modalStepBranchS5gKeyed`** -- *rejected on cost, not correctness*.
   `modalExpMeasure_step_lt_gen` is stated for `modalStepBranchGen` [VERIFIED], so a keyed driver can
   consume neither the measure engine nor `modalExpandBranchesGen_hintikka`. Also quadratic
   (⌊n²/4⌋+1 on `□◇` chains).
5. **The unkeyed guard `modalApplyOneS5g` / `blockingWorldS5`** -- *structurally dead*. `= none` at
   **every** mint. S5's universal box injects formulas post-birth; the S4 birth-content abstraction
   assumes a world inherits at birth everything it will ever have. **S5 violates that premise.**
6. **Keeping `modalUniverseS5`/`modalWorldBoundS5`** -- *breaks the fuel*. `entryWorkS5 > fuelExp` at
   `atom`/`□p`/`p∧q` [VERIFIED]; the escape hatch `modalWorldBoundS5 ≤ modalWorldBound` is **false**
   [VERIFIED].
7. **`.linear []` on the reuse arm** -- breaks `freshLocal`'s right disjunct (needs a cons). The
   landed `modalApplyOneS5g` makes exactly this mistake (:987).
8. **A `hasEdge` guard on the reuse arm that makes `.notApplicable` reachable on a mint shape** --
   inverts the `exfalso` conjunct-3/4 discharge (`CompletenessLoop.lean:1049-1060`) from a refutation
   into a proof obligation. **NB (v6): Route (a)'s mint-arm guard is NOT this.** Route (a)'s guard
   (exclude root `0` as a reuse witness; root-triggered mint arms mint FRESH) **falls through to a
   FRESH mint**, never to `.notApplicable` -- so the mint shape still always emits `.linear [witness]`
   with a cons and one added edge, and the `exfalso` discharge is preserved. The prohibition here is
   specifically against a guard whose *rejected* branch answers `.notApplicable` on a mint-shaped
   input; verify Route (a)'s guard preserves the discharge as its first 19a sub-milestone.
9. **Filtration / semantic FMP as the route to Phase 8** -- *category error*. Filtration is purely
   **semantic**; it cannot produce `modalHintikkaSetGen`. The naive form is **false for S5**:
   filtration preserves reflexivity but **not** transitivity or symmetry (Blackburn2001 pp.79-81).
10. **Doczkal-Smolka-style pruning** -- *no fixpoint*. S5's universal relation makes the box condition
    **global** on the state set, so shrinking `T` makes boxes easier and diamonds harder
    simultaneously -- neither monotone nor antitone.
11. **Tightening `modalFuel`** -- *scope creep*. Sufficiency, not tightness, is the requirement.
12. **Route (b): Euclidean-closure / model-repair for the mint-arm witness-reuse gap** -- *route
    rejected, PROVABLY DEAD* (`reports/08_*`, adjudicating the Phase-19 mint-arm gap; NOT re-litigated).
    The idea: leave `modalApplyOneFive`'s mint arms unguarded; in `modalTableauFive_sound`, close `m.r`
    under right-Euclideanness (or add the reuse pair then close) so the missing `m.r (f w) (f w')`
    holds. **Two independent kills**: **(Kill 1) closure is VACUOUS in the soundness direction** -- the
    model `m` is *given* to satisfy `fiveFC`, i.e. `m.r` is already `RightEuclidean`, so by
    `EuclGen.least` + `EuclGen.mono` (`Euclidean.lean`, Phase 16) `EuclGen m.r = m.r`; closing an
    already-closed relation adds **no edge**, so it cannot supply the missing reuse edge. The `EuclGen`
    API is built for the *completeness* direction (Phase 20, where the canonical relation is not yet
    Euclidean) and does nothing on the soundness side. **(Kill 2) "add-pair-then-close" FALSIFIES box
    formulas by anti-monotonicity** -- the only non-vacuous reading `r' := EuclGen (m.r ∪ {(f w, f w')})`
    adds the edge by fiat then re-closes; box formulas are anti-monotone in the relation, and the
    branch carries box formulas at the very world being edited. Concrete killer (`reports/08_*` §Kill 2,
    realizable, not asserted): a world `w` carrying both `T(◇p)@w` and `T(□q)@w`, with `witnessWorldS5`
    reusing a separate `w'` where `w' ⊨ p` but `w' ⊭ q`; in `r'` the world `w` now has successor `w'`
    with `w' ⊭ q`, so `Satisfies m' w (□q)` is **false** -- a branch formula that held has been
    falsified. **No "closure preserves satisfaction" lemma can exist, because the statement is FALSE.**
    ⚠ Route (b) is the DEAD route for this gap; the LIVE route is **Route (a)** (root-aware mint-arm
    guard + source-split termination re-derivation, Phase 19a). Do not re-attempt Route (b), and do not
    re-narrate its death as "the mint-arm gap is unfixable" -- Route (a) fixes it soundly and linearly.
