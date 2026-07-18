# Research Report: Is the S5/KB5 Tableau-Completeness Architecture on the Right Track?

**Task**: 525 (KB5 completeness and decidability) — architecture-direction investigation
**Date**: 2026-07-17
**Type**: Research only (no source edits)

---

## 0. Verdict (short form)

**The architecture is on the right track; the blocker is a single misplaced gate, not a
structural dead-end.** The user's universal-cluster hypothesis is mathematically correct — but
it indicts one boolean conjunct in `modalKb5BoxAllFull`/`modalKb5DiaNegAllFull`, not the
edge-closure architecture as a whole. The extraction `Relation.EuclGen (Relation.SymmGen
acc.hasEdge)` **already is** the universal cluster (the least PER over a connected edge set is
total on its field), and the semantic soundness lemmas needed for the corrected rule are
**already landed** in `FrameSoundness.lean` (`reachable_imp_related_kb5`,
`accReachableInv_related_kb5`, `accReachableInv_kb5_root_refl`). The fix is: clone
`modalApplyOneKb5'` into a rule whose 0-target arm fires on *cluster-nonemptiness alone*
(dropping the `w == 0` trigger-identity conjunct). This is exactly the handoff's fix (i), but
the handoff's scope estimate ("comparable to the original Five construction, needs a
cluster-membership bookkeeping device") is an **overestimate**: no new bookkeeping device is
needed, because every known world is root-reachable by construction (`accReachableInv`, already
landed and consumed by task 524's soundness proof). Scope is task-524-sized plus a truth-lemma/
completeness assembly phase, not Phases-15-21-sized. The `decide`-kernel stall is **orthogonal**
and is *not* fixed by any of this (Section 5).

---

## 1. Codebase Grounding: Why the Rule/Model Mismatch Exists

All claims in this section are **verified in the code** at the cited anchors.

### 1.1 The two halves that disagree

**Extraction half** (`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:3230-3270`):
`extractModelKb5 := extractModelWith (fun r => Relation.EuclGen (Relation.SymmGen r))`. Its
relation is the least symmetric right-Euclidean (= least PER, by
`Relation.symm_rightEuclidean_iff_trans`, `Euclidean.lean:291`) relation containing every raw
tableau edge. The docstring at :3224-3226 correctly notes this closure is *forced*: any
kb5FC-satisfying relation preserving all raw edges must contain it
(`Relation.EuclGen.least`, `Euclidean.lean:175`, plus the scout lemma's remark at :3507-3511
that the root-reach consequence holds in **any** such relation, so no alternative closure
operator escapes it).

**Rule half** (`Cslib/Logics/Modal/Tableau/FiveSimplification.lean:1535-1548`):
`modalKb5BoxAllFull b φ w` dumps `T(φ)` to every known **non-root** world unconditionally, and
adds the self-target `T(φ)@0` only under the gate

```
w == 0 && (modalKnownWorlds b).any (fun v => !(v == 0))
```

i.e. **trigger-identity** (`w == 0`) AND cluster-nonemptiness. The membership dichotomy
`modalKb5BoxAllFull_mem` (:1573) confirms structurally: a `0`-labeled output *requires* the
trigger to be literally `0`.

### 1.2 The proven gap

`extractModelKb5_root_reach_scout` (`FrameCompleteness.lean:3513`) shows two raw edges
`0 → a`, `a → w` force `EuclGen (SymmGen r) 0 w`; `extractModelKb5_nonRoot_boxPos_gap` (:3544)
combines this with `EuclGen.symm_of_symm` to get `.r w 0` while simultaneously proving
`T(ψ)@0 ∉ modalKb5BoxAllFull b ψ w` for any non-root `w`. Concrete Hintikka-saturated witness:
`φ₀ = ¬◇◇□p`, open branch with `acc.edges = [(1,2),(0,1)]`, `T(□p)@2 ∈ b`, `T(p)@0 ∉ b`, yet
`.r 2 0` holds (Phase 3 blocker note, :3559-3598). So `modalTruthLemmaKb5` is false for the
frozen rule — verified, not inferred.

### 1.3 Is the mismatch intrinsic to "close over raw edges"?

**No — it is intrinsic to *trigger-identity gating*, and would indeed recur under one of the
handoff's two fixes but not the other.** The scout's own docstring (:3507-3511) proves the
closure side is immovable: `r w 0` is forced in *every* kb5FC relation preserving raw edges.
Therefore:

- Handoff fix (ii) ("a different extraction that keeps the rule root-trigger-gated") is a
  **dead end** — my inference, but a near-immediate one from the verified scout remark: any
  admissible extraction must relate chain-connected non-root worlds back to the root, so a
  root-trigger-gated rule can never match any sound extraction. Fix (ii) should be dropped.
- Handoff fix (i) (dump to 0 unconditionally on chain-connectivity) is correct and is
  precisely the universal-cluster rule of Section 2. The mismatch does not recur under it.

---

## 2. The Universal-Cluster Alternative (Core Question)

### 2.1 The KB5 collapse — verified in-repo, not just literature

`Euclidean.lean`'s "Rooted normal form" section (:321-364) already formalizes the collapse:

- `rooted_cluster_universal` (:335): in a right-Euclidean frame all successors of a root are
  mutually related — the successor set is a universal cluster.
- `rooted_cluster_isEquiv` (:342): that cluster carries an equivalence (an S5 cluster).
- `rooted_mem_cod` (:349): the root sits *above* the cluster; for pure 5/K5 it need not be in
  it — this is the Five architecture, and it is why Five's root-gated rule is correct for Five.
- `symm_rightEuclidean_root_refl` (:362): **KB5 dichotomy witness** — with symmetry added, a
  root with *any* successor is reflexive, hence joins the cluster.

**Reconciliation the task asked for**: for KB5 the "root outside the cluster" configuration
degenerates. A point-generated KB5 frame is either (a) an edge-isolated root (trivial: all
boxes vacuously true, only propositional content matters), or (b) root-with-≥1-successor, in
which case symmetry pulls the root into the successors' universal cluster and the generated
subframe is a single universal cluster *containing the root*. So yes: the real distinction is
exactly "root with no successors" vs "root with ≥1 successor", and the collapse holds for full
KB5, not merely the successor-generated subframe — the root is *in* the generated subframe and
joins the cluster in case (b). This is verified in-repo at the lemma level
(`symm_rightEuclidean_root_refl`) and is the standard result (Section 3).

### 2.2 The extraction already IS the universal cluster

Key observation (my inference, one step from verified facts): the branch's raw edge set is a
tree rooted at 0 (worlds are only minted as fresh children of existing worlds; the landed
invariant `accReachableInv` in `FrameSoundness.lean` — verified present via `lean_local_search`
— states every known world is `ReflTransGen`-reachable from 0). The least PER containing a
*connected* symmetric graph is the **total relation on its vertex set**. Hence
`extractModelKb5`'s relation already equals "universal cluster over the branch's edge-touched
worlds" — which is exactly why the gap lemma could derive `.r 2 0`. **A flat universal
extraction would not change the extracted relation extensionally; it would only change its
presentation.** The defective half is the rule, full stop.

### 2.3 The corrected rule

Take `modalKb5BoxAllFull` and change one line — the gate at `FiveSimplification.lean:1544`
from `w == 0 && clusterNonempty` to `clusterNonempty` (dually :1561). The mint arms
(`T(◇φ)`/`F(□φ)`) stay untouched, exactly as task 524 already argued (:1517-1522): existential
shapes must keep witness-reuse or termination diverges (the R7 refutation,
`S5Simplification.lean:1944-2035`, is the machine-checked reason unconditional universal
propagation *without* witness-reuse mints is non-terminating; the corrected rule changes only
the universal shapes, so 524's termination story carries over structurally).

Does `modalKb5BoxAllFull` "already gesture at this"? **Yes, literally**: its non-root arm is
already unconditional in the trigger; only the 0-target arm carries the spurious identity gate.

**Soundness of the corrected rule is nearly free** — the lemma family is landed
(`FrameSoundness.lean`, task 524 section):

| Obligation (trigger `w`, target `v`) | Landed discharge |
|---|---|
| `w = 0`, `v ≠ 0` | `reachable_imp_related_kb5` (:1582) |
| `w ≠ 0`, `v ≠ 0` | `accReachableInv_related_kb5` (:1610) |
| `w = 0`, `v = 0` | `accReachableInv_kb5_root_refl` (:1633) — already used by the frozen rule |
| `w ≠ 0`, `v = 0` (**the new case**) | `Std.Symm.symm` of `reachable_imp_related_kb5` — a one-liner |

This is why the handoff's "needs a cluster-membership bookkeeping device" is an overestimate:
cluster membership for KB5 *is* known-world-ness (every known world is root-reachable,
`accReachableInv`), so `modalKnownWorlds b` is already the cluster bookkeeping. No new device.

**Truth lemma becomes true** with the corrected rule, even keeping the existing extraction:
given `.r w v` (closure), `symmEuclGen_mem_modalKnownWorlds_iff` (landed,
`FrameCompleteness.lean:3285`) puts `v` in the known set; if `v ≠ 0` the unconditional arm
covers it; if `v = 0`, any closure derivation contains at least one raw edge, whose target is
known and non-root (`accTargetsNeRoot`, cf. :3497), giving the cluster-nonempty witness the
gate needs. The gap lemma's obstruction dissolves because `T(ψ)@0` is now emitted for
non-root triggers too.

### 2.4 Flat universal extraction — optional simplification, not required

Alternative extraction: `r w w' := w ∈ K ∧ w' ∈ K ∧ (∃ v ∈ K, v ≠ 0)` with
`K := modalKnownWorlds b` (empty relation when the branch never minted — matching the
edge-isolated-root case, where boxes are vacuous). Properties: symmetric and right-Euclidean
definitionally (both trivial), so `kb5FC` is immediate; edge-survival needs only
`accSourcesKnown`/`accTargetsKnown`/`accTargetsNeRoot`; and the truth lemma's box case becomes
a direct membership computation with **no induction over closure derivations**. By 2.2 it is
extensionally the same relation as the closure on saturated branches.

Trade-off:
- **Keep closure extraction + corrected rule**: maximal reuse — `extractModelKb5`,
  `extractModelKb5_r/_symm/_rightEuclidean/_hasEdge_imp_r`, and Phase 1's
  `symmEuclGen_mem_modalKnownWorlds_iff`/`extractModelKb5_root_reach_mem_modalKnownWorlds` all
  survive verbatim. Truth lemma still does derivation induction (Five-style, precedented).
- **Flat extraction + corrected rule**: simplest possible truth lemma; retires the Phase 1
  closure lemmas and the `extractModelKb5` lemma block (small, ~90 lines); needs a fresh (but
  trivial) kb5FC/edge-survival block.

Either dissolves the blocker. Recommendation: **corrected rule + flat universal extraction**
if optimizing for proof simplicity and alignment with the KB5 dichotomy; **corrected rule +
existing closure** if optimizing for minimal churn and Phase 1-2 asset survival. The rule
change is mandatory in both; the extraction change is taste.

---

## 3. Literature & Mathlib Check

**Standard modal-logic results** (not verified in code; standard sources):

- S5 is characterized by the class of universal frames: validity over equivalence frames
  coincides with validity over universal frames, via point-generated subframes (an equivalence
  frame generated from a point is a universal cluster). Blackburn–de Rijke–Venema, *Modal
  Logic* (CUP 2001), generated-submodel machinery §2.1-2.3 and the S5/universal-frame
  discussion; also Chagrov–Zakharyaschev, *Modal Logic* (OUP 1997).
- The K5 family (K5, K45, KB5, KD45, S5) has the finite/small model property with
  point-generated frames of depth ≤ 2 ("root + universal cluster"); Nagle & Thomason's
  classification of extensions of K5 (JSL 1985) is the classical reference. S5-satisfiability
  is NP-complete (Ladner 1977) precisely because of the single-cluster small-model property.
- KB5 point-generated frames: isolated irreflexive point, or a universal cluster containing
  the root — matching Section 2.1's in-repo dichotomy. The repo's own blocker note already
  cites BdRV §4.8-4.9 for "KB5 completeness via rooted Euclidean tableau is standard"
  (`FrameCompleteness.lean:3585`).

**Mathlib**: no Kripke-frame or modal-logic infrastructure exists to reuse (checked via
LeanSearch, query "Kripke frame modal logic satisfiability universal accessibility relation" —
top hits are unrelated `Set.univ` relation trivia, e.g. `SetRel.isSymm_univ`,
`isTransitiveRel_univ`, which at most confirm Mathlib knows the universal relation is an
equivalence). Modal semantics lives entirely in CSLib.

**CSLib reuse check** (per reuse-first protocol): the universal-cluster infrastructure is
already in `Cslib/Foundations/Relation/Euclidean.lean` (rooted normal form section,
`RightEuclidean.equiv_cod` :124, `rooted_cluster_*` :335-350, `symm_rightEuclidean_root_refl`
:362) — **nothing needs to be rebuilt in Foundations**. The S5 chain (`modalS5BoxAll`,
`S5Simplification.lean:145`, trigger-*unused* universal dump; `extractModelS5 :=
extractModelWith Relation.EqvGen`, `FrameCompleteness.lean:500`; `hintikkaS5_box_pos`
:1986) is the existing in-repo precedent for exactly the "unconditional dump + closure that is
universal on the connected component" pairing — the corrected KB5 rule is its
non-reflexive-root-aware sibling, and S5's chain is unaffected by any of this.

---

## 4. Verdict, Sketch, Survival Accounting, Scope

### 4.1 Verdict

**(a)-leaning, with a correction to the handoff**: the edge-closure architecture is
salvageable, and the salvage *is* the universal-cluster route — the two are the same thing
here, because the closure already collapses to the universal cluster. What is **not**
salvageable is the handoff's fix (ii) (keep the trigger-gated rule, change the extraction):
provably no admissible extraction exists for that rule (Section 1.3). What is **overscoped**
in the handoff is fix (i): no cluster-membership bookkeeping device is needed. A full
re-architecture (filtration, fresh S5-style stack) is unnecessary.

### 4.2 Sketch of the fix (one follow-on task, phased)

1. **Rule**: `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv` — clones of the landed `*Full`
   helpers with the `w == 0` conjunct dropped from the 0-target gate (mint arms untouched).
   New `modalApplyOneKb5''` (naming per repo convention) cloning `modalApplyOneKb5'Prop`
   dispatch. Membership dichotomy: fresh, and (target known non-root) ∨ (target 0 ∧ cluster
   nonempty) — trigger no longer appears.
2. **specCore/termination**: re-derive `RuleApplicationSpecCore` mirroring
   `modalApplyOneKb5'_specCore` (mechanical clone; output-shape bounds unchanged since the
   emitted set only grows by at most the single `@0` formula, already present in the
   root-trigger case 524 handled).
3. **Soundness**: direct-against-`kb5FC` theorem mirroring `modalTableauKb5'_sound`, with the
   single new case discharged by symmetrizing `reachable_imp_related_kb5` (Section 2.3 table).
4. **Extraction + truth lemma**: either keep `extractModelKb5` (truth lemma by Five-style
   closure induction, root case via `symmEuclGen_mem_modalKnownWorlds_iff` + an
   `∃-edge-in-derivation` helper) or a flat universal extraction (truth lemma by membership
   computation). Phase 2's `hintikkaKb5'_box_pos`/`_diamond_neg` re-derive against the new
   rule with the simpler (trigger-free) dichotomy — near-copies.
5. **Completeness + decidability**: `modalOpenBranchKb5''_countermodel`,
   `modalTableauKb5''_complete`, `kb5Valid_decides`, `instDecidableKb5Valid` — assembly
   mirroring `fiveValid_decides`/`instDecidableFiveValid` (`FrameCompleteness.lean:3200-3216`).

### 4.3 What survives

- **Task 524 frozen deliverables**: survive untouched as landed sound artifacts
  (`modalApplyOneKb5'`, `modalTableauKb5'_sound`); the new rule sits beside them, exactly as
  `modalApplyOneKb5'` sits beside the `modalApplyOneKb5 := modalApplyOneFive` alias.
- **Task 524's semantic lemma family** (`reachable_imp_related_kb5`,
  `accReachableInv_related_kb5`, `accReachableInv_kb5_root_refl`): survive and become the
  soundness engine of the new rule — they were proved trigger-agnostically.
- **Task 525 Phase 1** (`symmEuclGen_mem_modalKnownWorlds_iff`,
  `extractModelKb5_root_reach_mem_modalKnownWorlds`): survive verbatim on the
  closure-extraction variant; retired (with the extraction) on the flat variant.
- **Task 525 Phase 2** (`modalKb5*AllFull_mem_of`, `hintikkaKb5'_*`): statements are pinned to
  the frozen rule's dichotomy; they survive as documentation of that rule but the new rule
  needs its own (simpler) copies. Pattern reuse is total; textual reuse is high.
- **Gap lemmas/blocker notes**: survive as the permanent record of why the gate moved.

### 4.4 Scope estimate

Comparable to **task 524 plus one truth-lemma/completeness phase block** — i.e., meaningfully
*smaller* than the Five Phases 15-21 construction, because every ingredient (closure operator,
reachability invariant, semantic cluster lemmas, Hintikka scaffolding, driver/specCore
patterns, completeness assembly template) exists; nothing is designed from scratch. My
inference; the main risk is the specCore re-derivation being tedious (it was the bulk of 524).

---

## 5. Decidability Payoff — Honest Assessment

**The universal-cluster route does not fix the `decide` kernel stall.** The stall
(`CslibTests/ModalFrameSeparation.lean:19-41`; task 525 handoff confirms `lake test` fails
pre-existing) is in the *driver*: `modalExpandBranchesGen`'s nested well-founded fuel
recursion does not reduce under kernel `rfl`/`decide`, and the `module`/`public meta import`
boundary blocks `#eval`/`native_decide` (`S5Simplification.lean:1959-1963`). That is
independent of which rule or extraction sits inside the driver. `instDecidableKb5Valid` will
exist and be correct (like `instDecidableFiveValid`, `FrameCompleteness.lean:3213`) but will
stall under kernel `decide` on concrete formulas exactly as its siblings do.

A *genuinely* "more decidable" S5/KB5 procedure — the textbook NP one (enumerate valuations of
the subformula closure over ≤ n+1-world single-cluster models, no tableau driver) — would be
kernel-friendlier and is enabled by the same small-model property, but it is a separate,
larger project (new procedure + its own soundness/completeness against `kb5FC`), and it is
**not needed** to finish KB5 completeness. Recommend tracking the driver-reduction stall as
its own task (structural-recursion driver or `Nat.rec`-style fuel loop), as the handoff also
suggested.

## 6. Tactic Survey Results

Not applicable — no live proof goals were attempted (research-only task; the deliverable is an
architecture assessment). The one anticipated new proof obligation (`w ≠ 0, v = 0` soundness
case) is a compositional one-liner over landed lemmas, not a tactic-search problem.

## 7. Uncertainty Flags

- "Least PER over a connected symmetric graph is total on its field" (Section 2.2) is my
  inference (standard graph/relation fact), not a landed lemma; it is *load-bearing only* for
  the claim that flat and closure extractions coincide extensionally, not for the fix itself.
- Scope estimate (4.4) is a judgment call; the specCore clone could be heavier than expected.
- Literature citations (Nagle–Thomason 1985, Ladner 1977) are from memory and not verified
  against local literature files (no `<literature-briefing>` was provided); the BdRV citation
  is already embedded in the repo's own blocker note.
