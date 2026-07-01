# Report 06 — Sfor Dedup / Loop-Check: Reuse & Abstraction Evaluation

- **Task**: 317 (evaluative research, standalone — NOT part of the 317 implementation lifecycle)
- **Question**: Does the Garg–Genovese–Negri (LICS 2012) `Sfor`-containment dedup / loop-check +
  fuel-sufficiency measure machinery being built for 317 present opportunities to (a) apply to
  other tableau/sequent developments in CSLib and/or (b) be abstracted into shared, reusable
  resources?
- **Method**: read the 317 artifacts + Lean sources; surveyed every `Tableau/` development in the
  repo (`grep`/`Read`), grounded against `Cslib/Foundations/Logic/Tableau/` and `ORGANISATION.md`.
- **Reference**: Garg, Genovese & Negri, "Countermodels from Sequent Calculi in Multi-Modal
  Logics", LICS 2012, pp.315–324 (`GargGenoveseNegri2012` — currently MISSING from `references.bib`,
  see report 05 §Q4).

---

## Executive Verdict

**The pattern is already pervasive and independently re-implemented at four sites.** The
Garg–Negri device (a world/point is not re-expanded when its forced-formula-set is contained in
an accessible ancestor's; distinct forced-sets number `≤ 2^|Sub(φ)|`, which bounds worlds and
makes a fixed fuel sufficient) is NOT unique to task 317. CSLib already contains:

- a **shared data layer** for tableaux (`Foundations/Logic/Tableau/`) — but it stops short of any
  termination / measure / blocking machinery;
- a **fully-realized counting-measure-over-a-fixed-finite-universe** instance (Modal K, task 442,
  `FmpMeasure.lean`, 3104 lines) — an alternative route to the same "strict decrease despite
  persistence" goal;
- a **fully-realized `Sfor`-containment device under a different name** ("time-subset blocking")
  in the Temporal tableau (`Temporal/Tableau/Branch.lean`) — whose *soundness* is currently
  `[BLOCKED]`;
- a **third subset-blocking + unexpanded-count-measure** instance in the Bimodal decidability
  procedure.

**Recommendation: abstract, but staged and AFTER task 317 lands — not now.** The duplication is
real and substantial (the three ingredients — forced-set/label-type primitive, containment
blocking, and `distinct-types ≤ 2^n` bound — recur verbatim in spirit), so this is not premature
abstraction in principle. But 317 is mid-implementation and is the *second* stable instance to
generalize from; generalizing from an in-flight instance risks churning both. Land 317 first, then
extract in three priority tiers (below). The single highest-value near-term payoff is that a
shared, once-proven "containment-blocking ⇒ bounded label-types ⇒ termination" lemma would
directly serve the **currently-blocked Temporal soundness obligation**
(`Temporal/Tableau/Soundness.lean` Phase 7).

---

## Part 1 — Core Reusable Ideas in Task 317

From reports 04/05 and `plans/04_sfor-dedup-fuel-sufficiency.md`, the three transferable ideas:

### 1a. The `Sfor` dedup invariant
- **Forced-set primitive**: `Sfor(w) := posFormulasAt bPers w` — the T-signed formulas holding at
  world `w` (`Intuitionistic/Rules.lean:126-128`).
- **Containment blocking rule** (plan 04, Phase 1, and report 05 §Q3-A): when `intFImpRule` would
  create a fresh world `w'` from `F(φ→ψ)@w`, first look for an accessible ancestor `x`
  (`isAccessible edges w x`) with `{φ} ∪ Sfor(w) ⊆ Sfor(x)` and `ψ ∉ forced(x)`; if found, **reuse
  `x`** (no new world, mark `F(φ→ψ)@w` expanded) instead of creating `w'`. Guarantees no two
  worlds on a branch have containment-equal forced-sets.
- This is exactly Garg–Negri's `Sfor`-set-containment termination condition (report 05 §7,
  citation #7).

### 1b. The loop-check / saturation condition
- Without dedup, `intExpandBranches`'s `expanded` set is keyed on the full `(sign, formula, label)`
  triple (`Intuitionistic/Expansion.lean:150-157`), so a `T(∨)` compound copied by
  `propagatePersistence` to each of `~complexity` fresh worlds re-splits at each — β-branchings
  multiply to `2^Θ(complexity²)` steps (report 04 F6; report 05 §Q2 "Crucial caveat").
- The dedup collapses the step count to the **deduplicated model size** `≤ 2^|Sub(φ)| · 2^|Sub(φ)|
  = O(2^{2n})`, at which point the *existing* fuel `2^(2·complexity+2)` becomes sufficient
  (report 05 §Q2; `Intuitionistic/Expansion.lean:295,308`).

### 1c. The fuel / termination measure
- **World bound**: `#worlds ≤ 2^|Sub(φ)|` (Garg–Negri antichain-of-forced-sets bound), with the
  weaker but self-contained **linear** fallback `W ≤ complexity + 1` (report 04 **F5**, a genuinely
  reusable lemma proved by subformula descent: only `F(φ→ψ)` creates worlds and it descends to
  `F(ψ)`; persistence copies only `.pos`, so F-formulas never persist).
- **Base-3 damped potential**: the F-signed potential `P = Σ 3^complexity` is persistence-invariant
  (report 04 F1–F3), mirroring the classical `classicalExpMeasure` template
  (`Classical/Completeness.lean:834` `classicalExpMeasure_step_lt`).
- **Well-foundedness**: `WellFounded.prod_lex` (`Mathlib.Order.RelClasses`) for the lexicographic
  `(worlds-remaining, intra-world-work)` object (report 04 F4).

---

## Part 2 — Candidate Reuse Sites (survey grounded in code)

### 2.0 The existing shared layer: `Cslib/Foundations/Logic/Tableau/` (741 lines)
The reuse-first check finds an existing shared tableau foundation:

| File | Provides | Termination-relevant? |
|------|----------|-----------------------|
| `SignedFormula.lean` | `SignedFormula F L`, `pos`/`neg`/`flip`/`withLabel`, `isPos`/`isNeg` | no |
| `Sign.lean` | `Sign`, `flip`, `LawfulBEq` | no |
| `Branch.lean` | `Branch F L := List (SignedFormula F L)`; `contains`, `positives`, `negatives`, `hasPosAt`, `formulasAt`, `labels`, `findContradiction`, `hasContradiction` | **partial** — `formulasAt`/`labels`/`positives` are the building blocks the per-logic "forced-set at a label" primitives specialize |
| `RuleResult.lean` | `RuleResult F L` with `linear`/`branching`/`persistent`/`notApplicable` + `isLinear`/`isBranching`/`isPersistent` | no (but the `persistent` variant is exactly what breaks naive complexity measures) |
| `ClosureCondition.lean`, `Closure.lean`, `PropositionalRules.lean` | closure predicates, the 8 propositional rules | no |

**Key gap**: `Foundations/Logic/Tableau/` has the *data* layer (signed formulas, branches, rules,
closure) but **no measure, no fuel, no world/label bound, and no containment-blocking layer**.
Every one of the four developments below re-implements that missing layer bespoke.

### 2.1 Classical propositional (`Tableau/Classical/`) — template, no dedup
- `classicalBranchComplexity` (`Classical/Completeness.lean:473`), `classicalExpMeasure`,
  `classicalExpMeasure_step_lt` (`:834`), `classicalExpandBranches_hintikka` (`:924`), fuel
  `3^complexity` (`Classical/Expansion.lean:163`).
- **Single world, no persistence** ⇒ `#β-splits = #compounds = O(c)` and `3^c` dominates. Needs no
  dedup. Value to 317: the *shape* of the `fuel=0 ⇒ saturated` closing argument (plan 04 Phase 7
  explicitly ports it). **Not a dedup reuse site**, but the canonical measure-proof skeleton.

### 2.2 Modal K (`Tableau/Modal/`, task 442) — the alternative route, fully realized
`FmpMeasure.lean` (3104 lines) solves the *same* "strict decrease despite persistent rules"
problem 317 faces, by a **different device**: instead of `Sfor`-containment dedup, it counts
against a **fixed finite universe**.

- `modalWorldBound φ := (2·c+1)^(c+1)` — **a-priori** world bound (`FmpMeasure.lean:119`).
- `modalUniverse φ` — all `(sign, subformula, world≤bound)` triples (`:124`).
- `modalWork U b e := |U\b| + |U\e|` — counting measure (`:180`).
- `modalExpMeasure U branches exp := Σ 3^(modalWork U bᵢ eᵢ)` — base-3 damped worklist measure
  (`:185`).
- `modalExpMeasure_entry_le_fuel` (`:196`), `modalExpMeasure_step_lt` (`:3018`), fuel
  `modalFuel` triple-exponential (`Saturation.lean:94`).
- Design note (`FmpMeasure.lean:47-56`): *"the persistent modal rules (`boxPos`, `diamondNeg`)
  re-fire without shrinking branch complexity, so a `3^complexity` exponent is non-decreasing on
  those rules. Counting against a fixed finite `U(φ)` restores strict decrease."* — this is the
  **exact same obstruction** report 04 F6 diagnoses for the intuitionistic persistence.

**Relationship to 317**: two solutions to one problem. Modal K bounds worlds a priori
(`Sf^(c+1)`) and counts against `U`; 317 bounds worlds by `Sfor`-dedup (`2^|Sub|`) and uses a
lex/base-3 potential. The **counting-measure-over-fixed-universe** (`modalWork`/`modalExpMeasure`)
is arguably the *cleaner* reusable core, because it sidesteps the per-step β-inflation without
needing the semantics-affecting dedup — and it is already proven. 317 could in principle have used
the modal counting-universe approach (fixed `U(φ)` with the linear world bound `W ≤ c+1` from
report 04 F5 as the label range) instead of dedup; the user chose dedup (plan 04, settled).

### 2.3 Temporal (`Tableau/Temporal/`) — `Sfor`-containment ALREADY implemented, soundness BLOCKED
`Temporal/Tableau/Branch.lean:101-174` is a **verbatim conceptual match** to the 317 dedup, under
the name **"time-subset blocking"**:

- `timeType b t := ((formulasAtTime b t).map (sign,formula)).eraseDups` (`:113`) — the forced-set
  primitive (= 317's `Sfor`, = a `(Sign × F)`-projected `Branch.formulasAt`).
- `isSubsetBlocked b t_new t_anc := timeType(t_new) ⊆ timeType(t_anc)` (`:120`) — the containment
  test (= 317's `{φ}∪Sfor(w) ⊆ Sfor(x)`).
- `isTemporallyBlocked` (`:160`) / `findBlockedTime` (`:171`) — the loop-check driver.
- `Saturation.lean:74`: *"the number of distinct time types is bounded by `2^n`"* — **literally the
  Garg–Negri `Sfor`-count bound** `2^|Sub(φ)|` that 317's Phase 5 (`intExpandBranches_world_bound_dedup`)
  is re-deriving.
- **Soundness is `[BLOCKED]`**: `Temporal/Tableau/Soundness.lean:23-54,169+` — Phase 7 is blocked on
  proving "time-subset blocking with unfulfilled eventualities implies unsatisfiability" and "a
  constructive loop-detection argument showing the blocked branch [yields a countermodel]". This is
  precisely the soundness half of the Garg–Negri device — the same obligation 317's plan 04 Phase 3
  ("re-verify countermodel/Hintikka conditions for reused worlds", risk R2) must discharge.

**This is the strongest reuse pull in the repo**: 317 and Temporal are solving the *same* soundness
problem for the *same* blocking device, in two files, independently, and Temporal is stuck on it.

### 2.4 Bimodal decidability (`Bimodal/Metalogic/Decidability/`) — third subset-blocking instance
- `Decidability/Tableau.lean`: `countUnexpanded` (`:1196`) and `totalUnexpandedComplexity` (`:1203`)
  — two termination-measure candidates; `AppliedSet` HashSet (`:1005`) tracking persistent outputs.
- `Decidability/DecisionProcedure.lean:203`: *"Combined with subset blocking…"* — a third subset-
  blocking site. Temporal's `Closure.lean:34` and `Saturation.lean:44` explicitly cite the Bimodal
  `Decidability/Saturation.lean` as the "blocking + eventuality tracking template" — so Temporal was
  already copied from Bimodal. The copy-lineage confirms the duplication is active, not hypothetical.

### 2.5 Duplicated arithmetic helpers (logic-agnostic, already copied)
- `sum_map_le_length_mul` (`FmpMeasure.lean:131`, `private`) — pure list arithmetic, no modal
  content; needed by any counting-measure-length bound.
- `modalCap Sf k = Σ_{i≤k} Sf^i` geometric-sum capacity (`FmpMeasure.lean:776-814`) — pure Nat
  arithmetic for world-tree size bounds.
- Base-3 domination boilerplate (`Nat.pow_le_pow_right`, `Nat.one_le_pow`) is hand-rolled in both
  `Classical/Completeness.lean:677-687,954` and `FmpMeasure.lean:238` — the same `3^a ≤ 3^C` / `1 ≤
  3^C` lemmas re-proved inline.

---

## Part 3 — Abstraction Assessment

### Is the duplication substantial enough to justify a shared module?
**Yes for two of three tiers; defer the third.** The three ingredients recur at 4 sites:

| Ingredient | Classical | Modal K (442) | Intuitionistic (317) | Temporal | Bimodal |
|---|---|---|---|---|---|
| forced-set / label-type primitive | — (1 world) | per-world `U` slice | `posFormulasAt` (Sfor) | `timeType` | time/world slice |
| containment / subset blocking | — | a-priori bound instead | `Sfor ⊆` (in progress) | `isSubsetBlocked` | "subset blocking" |
| `distinct-types ≤ 2^n` / world bound | trivial | `Sf^(c+1)` counting | `2^|Sub|` / `W≤c+1` | "≤ 2^n time types" | (implicit) |
| worklist counting measure + `step_lt` + `entry_le_fuel` | `classicalExpMeasure` | `modalExpMeasure` | (Phase 5, in progress) | `temporalFuel` (unproven) | `countUnexpanded` |

The forced-set primitive and the counting/worklist-measure skeleton are near-identical in shape
across sites; only the rule set and the label type differ. That is a textbook signal for a
label-generic (`F`, `L`)-parameterized abstraction — and `Foundations/Logic/Tableau/` already
parameterizes the data layer over exactly `(F, L)`, so the abstraction seam already exists.

### Why NOT abstract right now
1. **317 is mid-implementation** (plan 04, Phases 1–7 `[IN PROGRESS]`/`[NOT STARTED]`). Extracting a
   shared module while its second instance is being written invites double-churn (violates the
   convergence-policing spirit).
2. **The instances are at different maturities**: classical done, modal done, intuitionistic in
   flight, temporal blocked, bimodal partial. Generalizing from "done + done + in-flight" is
   defensible; but the cleanest generalization needs 317's dedup instance *finished* to know the
   final API shape (e.g. whether the blocking predicate needs the `ψ ∉ forced(x)` side condition
   generically).
3. **Two genuinely different strategies coexist** (counting-fixed-universe vs. Sfor-dedup). A shared
   module must either pick one or host both; that design choice is easier once 317's dedup lands and
   can be compared head-to-head with modal's counting universe.

### Where shared resources would live (ORGANISATION.md)
`ORGANISATION.md:20-22` — *"`Foundations/` provides infrastructure shared across all specific
logics."* The existing `Cslib/Foundations/Logic/Tableau/` is the correct home; new termination
infrastructure would be sibling files there (namespace `Cslib.Logic.Tableau`, already used). No new
top-level directory is needed.

---

## Part 4 — Prioritized, Actionable Recommendations

Every item is grounded in the files above. Ordering assumes **task 317 lands first**.

### R1 — Extract logic-agnostic measure arithmetic (LOW risk, HIGH certainty) → new small task
- **What**: a `Cslib/Foundations/Logic/Tableau/Measure.lean` hosting the pure helpers already
  duplicated: `sum_map_le_length_mul` (`FmpMeasure.lean:131`), the geometric-sum cap `modalCap` +
  `modalCap_le_pow` family (`FmpMeasure.lean:776-833`), and a small base-3 domination API (`3^a ≤
  3^C`, `1 ≤ 3^C`, `3^a+3^b ≤ 3^(1+max)`) to replace the inline copies in
  `Classical/Completeness.lean:677-687` and `FmpMeasure.lean:238`.
- **API sketch** (all `F`/`L`-free, pure `Nat`/`List`):
  ```
  lemma Tableau.sum_map_le_length_mul (l : List α) (f : α → Nat) (c : Nat)
      (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c
  def  Tableau.geomCap (base k : Nat) : Nat            -- Σ_{i≤k} base^i
  lemma Tableau.geomCap_le_pow {base k} (h : 2 ≤ base) : geomCap base k ≤ base ^ (k+1)
  ```
- **Cost/benefit**: ~80–150 lines moved, zero semantic risk (pure arithmetic), immediately
  de-duplicates modal↔classical. **Warrants a new task** (small `cslib`/refactor task; can be done
  independently of 317).

### R2 — Generalize the `Sfor`-containment / subset-blocking device (MEDIUM, HIGH value) → new task, after 317
- **What**: lift Temporal's `timeType`/`isSubsetBlocked`/`isTemporallyBlocked` and 317's
  `Sfor`/containment check to a single label-generic device in
  `Cslib/Foundations/Logic/Tableau/Blocking.lean`, built on the existing `Branch.formulasAt`
  (`Foundations/Logic/Tableau/Branch.lean:81`).
- **API sketch** (over the existing `Branch F L`):
  ```
  /-- The forced type at a label: the deduplicated (sign, formula) set at `l`. -/
  def Branch.typeAt [BEq F] [BEq L] (b : Branch F L) (l : L) : List (Sign × F)
  /-- `l_new` is subsumed by `l_anc` when its type is contained in `l_anc`'s. -/
  def Branch.containmentBlocked [BEq F] [BEq L] (b : Branch F L) (l_new l_anc : L) : Bool
  /-- Distinct forced-types over a subformula universe number ≤ 2^|U|. -/
  lemma Tableau.distinctTypes_le_pow (b : Branch F L) (U : List F)
      (hclosed : ∀ sf ∈ b, sf.formula ∈ U) :
      (b.labels.map (b.typeAt)).eraseDups.length ≤ 2 ^ U.length
  ```
  Temporal's `timeType`/`isSubsetBlocked` become `Branch.typeAt`/`containmentBlocked` specialized to
  `L = TimeIndex`; 317's `Sfor ⊆` becomes the `.positives`-projected instance at `L = WorldIndex`.
- **Highest-value payoff**: `distinctTypes_le_pow` is the shared, once-proven core of BOTH 317's
  `intExpandBranches_world_bound_dedup` (plan 04 Phase 5.1) AND the blocked Temporal soundness
  obligation (`Temporal/Tableau/Soundness.lean:23-54` "≤ 2^n time types" / loop-detection). Proving
  it once in Foundations could **unblock Temporal Phase 7**.
- **Cost/benefit**: the *definitional* lift is cheap; the *soundness* lemma (blocking ⇒ bounded ⇒
  countermodel) is the hard part — but it is hard *exactly once* here instead of 2–3 times.
  **Warrants a new task**, sequenced after 317 lands (so the `ψ ∉ forced(x)` side-condition shape is
  settled) and ideally co-scoped with the Temporal soundness unblock. Cite `GargGenoveseNegri2012`.

### R3 — Generic worklist counting-measure functor (HIGH cost, evaluate later) → defer, re-assess after R2
- **What**: a `Cslib/Foundations/Logic/Tableau/WorklistMeasure.lean` parameterizing the
  `expandBranches` + `work U b e := |U\b|+|U\e|` + `expMeasure := Σ 3^work` + `expMeasure_step_lt` +
  `expMeasure_entry_le_fuel` skeleton (currently `modalWork`/`modalExpMeasure`,
  `FmpMeasure.lean:180-3018`) over an abstract `(F, L, ruleStep)` interface, so Modal K,
  Intuitionistic, and Classical instantiate rather than re-prove it.
- **Cost/benefit**: this is the biggest de-duplication (the 3104-line `FmpMeasure.lean` is ~30–40%
  logic-agnostic scaffolding) but also the riskiest: the per-rule `step_lt` proofs are deeply tied
  to each rule catalogue, and the abstraction boundary (what the generic `ruleStep` must guarantee:
  "each step adds ≥1 element to `b` or `e`, both ⊆ finite `U`") must be gotten exactly right. **Do
  NOT attempt until there are three *finished* instances** (classical + modal + intuitionistic-317)
  to generalize from — abstracting from two is premature, abstracting from three is grounded. **Defer;
  re-assess after 317 lands and R2 is done.**

### Sequencing summary
```
land 317 (dedup instance) ──► R1 (cheap arithmetic extraction, independent, do anytime)
                             └► R2 (generalize blocking device; unblocks Temporal soundness)
                                   └► R3 (worklist-measure functor; only with 3 finished instances)
```

### On the reuse-first mandate
The reuse-first check was run: `Foundations/Logic/Tableau/` already exists and already hosts the
`(F,L)` data layer, so R1/R2 are *extending* an existing shared module, not creating a speculative
one. That is the low-risk, sanctioned direction. R3 is the one place where premature abstraction
would genuinely hurt, hence the explicit defer.

---

## Files Referenced (absolute paths)
- `Cslib/Foundations/Logic/Tableau/{Branch,SignedFormula,Sign,RuleResult,ClosureCondition,Closure,PropositionalRules}.lean`
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` (473, 677-687, 834, 924, 954)
- `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` (163)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Rules.lean:126-159, Expansion.lean:150-157,295,308, Scheme.lean}`
- `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (47-56, 119, 124, 131, 180, 185, 196, 776-833, 3018)
- `Cslib/Logics/Modal/Tableau/Saturation.lean` (94)
- `Cslib/Logics/Temporal/Tableau/Branch.lean` (101-174), `Saturation.lean` (44, 74), `Soundness.lean` (23-54, 169+), `Closure.lean` (34)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` (1005, 1196, 1203), `DecisionProcedure.lean` (203)
- `ORGANISATION.md` (20-22, 127-135)
- `specs/317_propositional_tableau_completeness/reports/{04,05}_*.md`, `plans/04_sfor-dedup-fuel-sufficiency.md`
