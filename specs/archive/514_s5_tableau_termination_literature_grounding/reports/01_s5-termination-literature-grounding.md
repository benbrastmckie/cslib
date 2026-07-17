# Research Report: Task #514 — S5 Tableau Termination Obstruction, Literature-Grounded

- **Task**: 514 — s5_tableau_termination_literature_grounding (grounds task 504's Phase-2
  obstruction; feeds task 515)
- **Type**: cslib (research; orchestrator mode)
- **Session**: session_01URooV1ZJEr3MiTi2gxDuLW
- **Date**: 2026-07-14
- **Files studied (read-only)**: `Cslib/Logics/Modal/Tableau/{GenericDriver,S5Simplification,
  FrameCompleteness,BDriver,LoopChecking}.lean`; `specs/504_*/summaries/01_*.md`;
  `specs/511_*/{reports,plans}/01_*.md`.
- **Literature (via `--lit` / `literature-search.sh`)**: Massacci2000 (doc_id
  `massacci_2000_single_step_tableaux_for_modal_logics`, chunks 32–35 primary), with in-corpus
  surrogates for the paywalled Gore1999. BibKeys verified present in `references.bib`:
  `Massacci2000` (l.974), `Gore1999` (l.987), `ChagrovZakharyaschev1997` (l.75), `Fitting1983`
  (l.211).
- **Central deliverable**: a BibKey-cited confirmation that task 504's mechanized
  `modalApplyOneS5_rankStep_not_dischargeable` is a faithful Lean instance of a *known,
  published* obstruction (transitive/euclidean logics admit no per-edge modal-depth decrement),
  plus a lemma-level recommendation that task 515 rebuild S5 termination on the **loop-checking
  world-bound interface already landed for S4** (task 511, `LoopChecking.lean`), not on
  `RuleApplicationSpec`'s rank machinery.

---

## Executive Summary

Four findings, in decreasing order of impact on task 515's plan:

1. **[The obstruction is real and named in the literature — not a CSLib artifact.]**
   Task 504's `modalApplyOneS5_rankStep_not_dischargeable` (S5Simplification.lean:342, sorry/
   axiom-free) proves the `RuleApplicationSpec.rankStep` field (GenericDriver.lean:213) is
   *mathematically false* for the universal S5 rule. Massacci2000 §8 states the general fact this
   instantiates: for **transitive and euclidean logics (K4, S4, K45, KD45, S5)** the naive
   depth-based termination fails and must be replaced either by **loop-checking** or by a
   **prefix-length bound** `hbL` — a *local* check on the world-path length of the formula being
   reduced, *not* a modal-depth decrement (Massacci2000, Technique 8.3, Lemma 8.3, Theorem 8.4,
   chunk 33). The edge-local rank-potential argument the CSLib driver presupposes is exactly the
   `1+d` measure Massacci reserves for the **non-transitive** logics `K, D, T, KB, KDB, B`
   (Table IV, chunk 32) — the same family for which CSLib's K/T/B *do* discharge the spec, and
   which excludes S4/S5 by design.

2. **[S5's terminating strategy is the S4 loop-checking world-bound — already built in CSLib.]**
   Massacci proves S5 needs no new termination device beyond S4's: "An S4 model is also an S5
   model. So, this technique also works for K45 and S5" (chunk 35). CSLib **already landed** the
   Lean realisation of S4's device in task 511 (`LoopChecking.lean`, 0 sorries): a birth-content
   minting guard (`blockingWorldS4`/`successorBirthContent`), a pigeonhole world bound
   `modalWorldBoundS4 φ₀ := 2 ^ (2 * |modalSubfmls φ₀|)`, a finite universe `modalUniverseS5`-
   analogue `modalUniverseS4`, and a stable-key loop invariant `S4LoopInv`. **Task 515 should
   mirror this file declaration-for-declaration**, exactly as S5Simplification.lean already
   mirrors BDriver.lean for the (dead) rank route.

3. **[`rankStep` is the single field to drop; the depth-based `modalWorldBound` universe is the
   second thing to replace.]** S5 should stop being a `RuleApplicationSpec` instance (S4 already
   is not — GenericDriver.lean:126). The two load-bearing removals are `rankStep` (provably
   false) and the reliance of `outputsSubsetUniverse` on the depth-based `modalWorldBound φ0`
   (the `geomCap` tree capacity), which is replaced by the pigeonhole `modalWorldBoundS5 :=
   2^(2|Sf|)` and the `modalUniverseS5` catalog. The counting-measure/shape fields
   (`freshLocal`, `persistentFresh`, `outDegStep`, `knownWorldsStep`, `branchingLength`) and the
   Hintikka/saturation fields F8–F12 survive essentially intact, re-targeted at the S5 universe —
   but the K minting arms must acquire the S4-style blocking guard, so `freshLocal`/
   `knownWorldsStep` take their loop-back-edge variant.

4. **[No K/T/B regression; the natural home is a shared loop-termination interface.]** Because K,
   T, B keep `RuleApplicationSpec` untouched and S5 becomes a sibling instance of the same
   loop-checking machinery S4 uses, there is **zero regression risk** to the existing
   instantiations. The cleanest architecture is the generalized `LoopTermination` interface that
   task 511's Phase-9 research (report §3, Option 9-A) already recommends abstracting in
   `CompletenessLoop.lean` for S4/505/513 — S5 becomes one more consumer of it. Task 515 must
   coordinate with, or explicitly fork from, that interface decision.

Zero-debt is respected throughout: no recommended path relies on `sorry`, `axiom`, or a vacuous
placeholder. Where a proof is heavy, the recommendation is decomposition mirroring task 511's
phase structure, not deferral.

---

## 1. The Mechanized Obstruction, Stated Precisely

### 1.1 What `rankStep` demands (GenericDriver.lean:213–226)

`RuleApplicationSpec.rankStep` is the FMP rank-potential contract. Given any `rank :
WorldIndex → Nat` satisfying, *pre-call*, the two invariants

- **depth bound** `∀ x ∈ b, modalDepth x.formula ≤ rank x.label`, and
- **edge decrement** `∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w`,

the rule must exhibit a `rank'` (agreeing with `rank` off `modalNextWorld b`) that re-establishes
both invariants on the rule's output. The edge-decrement clause is the crux: it says a world's
rank is *one less than* its predecessor's along every recorded edge, so `rank` is literally the
**remaining modal-depth budget**, decremented one unit per accessibility step. The depth bound
then says every formula sitting at a world fits inside that world's budget.

### 1.2 Why K/T/B satisfy it and S5 cannot (verified against source)

- **K** (`modalApplyOne_spec`, GenericDriver.lean:334): mints a fresh successor `modalNextWorld b`
  one edge deeper and emits the *unwrapped body* there — depth drops by exactly one, matching the
  edge decrement. Discharged by `modalApplyOne_rank_step`.
- **T** (`TDriver.lean`): self-propagation, target = the trigger's *own* world `w`, so
  `rank w' = rank w` trivially and the body's depth `< rank w` still holds.
- **B** (`modalApplyOneB_rankStep`, BDriver.lean:460–466, read): backward propagation to a
  *recorded-edge predecessor* `v` of `w`; because `acc.hasEdge v w`, the pre-call `hedge`
  hypothesis *directly* gives `rank w + 1 = rank v`, pinning the target's budget. B reuses K's
  `rank'` witness verbatim since it never touches `acc`.

  **Common structural feature**: every K/T/B target world is edge-related to the trigger, so
  `hedge` controls the target's rank.

- **S5** (`modalApplyOneS5`, S5Simplification.lean:153; `modalS5BoxAll`, l.69): the universal rule
  propagates `T(φ)@w'` to **every** `w' ∈ modalKnownWorlds b`, *unconditionally on any edge*. A
  known world `v` may sit in a disjoint mint-subtree with no recorded path to `w`, so `hedge`
  says nothing about `rank v` versus `rank w`. The mechanized counterexample
  (`modalApplyOneS5_rankStep_not_dischargeable`, S5Simplification.lean:342): `φtest = ◇◇(atom 0)`
  (`modalDepth = 2`), branch `[T(□φtest)@0, T(atom 0)@3]`, chain `0→1→2→3`, tight rank
  `rank w = 3 − w`. Both hypotheses hold, yet the rule emits `T(φtest)@3` (world 3 is known) while
  `modalDepth φtest = 2 > rank 3 = 0`; since `3 ≠ modalNextWorld b = 4`, every admissible `rank'`
  is forced to `rank' 3 = 0`. **The field is false, by `rfl`+`omega`, not merely unproved.**

This is the same class of obstruction the module docstring already records for S4
(GenericDriver.lean:126–129): both propagate content to worlds "whose depth-budget is not
controlled by any recorded edge to the trigger world" (S5Simplification.lean:338–341).

---

## 2. Literature Grounding (Massacci2000, cross-checked to the mechanized obstruction)

### 2.1 SST propagates along the *prefix tree*, and bounds *prefix length*, not formula depth

Massacci2000's Single-Step Tableaux (SST) label formulas with **prefixes** `σ` — world-paths
such as `1.n₁.n₂` — whose parent→child extension *is* the accessibility structure (Massacci2000
§3–4, chunk 11). The box (ν-) rule sends `σ:□A ⇒ σ.n:A` and, for transitive logics, the (4) rule
adds `σ:□A ⇒ σ.n:□A` (Proposition 8.1, chunk 34: "if σ₀ is an initial subsequence of σ, then
σ₀:□A ∈ B implies σ:□A ∈ B"). Crucially, **propagation is always edge-structured along the prefix
tree** — never a broadcast to arbitrary worlds. Termination is then obtained by bounding **prefix
length** (equivalently, R-path length), *not* by decrementing formula depth:

> Technique 8.3. For every logic L the application of the single step tableau π-rule is limited to
> prefixes whose length is less than `hbL`. (Massacci2000, chunk 32)

> **Table IV — Bounds for decidability checks** (Massacci2000, chunk 32/34)
> | Logic L | Bound `hbL` |
> |---|---|
> | K, D, T, KB, KDB, B | `1 + d` |
> | K4, KD4, S4 | `2 + d·p + p·n` (= `2 + d + n·p`, chunk 34) |

> "We have replaced loop checking for SST with a simple local check." (Massacci2000, chunk 34)

**Cross-check to CSLib.** CSLib's `RuleApplicationSpec.rankStep` *is* Massacci's `1 + d`
regime: a per-edge modal-depth decrement, valid precisely for the **non-transitive** family
`K, D, T, KB, KDB, B` — which is exactly the set for which CSLib discharges the spec (K/T/B) and
exactly the set from which S4/S5 are excluded (GenericDriver.lean:109–129). The mechanized S5
counterexample lands in the gap Massacci identifies: transitive/euclidean logics fall outside the
`1+d` measure. The published fact and the Lean obstruction agree at the level of the *measure*,
not merely the *conclusion*.

### 2.2 Why S5 (universal/global modality) specifically needs loop-checking / a global bound

The universal S5 rule (broadcast box to all worlds) is the extreme case: there is *no* prefix
tree to bound because every world is mutually accessible (one cluster). Massacci's own remedy for
the euclidean family is to **reuse the S4 bound**:

> "An S4 model is also an S5 model. So, this technique also works for K45 and S5." (Massacci2000,
> chunk 35)

That is: bound the number/length of distinct world-states, then any world beyond the bound is a
*repeat* (loop) and need not be expanded. Massacci frames S4/S5 termination semantically via the
longest-simple-R-path property:

> Fact 9.3. If deciding L-satisfiability is PSPACE-complete, for every L-satisfiable formula A
> there is an L-model where the longest simple R-path is bounded by a polynomial … The
> termination check in Section 8 is a reformulation of this property. Theorem 8.4 simply says that
> the length of the longest R-path is `hbL`. (Massacci2000, chunk 35)

And S5 is in fact *easier* than S4 semantically — a finite-model / filtration argument gives
**polynomial-size** single-cluster models:

> "For K45, KD45, and S5, deciding validity is 'only' co-NP-complete … Fact 9.1: if deciding
> L-satisfiability is NP-complete, for every L-satisfiable formula A there is an L-model whose
> size (number of worlds) is polynomially bounded." (Massacci2000, chunk 35; the complexity
> result is Halpern–Moses, cited as [22].)

The underlying finite-model-property machinery (filtration collapsing an S5 model to one
equivalence class of bounded size) is the classical route surveyed in
`ChagrovZakharyaschev1997` (filtration, FMP) and the Handbook chapter `Gore1999` (tableau
loop-checking for K4/S4/S5); both are the standard references for "why a depth measure is
insufficient and a loop-check / bounded-model argument is required." (Gore1999's PDF is
outstanding/paywalled; the in-corpus `ChagrovZakharyaschev1997` and the polynomial-model facts
above supply the same content.)

**Net literature verdict.** The mechanized obstruction is not a Lean encoding accident. It is the
expected consequence of the S5 rule being a *universal/global* modality: no edge-local depth
decrement exists (Massacci reserves that for `K…B`), and the correct terminating device is a
**bound on the number of distinct world-states** (loop-checking / prefix bound / filtration),
which for S5 may reuse the S4 bound.

---

## 3. The Concrete Terminating Strategy, Mapped onto the CSLib Driver

Three literature strategies exist; they collapse onto **one** Lean realisation already present in
the codebase.

### 3.1 Strategy 1 (RECOMMENDED): loop-checking world bound — mirror S4 (`LoopChecking.lean`)

**Literature basis**: Massacci Technique 8.3 + Table IV + "works for K45 and S5" (chunk 35);
Gore1999 loop-checking. **Lean realisation**: task 511's landed, sorry-free `LoopChecking.lean`
(verified: `grep -c sorry` = 0), transposed to S5.

The essential mechanism is a **birth-content minting guard** plus a **pigeonhole world bound**:
- The K minting arms (`F(□ψ)@w`, `T(◇ψ)@w`) consult a blocking function before minting a fresh
  world; if an existing world already realises the prospective successor's birth content, add a
  loop-back edge instead of a new world (`blockingWorldS4`/`successorBirthContent`,
  LoopChecking.lean:51–55, 359–362).
- A stable per-world **birth key** (never changes after birth) makes pairwise world-distinctness a
  genuine loop invariant (`S4LoopInv` fields `keysTotal`/`keyLowerBd`/`keysDistinct`/
  `keysInUniverse`, LoopChecking.lean:40–41), injecting worlds into the finite powerset of signed
  subformulas.
- The pigeonhole then bounds `#worlds ≤ modalWorldBoundS4 φ₀ = 2^(2·|modalSubfmls φ₀|)`
  (LoopChecking.lean:229, 288–315), which sizes fuel for decidability.

**Why S5 needs the guard at all (independent confirmation the rank route was not merely unproven
but that the rule diverges).** `modalApplyOneS5`'s universal dia-negative arm (`modalS5DiaNegAll`,
S5Simplification.lean:80) sends `F(◇ρ)@w ⇒ F(ρ)@w'` for every known `w'`. When `ρ = □χ`, each
copy `F(□χ)@w'` is a fresh box-negative that mints a new world; every new world re-enters
`modalKnownWorlds b`, causing existing universal box-positives to re-broadcast to it, which can
mint again. Absent a blocking guard this cascades without bound — precisely the divergence
loop-checking exists to cut, and precisely why the depth-fuel `modalFuel`/`modalWorldBound` the K
driver ships is unsound for S5. This is the S5 analogue of task 511 §2's Gap-1/Gap-2 analysis.

**Mapping onto `RuleApplicationSpec` — which fields change or are replaced:**

| Field (GenericDriver.lean) | Fate for S5 | Reason |
|---|---|---|
| `rankStep` (l.213) | **DROP** | Provably false (`modalApplyOneS5_rankStep_not_dischargeable`). This is the one irreducible removal. |
| `outputsSubsetUniverse` (l.191) | **REPLACE universe** | Its `modalWorldBound φ0` (depth/`geomCap` tree) → `modalWorldBoundS5 := 2^(2|Sf|)` and `modalUniverseS5` (mirror `modalUniverseS4`, LoopChecking.lean:237). |
| `freshLocal` (l.181) | **VARIANT** | Add the loop-back-edge alternative (guard adds `acc.addEdge w wBlock` with a `.linear []` result), as S4's guard does. |
| `knownWorldsStep` (l.245) | **VARIANT** | Same loop-back dichotomy: mint-or-loopback, both landing in known worlds. |
| `outDegStep` (l.231), `persistentFresh` (l.205), `branchingLength` (l.263) | **KEEP** (re-targeted) | Counting/shape facts; universal arm is `.persistent` at existing worlds, so these transfer as in B/T. |
| `localShapeInvariance` F8 (l.273) | **KEEP** | Non-modal shapes reduce to K (`modalApplyOneS5_eq_of_not_boxPos_diaNeg`, l.181). |
| `boxPosNotExpanding` F9 (l.287), `diaNegNotExpanding` F10 (l.295) | **KEEP** | The universal arms emit `.persistent`/`.notApplicable` only — F9/F10 were *deliberately payload-weakened* (l.283–285) so T/B/S5 universal propagation discharges them. Already true for S5 by construction. |
| `boxNegWitness` F11 (l.307), `diaPosWitness` F12 (l.316) | **KEEP but guard-adjust** | With the blocking guard these hold only on the *unblocked* mint branch; F11/F12 need the S4 guarded form. |

**Consequence**: S5 is **not** a `RuleApplicationSpec` witness. It is an instance of the
loop-checking termination interface. The 11-field spec is *split*: F8–F12 (completeness/Hintikka,
spec-free-ish) remain reusable, while the termination fields (`rankStep` + the depth-universe
dependence of `outputsSubsetUniverse`, `freshLocal`, `knownWorldsStep`, F11/F12) migrate to an
`S5LoopInv`-parametrised set, mirroring `S4LoopInv`.

### 3.2 Strategy 2 (alternative, not recommended as primary): semantic filtration / bounded-model FMP

**Literature basis**: Massacci Fact 9.1/9.3 (polynomial single-cluster models);
`ChagrovZakharyaschev1997` filtration. Decide `s5Valid φ` by searching models of size ≤ a
computed polynomial bound, bypassing tableau termination entirely. CSLib already has the
completeness-side extractor `extractModelS5` (EqvGen closure, FrameCompleteness.lean; task 504
Phase 3, landed sorry-free) and `extractModelS5_rightEuclidean`. **Downside**: this is a *different*
decision procedure — it discards the generic tableau driver, needs a fresh bounded-model
enumeration + a filtration truth lemma, and duplicates rather than reuses the S4 infrastructure.
Recommended only if Strategy 1's guard proves intractable.

### 3.3 Strategy 3 (equivalent to Strategy 1 in Lean): global caching

**Literature basis**: Gore1999 global-caching tableaux. In a functional Lean setting this is just
Strategy 1's blocking table threaded globally; it offers no distinct Lean formalisation advantage
over the per-branch birth-key guard S4 already uses. Fold into Strategy 1.

---

## 4. Lemma-Level Recommendation for Task 515

Rebuild S5 termination as a **declaration-for-declaration transpose of `LoopChecking.lean`**,
replacing the S4 transitive-4 rule slot with the S5 universal rule slot. Concrete deliverables
(signatures; all expected to close without `sorry`/`axiom`, mirroring the landed S4 lemmas):

```lean
/-- Pigeonhole world bound for S5 (mirror `modalWorldBoundS4`, LoopChecking.lean:229). -/
def modalWorldBoundS5 (φ₀ : Proposition Atom) : Nat := 2 ^ (2 * (modalSubfmls φ₀).length)

/-- Finite catalog at bounded worlds (mirror `modalUniverseS4`, LoopChecking.lean:237). -/
def modalUniverseS5 (φ₀ : Proposition Atom) : List (SignedFormula (Proposition Atom) WorldIndex)

/-- Prospective birth content of the guarded successor (mirror `successorBirthContent`). -/
def successorBirthContentS5 (φ₀ …) (s φ w) : Finset (Sign × Proposition Atom)

/-- Blocking guard on the K minting arms (mirror `blockingWorldS4`). -/
def blockingWorldS5 (φ₀ …) (s φ w) : Option WorldIndex

/-- Guarded S5 rule: `modalApplyOneS5` with the two K minting shapes routed through
    `blockingWorldS5` before falling through to the universal-propagation arms. -/
def modalApplyOneS5g (sf b acc) : RuleResult … × Accessibility

/-- Stable-key loop invariant (mirror `S4LoopInv`; four key fields + the rule-independent
    universe fields). -/
structure S5LoopInv (φ₀ b e acc keys) : Prop where
  keysTotal    : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys
  keyLowerBd   : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w
  keysDistinct : ∀ w w' k k', (w,k) ∈ keys → (w',k') ∈ keys → w ≠ w' → k ≠ k'
  keysInUniverse : ∀ w k, (w,k) ∈ keys → k ⊆ signedSubfmls φ₀
  -- + the rule-independent fields over modalUniverseS5

/-- Preservation lemmas (mirror `modalStepBranchS4_preserves_*`). -/
lemma modalStepBranchS5_preserves_keyLowerBd   …
lemma modalStepBranchS5_preserves_keysDistinct …    -- guard contract at minting; monotone at persistent
lemma modalStepBranchS5_preserves_keysTotal / _keysInUniverse …

/-- Pigeonhole world bound (mirror `modalKnownWorlds_length_le_worldBoundS4`, l.288). -/
lemma modalKnownWorlds_length_le_worldBoundS5 (hInv : S5LoopInv φ₀ b e acc keys) :
    (modalKnownWorlds b).length ≤ modalWorldBoundS5 φ₀

lemma modalStepBranchS5_worldBound … : modalMaxWorld b < modalWorldBoundS5 φ₀

/-- Decidability, once the world bound sizes fuel (mirror `instDecidableTValid`,
    FrameCompleteness.lean:1281 / `instDecidableBValid`, l.1896). -/
instance instDecidableFiveValid (φ0) : Decidable (fiveValid φ0)   -- and/or s5Valid / kb5Valid
```

**Key reuse verdicts** (CSLib reuse-first; verified against source):

| Concept | Existing asset | Verdict |
|---|---|---|
| Birth-content guard + stable keys + pigeonhole | `blockingWorldS4`/`successorBirthContent`/`S4LoopInv`/`modalWorldBoundS4`/`modalUniverseS4` + `modalKnownWorlds_length_le_worldBoundS4` (LoopChecking.lean, landed 0 sorries) | **Transpose** — the template. Swap the 4-rule slot for the S5 universal slot. |
| S5 universal arms + agreement lemma | `modalS5BoxAll`/`modalS5DiaNegAll`/`modalApplyOneS5_eq_of_not_boxPos_diaNeg` (S5Simplification.lean) | **Reuse** — the rule content is done; only the *minting guard* wrapper is new. |
| Countermodel (completeness side) | `extractModelS5` + `_rightEuclidean` (FrameCompleteness.lean, task 504 Ph3) | **Reuse** — independent of termination. |
| Universe/fuel counting engine | `modalWork`/`modalExpMeasure` (FmpMeasure.lean) | **Reuse verbatim** (universe-parametric). |
| Generic Hintikka predicate + loop | `modalHintikkaSetGen` (spec-free); `modalExpandBranchesGen_hintikka` (needs `RuleApplicationSpec`) | Predicate: **reuse**. Loop lemma: **cannot reuse** (needs rank fields) — same blocker task 511 §3 hit; consume the `LoopTermination` generalization instead. |
| Pigeonhole | `Finset.card_powerset`, `Finset.card_le_card_of_injOn`, `List.Nodup.length_le_card` | Mathlib, confirmed present in task 511. |
| Rank machinery `ModalPotentialInv`/`rankStep` | GenericDriver.lean / FmpMeasure.lean | **Do NOT reuse/extend** — provably inapplicable. `S5LoopInv` is a sibling. |

**Coexistence / regression**: K/T/B keep `modalApplyOne`/`modalApplyOneT`/`modalApplyOneB` and
their `RuleApplicationSpec` witnesses **unchanged**. S5's guard is a new file (or new section)
consuming the S4-style interface; nothing edits `GenericDriver.lean`'s spec, `FmpMeasure.lean`, or
the K/T/B declarations. No notation change (guard/invariant are plain defs/structures). No new
axiom.

---

## 5. Recommended Decomposition, Risks, Zero-Debt Posture

**Phase structure for task 515's plan (mirrors task 511's landed plan):**
1. **P1 — S5 bound + universe**: `modalWorldBoundS5`, `modalUniverseS5`,
   `modalUniverseS5_length_le`. Independent, green, commit.
2. **P2 — Guard**: `successorBirthContentS5`, `blockingWorldS5`, `modalApplyOneS5g`; prove the
   non-minting behaviour still agrees with `modalApplyOneS5`/K (so completeness-side lemmas that
   depend only on the universal arms are unaffected). Re-run CI on S5's consumers.
3. **P3 — `S5LoopInv` + four preservation lemmas** (the mathematical crux; budget generously, as
   task 511 did for S4 Phase 5).
4. **P4 — Pigeonhole** `modalKnownWorlds_length_le_worldBoundS5` + `modalStepBranchS5_worldBound`.
5. **P5 — Fuel sufficiency + `Decidable (fiveValid/s5Valid/kb5Valid φ)`** — **gated** on the
   Phase-9 `LoopTermination` interface decision (task 511 §3, Option 9-A vs 9-B). Land [BLOCKED]
   with a precise handoff if the shared interface is not yet available, **not** a `sorry`.

**Risks:**
- **Interface coupling (highest)**: S5 decidability (P5) inherits task 511's Phase-9 blocker —
  `modalExpandBranchesGen_hintikka` requires `RuleApplicationSpec` + rank fields, which S5 (like
  S4) cannot supply. P5 must consume the generalized `LoopTermination` interface (Option 9-A) or
  an S5-local re-derivation (9-B). **Coordinate task 515 with the S4 Phase-9 interface task**;
  do not duplicate.
- **Guarded rule vs completeness proofs**: adding the guard changes the *minting* behaviour;
  verify the S5 truth-lemma/Hintikka bridges (which depend on the *universal-arm* behaviour,
  unchanged) still build.
- **Bound size**: `2^(2|Sf|)` is loose (S5 is genuinely polynomial per Fact 9.1) but only sizes
  fuel, never computed — harmless for decidability, matching S4.

**Zero-debt**: every lemma above is expected to close without `sorry`/`axiom`; the S4 siblings all
did. If a preservation lemma resists within a run, mark that phase [BLOCKED] with the exact open
goal and split — **do not** weaken `S5LoopInv` to something vacuous, and **do not** re-introduce a
rank axiom to bridge the gap.

---

## 6. Open Questions for the Planner

1. **New file vs section?** Recommend a new `S5LoopChecking.lean` (or a "Termination" section
   appended to `S5Simplification.lean`) mirroring `LoopChecking.lean`, keeping the guarded rule
   `modalApplyOneS5g` distinct from the current unguarded `modalApplyOneS5` (which remains valid
   for the completeness-side content).
2. **Shared `LoopTermination` interface (Option 9-A) or S5-local (9-B)?** 9-A unifies S4/S5/505/513
   and is the reuse-first choice, but is a cross-cutting shared-file task requiring coordination;
   9-B is self-contained but duplicative. This is the same fork task 511 left open — resolve once
   for both.
3. **Which validity targets?** `fiveValid`, `kb5Valid`, and/or `s5Valid` — FrameCompleteness.lean
   already flags `fiveValid`/`kb5Valid` completeness as transitively blocked on the (now-to-be-
   replaced) S5 proof engine (l.571–578); confirm the intended decidability surface with the S5
   route now unblockable via loop-checking.

---

## References (BibKeys verified in `references.bib`)

- **Massacci2000** — F. Massacci, *Single Step Tableaux for Modal Logics*, J. Automated Reasoning
  24(3):319–364, 2000. §8 (Technique 8.3, Table IV, Lemma 8.3, Theorem 8.4, chunks 32–34); §9
  (Facts 9.1/9.3, complexity, chunk 35). **Primary source**: prefix-length termination replacing
  loop-checking; S5/K45 reuse the S4 bound.
- **Gore1999** — R. Goré, *Tableau Methods for Modal and Temporal Logics*, Handbook of Tableau
  Methods, pp.297–396, 1999. Standard survey of loop-checking / global-caching for K4/S4/S5. PDF
  outstanding/paywalled; content covered by Massacci2000 §8 and ChagrovZakharyaschev1997.
- **ChagrovZakharyaschev1997** — Chagrov & Zakharyaschev, *Modal Logic*, 1997. Filtration and the
  finite model property for S5 (surrogate for the FMP/bounded-model route, Strategy 2).
- **Fitting1983** — M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*, Ch.2.
  Already cited in `S5Simplification.lean`; prefixed-tableau ancestry of SST.
