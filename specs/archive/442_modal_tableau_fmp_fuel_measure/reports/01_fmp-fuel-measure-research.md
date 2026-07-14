# Research Report: Modal K Tableau FMP Fuel Measure (Task 442)

**Task**: 442 — Modal K Tableau FMP Fuel Measure
**Agent**: cslib-research-hard-agent
**Date**: 2026-06-30
**Reference grounding tier**: Tier 1 (literature-backed: Fitting1983 / Smullyan1968) + Tier 3 (implementation-backed: classical template + green modal soundness/completeness)
**Unblocks**: task 299 Phase 6 (`modalExpandBranches_hintikka`) and Phase 7 (`modalTableau_decides`, `Decidable`)

---

## Executive Decision (the CRUX, resolved)

**Measure structure**: Adopt a **single fully-exponential per-branch measure** `3 ^ R(b,e)` where the
exponent is a **counting** measure over a fixed finite signed-formula universe `U(φ)`:

```
R(b, e) := |U(φ) \ set(b)| + |U(φ) \ set(e)|
```

(number of universe elements not yet on the branch, plus number not yet expanded). This is the plan's
own `R = (|U|−|branch∩U|)+(|U|−|exp∩U|)` sketch (`plans/05...:472`), and it is **correct** — but only
because, after verifying the code, the counting measure `R` (NOT a complexity measure) is the unique
form that strictly decreases on **all four modal rule kinds including the re-firing persistent rules**.

**Exact new `modalFuel` closed form**:

```lean
def modalFuel (φ : Proposition Atom) : Nat := 3 ^ (2 * (modalUniverse φ).length)
```

with `(modalUniverse φ).length ≤ 2 · Sf(φ) · (W(φ) + 1)`, `Sf(φ) := 2·modalComplexity φ + 1`
(distinct-subformula over-count), `d(φ) := modalComplexity φ ≥ modalDepth φ`, and world bound
`W(φ) := Sf(φ) ^ (d(φ)+1)`. Fully expanded, a provably-sufficient closed-form Nat is:

```
modalFuel φ  =  3 ^ ( 4 · (2n+1) · ( (2n+1)^(n+1) + 1 ) )     where n = modalComplexity φ
```

This is a triple-exponential over-count. **Sufficiency, not tightness, is the requirement** (zero-debt),
and the double/triple-exponential slack is harmless because `modalFuel` never appears in soundness
(`modalExpandBranches_closed_unsat` is fuel-agnostic, `Soundness.lean:165/226`).

**Why fuel ≥ that guarantees saturation before `fuel = 0`**: At the entry point
`modalTableau φ = modalExpandBranches [ [F(φ)@0] ] [[]] [empty] (modalFuel φ)` the initial worklist
measure is `modalExpMeasure = 3 ^ R([F(φ)@0], []) ≤ 3 ^ (2·|U|) = modalFuel φ` (since `R ≤ 2|U|` always).
Each `modalStepBranch = some` step strictly decreases the worklist measure by ≥ 1 (proved by the
per-rule `R`-drop lemma + base-3 damping). Therefore the measure is `< fuel` throughout, so `fuel = 0`
is reached only when the worklist is empty (all branches closed) — never with an unsaturated open branch.
This is the exact contract of the classical `classicalExpandBranches_hintikka` (`.../Classical/Completeness.lean:924`),
transplanted with `classicalBranchComplexity` replaced by `R`.

**The irreducible crux and top risk** (see §6): the `R`-drop for the fresh-world-creating and
persistent rules is valid **only if every emitted formula lies in `U(φ)`** — which requires an
**a-priori world bound** `W(φ)` proved as a loop invariant. This world bound is the single
research-hard obligation; everything else is a faithful port of two existing green proofs.

---

## 1. Verified Reference-Signature Table (Deliverable 1)

All signatures quoted from source read this session. Line numbers verified.

| Reference declaration | File:Line | Exact signature (quoted / paraphrased from source) | Modal obligation it templates |
|---|---|---|---|
| `classicalExpandBranches_hintikka` | `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924` | `(fuel : Nat) : ∀ (branches) (expandedSets), expandedSets.length = branches.length → classicalExpMeasure branches expandedSets ≤ fuel → (Hintikka-inv on expanded) → ∀ b, classicalExpandBranches … fuel = .openBranch b → classicalHintikkaSet b` | **`modalExpandBranches_hintikka`** — top-level target. Note it takes `measure ≤ fuel` as a HYPOTHESIS; the numeric `modalFuel` only has to satisfy that at entry. |
| `classicalStepBranch_none_saturated` | `.../Classical/Completeness.lean:694` | `{b e} (hstep : classicalStepBranch b e = none) (sf) (hsfb : sf ∈ b) : sf ∈ e ∨ classicalApplyOne sf = .notApplicable` | **`modalStepBranch_none_saturated`** — proves saturation of the returned open leaf. Modal version must also thread `acc` and split the `sf ∈ e` disjunct against the modal `modalApplyOne sf b acc`. |
| `classicalStepBranch_hintikka_inv` | `.../Classical/Completeness.lean:722` | `(b e newBs newExp) (hstep : classicalStepBranch b e = some (newBs,newExp)) (hInv_b : ∀ sf∈e, match classicalApplyOne sf …) : ∀ b'∈newBs, ∀ sf∈newExp, match classicalApplyOne sf …` | Invariant-maintenance lemma carried through the `processNext` induction that yields `modalHintikkaSet` at the saturated leaf. Modal analogue must handle the **`.persistent` clause where `newExp = e` (unchanged)** — see §3.1. |
| `classicalExpMeasure_step_lt` | `.../Classical/Completeness.lean:834` | `… (hstep : classicalStepBranch bh e = some (newBs,newExp)) : classicalExpMeasure (done++newBs++bt) (doneExp++newBs.map(fun _=>newExp)++es) + 1 ≤ classicalExpMeasure (done++bh::bt) (doneExp++e::es)` | **`modalExpMeasure_step_lt`** — the strict-decrease engine. Rename `classicalBranchComplexity → R`; reuse `pow3_add_one_le`/`pow3_two_add_one_le` verbatim. |
| `pow3_add_one_le` / `pow3_two_add_one_le` | `.../Classical/Completeness.lean:684` / `:674` | `{a0 C} (hC:1≤C)(h0:a0≤C-1) : 3^a0+1 ≤ 3^C` / `{a0 a1 C}(hC)(h0)(h1) : 3^a0+3^a1+1 ≤ 3^C` | Generic Nat lemmas (label-agnostic). **Directly reusable** — currently `private`; hoist or re-prove (1-liners). Base-3 damping of ≤2-way prop branching. |
| `classicalExpMeasure_split` / `_append` / `_const_exp` | `:641` / `:656` / `:666` | additivity of `Σ 3^C` over `zip`/append/replicate | **`modalExpMeasure_split/_append/_const_exp`** — identical structure with `R`; needed to expand both sides of the step inequality. |
| `classicalBranchComplexity_drop` | `:509` | strict drop of the exponent when `sf` moves into `e` | Template for the **linear/branching `R`-drop** (sf added to `e` ⇒ `|U\e|` drops by 1). Modal version is *simpler* (counting, not complexity). |
| `modalExpandBranches_closed_unsat` | `Cslib/Logics/Modal/Tableau/Soundness.lean:165` | `(fuel : Nat) : ∀ branches expandedSets accs, lengths → Forall₂ accFreshInv branches accs → modalExpandBranches … fuel = .closed → Forall₂ (¬branchSatisfiable) branches accs` | **The acc-threading skeleton.** Its `succ`-case `key` suffices establishes the exact `processNext fuel' pending pendingExp pendingAccs done doneExp doneAccs` inner induction with per-branch `List.Forall₂` accs (`:190-262`). `modalExpandBranches_hintikka` reuses this shape 1:1, swapping the conclusion `¬branchSatisfiable` for `measure-bound ⇒ Hintikka`. |
| `modalStepBranch_preserves_accFreshInv` | `Soundness.lean:111` | `(b e acc newBs newExps newAcc)(hstep)(hInv:accFreshInv b acc) : ∀ b'∈newBs, accFreshInv b' newAcc` | Precedent for a **per-step invariant that survives child branching** — the pattern the world-bound invariant (§6) must follow. |
| `modalApplyOne_fresh` | `Soundness.lean:87` | `(sf b acc) : (modalApplyOne sf b acc).snd = acc ∨ ∃ wsf rest, .fst = .linear (wsf::rest) ∧ .snd = acc.addEdge sf.label wsf.label` | Proves fresh-edge creation is confined to `.linear` results with head witness at the fresh world — the fact that **only linear rules create worlds** (single-child), key to the branching argument in §2. |
| `forall₂_of_zip_mem`, `forall₂_replicate_right`, `forall₂_append_aux`, `forall₂_drop_aux`, `forall₂_take_aux` | `Cslib/Logics/Modal/Tableau/LoopInduction.lean:44,66,87,96,104` | generic `List.Forall₂` worklist helpers (public, de-privatised) | Already hoisted (task-299 prior dispatch). Reused verbatim to thread the per-branch `accs` list through the `modalExpandBranches_hintikka` inner induction. |
| `modalTruthLemma` | `Cslib/Logics/Modal/Tableau/Completeness.lean:383` | `(b acc)(hH : modalHintikkaSet b acc) : ∀ φ w, (⟨.pos,φ,w⟩∈b → Satisfies (extractModel b acc) w φ) ∧ (⟨.neg,φ,w⟩∈b → ¬ Satisfies …)` | **GREEN, consumed unchanged.** Downstream of Hintikka; no rework. |
| `modalOpenBranch_countermodel` | `Completeness.lean:560` | `(b acc φ)(hH : modalHintikkaSet b acc)(hF : ⟨.neg,φ,0⟩∈b) : ¬ Satisfies (extractModel b acc) 0 φ` | **GREEN.** `modalTableau_complete` = contrapositive wrapper: open ⇒ Hintikka (this task) ⇒ countermodel (here). |

**Modal-side objects being defined (do NOT exist yet — confirmed absent by grep):**
`modalStepBranch_none_saturated`, `modalExpandBranches_hintikka`, `modalTableau_complete`,
`modalTableau_decides`, `Decidable (kValid φ)` instance — referenced only in the `Completeness.lean`
header docstring (`:20-23`), not proven. Also **no** existing `modalDepth`, `subformula`, or closure
definition anywhere under `Cslib/Logics/Modal/` (Reuse Check exhausted — see §7).

---

## 2. The Measure Decision — full justification

### 2.1 Why the classical complexity measure fails (root cause, verified in code)

The classical measure `classicalBranchComplexity b e = Σ_{sf∈b, sf∉e} sf.formula.complexity`
(`:473`) strictly decreases because **every** classical rule — including `.persistent` — is applied
**single-shot**: `classicalStepBranch` (`Expansion.lean:99-100`) does
`| .persistent newForms => some ([extendMany b newForms], expanded ++ [sf])`, i.e. **it appends `sf`
to `expanded`**. So the source's complexity term always leaves the sum.

The modal step is structurally different at exactly one line
(`Saturation.lean:116-117`):

```lean
| .persistent newForms =>
  some ([newForms ++ b], [expanded])     -- expanded UNCHANGED: sf re-fires
```

The modal `.persistent` (used by `boxPos` `Rules.lean:83-88` and `diamondNeg` `Rules.lean:142-151`)
**leaves `expanded` unchanged** — this is mandatory for K-soundness (a `T(□ψ)@w` must re-propagate to
each new successor of `w` as diamonds mint them). Consequence:

- A complexity measure over `b\e` **does not decrease** on a persistent step (source stays in `b\e`),
  and in fact **increases** (it adds the positive complexities of `newForms`). The classical template
  is therefore *provably* inapplicable to the modal loop as-is.

### 2.2 Why the counting measure `R = |U\b| + |U\e|` succeeds on every rule kind

Verified emission facts (from `Rules.lean` + `Saturation.lean`):

| Rule | `Rules.lean` | Result kind | Child count | `expanded` on step | Emitted formulas ⊆ | Fresh world? |
|---|---|---|---|---|---|---|
| prop α (`modalAndOf?`/`modalNegOf?`/`modalImpOf?` linear) | via `tryAllPropRules` (`:75`) | `.linear` | 1 | `e++[sf]` | subformulas @ `sf.label` | no |
| prop β (`modalOrOf?` etc.) | via `tryAllPropRules` | `.branching` | **2** (`classicalApplyOne_branching_length :818`) | `e++[sf]` (per child) | subformulas @ `sf.label` | no |
| `boxPos` `T(□φ)@w` | `:83-88` | `.persistent` | 1 | **`e` (unchanged)** | `T(φ)@w'`, `w'∈successorsOf w` (existing), all `∉b` | no |
| `diamondPos` `T(◇φ)@w` | `:91-114` | `.linear` | 1 | `e++[sf]` | `T(φ)@w'`(fresh) `::` boxProps `++` diaNegProps @ fresh `w'` | **yes** (`modalNextWorld`) |
| `boxNeg` `F(□φ)@w` | `:117-139` | `.linear` | 1 | `e++[sf]` | `F(φ)@w'`(fresh) `::` boxProps `++` diaNegProps @ fresh `w'` | **yes** |
| `diamondNeg` `F(◇φ)@w` | `:142-151` | `.persistent` | 1 | **`e` (unchanged)** | `F(φ)@w'`, `w'∈successorsOf w` (existing), all `∉b` | no |

Key structural facts, each verified:

1. **Only `.linear` rules mint worlds** (`modalApplyOne_fresh`, `Soundness.lean:87-104`), and they are
   **single-child**. The only **2-child** rule is prop-β, which is **world-preserving** (same
   `sf.label`). Hence the exponential base-3 damping only ever has to absorb 2-way *world-preserving*
   splits — exactly the classical situation.
2. **Persistent rules add ≥1 genuinely-new formula to `b`**: `boxPropagation` (`Branch.lean:194-199`)
   and the `diamondNeg` `filterMap` (`Rules.lean:144-147`) filter out formulas already on `b`
   (`if b.any (· == sf) then none`), and `modalApplyOne` returns `.notApplicable` when the result is
   empty (`:85-86`, `:148-149`). So a `.persistent` `some` step strictly grows `set(b)`.

**`R`-drop, by rule kind** (letting `set(b') ⊇ set(b)` always, since formulas are only ever prepended):

- **prop α / prop β / diamondPos / boxNeg (all add `sf` to `e`)**: `sf ∈ b ⊆ U` and `sf ∉ e` (guard),
  so `e' = e++[sf]` gives `|U\e'| = |U\e| − 1`; and `|U\b'| ≤ |U\b|`. Hence `R(child) ≤ R − 1`.
  For **prop β** BOTH children share `e' = e++[sf]`, so both have `R ≤ R−1` → `pow3_two_add_one_le`.
- **boxPos / diamondNeg (persistent, `e` unchanged)**: `newForms ⊆ U`, `newForms ∩ set(b) = ∅`,
  `newForms ≠ []`, so `set(b') ⊋ set(b)` and `|U\b'| ≤ |U\b| − 1`; `e' = e` so `|U\e'| = |U\e|`.
  Hence `R(child) ≤ R − 1` → `pow3_add_one_le`.

Therefore `R` strictly drops by ≥1 on **every** `some` step, and `3^R` summed over the worklist
satisfies `newmeasure + 1 ≤ oldmeasure` — the exact shape of `classicalExpMeasure_step_lt` (`:834`).
**Every hypothesis of `pow3_add_one_le`/`pow3_two_add_one_le` is met** (`1 ≤ R` because `R` drops to a
value ≥0 and the parent had a droppable element, i.e. `sf ∈ b\e` or a nonempty `newForms`).

**Load-bearing caveat (→ §6):** every "⊆ U" above is exactly the world-bounded closure invariant.
If a persistent/existential emission lands at a world label **outside** `U`'s world range, its formulas
are **not** counted in `|U\b|`, and the `R`-drop fails. The measure's correctness is therefore
**equivalent to** the a-priori world bound holding as an invariant.

### 2.3 Entry-point sufficiency

`R(b,e) ≤ 2|U|` always (each summand ≤ |U|). At entry `modalExpMeasure [[F(φ)@0]] [[]] = 3^{R(...)}
≤ 3^{2|U|} = modalFuel φ`. Monotonicity `Nat.pow_le_pow_right` (already used at `:677`) closes it.
No separate "revise fuel if gap" branch is needed: the fuel is *defined* as `3^{2|U|}`, so the entry
bound is definitional-plus-monotonicity.

---

## 3. Lean-Level Formalization Sketch (Deliverable 3)

New file recommended: `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (imports `Saturation`, `LoopInduction`),
then extend `Completeness.lean`. Keeps the measure infra out of the green truth-lemma file.

### 3.1 The universe `U(φ)` and the world bound

```lean
/-- Structural subformula list of a modal proposition (Lukasiewicz constructors imp/box). -/
def modalSubfmls : Proposition Atom → List (Proposition Atom)
  | .atom p      => [.atom p]
  | .bot         => [.bot]
  | .imp a b     => (.imp a b) :: modalSubfmls a ++ modalSubfmls b
  | .box a       => (.box a)  :: modalSubfmls a
-- |modalSubfmls φ| ≤ 2 * modalComplexity φ + 1  (each node contributes ≤1; ≤ tree size)

/-- Modal (box-nesting) depth; ≤ modalComplexity. -/
def modalDepth : Proposition Atom → Nat
  | .atom _ | .bot => 0
  | .imp a b => max (modalDepth a) (modalDepth b)
  | .box a   => 1 + modalDepth a

/-- A-priori world-count bound. Sf := #subfmls, d := modalDepth. -/
def modalWorldBound (φ : Proposition Atom) : Nat :=
  (2 * modalComplexity φ + 1) ^ (modalComplexity φ + 1)   -- Sf^(d+1), using d ≤ complexity

/-- Fixed finite signed-formula universe: both signs × subformulas × world labels [0 .. W]. -/
def modalUniverse (φ : Proposition Atom) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  (List.range (modalWorldBound φ + 1)).flatMap (fun w =>
    (modalSubfmls φ).flatMap (fun ψ => [⟨.pos, ψ, w⟩, ⟨.neg, ψ, w⟩]))
-- (modalUniverse φ).length = (W+1) * |subfmls| * 2  ≤  (W+1) * (2n+1) * 2
```

`BEq`/`DecidableEq (SignedFormula (Proposition Atom) WorldIndex)` already used throughout
(`b.any (· == sf)`, `expanded.any (· == sf)`), so `List.countP`/`filter`/`contains` on `U` are available.

### 3.2 The measure

```lean
def modalWork (U b e : List (SignedFormula (Proposition Atom) WorldIndex)) : Nat :=
  U.countP (fun sf => !(b.any (· == sf))) + U.countP (fun sf => !(e.any (· == sf)))   -- |U\b| + |U\e|

def modalExpMeasure (U : …) (branches expandedSets : List (List …)) : Nat :=
  ((branches.zip expandedSets).map (fun p => 3 ^ modalWork U p.1 p.2)).sum

def modalFuel (φ : Proposition Atom) : Nat := 3 ^ (2 * (modalUniverse φ).length)
```

Primitives confirmed available (loogle): `List.Sublist.countP_le` (monotone drop),
`List.Sublist.length_le`, `Nat.pow_le_pow_right`, `Nat.one_le_pow`, `List.monotone_filter_right`,
`List.filter_sublist` — the last three already used in the classical file (`:502,581,677`).

### 3.3 Subformula-closure lemma (per-rule dispatch — the emissions enumerated)

```lean
/-- Every formula emitted by any rule at a branch already inside U stays inside U. -/
lemma modalApplyOne_outputs_subset
    (φ0 : Proposition Atom)          -- the root formula fixing U := modalUniverse φ0
    (sf b acc) (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (hW : modalMaxWorld b < modalWorldBound φ0) :        -- world-bound hypothesis (§6)
    (∀ x ∈ (emitted formulas of modalApplyOne sf b acc), x ∈ modalUniverse φ0)
```

Per-case obligations (dispatch mirrors `Rules.lean` structure):
- **prop rules**: output propositions are structural subformulas of `sf.formula` (⊆ `modalSubfmls φ0`
  by `hb sf`), all at world `sf.label` (already a `b`-label ⇒ ≤ `modalMaxWorld b` < W). Reuse the
  shape of `classicalApplyOne_output_complexity` (`:609`) but for membership, not complexity.
- **boxPos** (`:83-88`): emits `T(ψ)@w'`, `ψ` from the SAME `T(□ψ)` node (so `.box ψ`∈subfmls ⇒ `ψ`∈subfmls),
  `w'∈successorsOf w` ⊆ existing labels ≤ maxWorld < W. ⇒ ∈ U.
- **diamondPos** (`:91-114`) emits three groups:
  - `witness = ⟨.pos, φ, w'⟩`: `φ` is the diamond body (subformula of `◇φ = (□(φ→⊥))→⊥`), `w' = modalNextWorld b = maxWorld+1 ≤ W`.
  - `boxProps` from `boxPositivesOf b` (`Branch.lean:180-187`): each `ψ` comes from a `T(□ψ)@w`∈b ⇒ `ψ`∈subfmls; at `w'`.
  - `diaNegProps`: each `ψ` from an `F(◇ψ)@w`∈b ⇒ `ψ`∈subfmls; at `w'`.
  All at fresh `w' = maxWorld+1`; **needs `maxWorld+1 ≤ W`** — this is the exact point where the world
  bound is consumed.
- **boxNeg** (`:117-139`): identical to diamondPos with `witness = ⟨.neg, φ, w'⟩`.
- **diamondNeg** (`:142-151`): emits `F(φ)@w'`, `w'∈successorsOf w` (existing ≤ maxWorld < W), `φ`∈subfmls.

### 3.4 Output-disjointness (freshness on branch)

`boxPropagation` (`Branch.lean:197-199`) and the `boxProps`/`diaNegProps` filterMaps
(`Rules.lean:100-101, 111-112, 126-127, 135-136`) all guard `if b.any (· == sf') then none`, so emitted
formulas of persistent rules are `∉ set(b)`. Formalize:

```lean
lemma modalPersistent_outputs_fresh (hstep : modalStepBranch b e acc = some (newBs,newExps,newAcc))
    (hpers : the fired rule was .persistent) : ∀ b'∈newBs, ∀ sf'∈(b'.diff b), sf' ∉ b
-- ⇒ set(b') ⊋ set(b) ⇒ |U\b'| < |U\b|  (with §3.3 giving newForms ⊆ U)
```

### 3.5 World-count bound (the crux invariant) — §6

```lean
lemma modalStepBranch_maxWorld_lt
    (φ0) (hb : ∀ x∈b, x∈modalUniverse φ0) (hW : modalMaxWorld b < modalWorldBound φ0)
    (hstep : modalStepBranch b e acc = some (newBs,newExps,newAcc)) :
    ∀ b'∈newBs, modalMaxWorld b' < modalWorldBound φ0
```

**This is NOT a one-step monotonicity** (`maxWorld+1 < W` does not follow from `maxWorld < W`). It
requires the depth-stratification argument (§6): worlds form a forest of depth ≤ `modalDepth φ0` and
branching ≤ `Sf(φ0)`, so `#worlds ≤ Sf^(d+1) = W`. This is the ~200-400-line research obligation.

### 3.6 Strict-decrease + top lemma (ports)

`modalExpMeasure_step_lt` ← `classicalExpMeasure_step_lt (:834)` with `R` for `classicalBranchComplexity`,
using §2.2 case analysis + `pow3_add_one_le`/`pow3_two_add_one_le`.
`modalExpandBranches_hintikka` ← fusion of `modalExpandBranches_closed_unsat` (`Soundness.lean:165`,
acc-threading `processNext` + `Forall₂` accs) and `classicalExpandBranches_hintikka` (`:924`,
measure-bound ⇒ Hintikka + `classicalStepBranch_hintikka_inv`). The `processNext` inner induction
simultaneously carries: (i) length invariants, (ii) `Forall₂ accFreshInv`, (iii) the world-bound
invariant §3.5, (iv) the measure bound, (v) the Hintikka expanded-set invariant.
`modalStepBranch_none_saturated` ← `classicalStepBranch_none_saturated (:694)`, threaded with `acc`,
feeding the saturated-leaf `.openBranch b a` case (`Saturation.lean:167`) into `modalHintikkaSet`
(all three conjuncts, `Saturation.lean:218-234`).

---

## 4. Dependency-Ordered Obligation List (Deliverable 4 — planner phase-cut guide)

Sizes are estimates for a hard planner to cut into ~100-500-line phases. **Phase 0 (world bound) is the
gate**; everything after it is a mechanical port of green proofs.

- **P0 — Definitions (new file `FmpMeasure.lean`)** [~120 lines]
  `modalSubfmls`, `modalDepth`, `modalWorldBound`, `modalUniverse`, `modalWork`, `modalExpMeasure`,
  redefine `modalFuel := 3^(2*|modalUniverse φ|)`; `|modalUniverse|` length lemma; `modalSubfmls`
  size bound `≤ 2n+1`; `modalDepth ≤ modalComplexity`. Depends on: nothing new. **Verify soundness still
  green** after `modalFuel` value change (fuel-agnostic ⇒ should be immediate; `Soundness.lean` never
  reads the value).
- **P1 — Subformula-closure lemma** [~250-400 lines] `modalApplyOne_outputs_subset` (§3.3), full
  per-rule dispatch, **conditioned on** the world-bound hypothesis `maxWorld b < W`. Depends: P0.
- **P2 — World-count bound (CRUX)** [~250-450 lines] depth-stratification invariant ⇒
  `modalStepBranch_maxWorld_lt` (§3.5) and the initial `maxWorld [F(φ)@0] = 0 < W`. Depends: P0, P1
  (closure gives "emitted worlds are fresh/existing", stratification gives the count cap). **Highest
  risk; isolate; adversarial audit before proceeding (see §6).**
- **P3 — Output-freshness + `R`-drop per rule** [~200-350 lines] `modalPersistent_outputs_fresh` (§3.4);
  `modalWork_drop_linear`, `modalWork_drop_persistent` (`R(child) ≤ R−1`); `modalExpMeasure_step_lt`
  (port of `:834`); hoist/re-prove `pow3_add_one_le`,`pow3_two_add_one_le`,`modalExpMeasure_split/_append/_const_exp`.
  Depends: P1, P2.
- **P4 — Saturation characterisation** [~120-200 lines] `modalStepBranch_none_saturated` (port `:694`)
  + `modalStepBranch_hintikka_inv` (port `:722`, handling the `.persistent`⇒`newExp=e` case). Independent
  of P2/P3 (can be built in parallel with P1/P2). Depends: P0.
- **P5 — Top loop lemma** [~300-500 lines] `modalExpandBranches_hintikka` (§3.6 fusion). Depends: P3, P4.
- **P6 — Public theorems + Decidable** [~120-200 lines] `modalTableau_complete` (contrapositive via
  `modalOpenBranch_countermodel`, green); `modalTableau_decides` (`.closed ↔ kValid`, combining
  `modalTableau_sound` + P5); `instance : Decidable (kValid φ)` from the `.closed`/`.openBranch`
  dichotomy (no `Fintype Atom`). `#print axioms` on each; whole-library `lake build`; CI pipeline.
  Depends: P5.

Parallelizable (H7 territory): P4 is disjoint from P1-P3 (new lemmas in the same new file — assign
distinct declaration blocks). P0 must land first (shared defs). P2 must be gated/serial.

---

## 5. Reconciliation with the Task-299 Plan Phase-6 Addendum (Deliverable 5)

Read `specs/299_modal_k_tableau/plans/05_modal-k-tableau-plan.md` "DECISIVE FINDING" (`:440-461`) and
"Precise residual obligation" (`:462-527`). Findings:

- **CONFIRMED (no correction)**: the polynomial `modalFuel = (4n+4)(n+2)+2` (`Saturation.lean:89`) is
  provably insufficient; K's exponential minimal-model lower bound forces `fuel = 0` with an unsaturated
  open branch. Option A (raise fuel + FMP measure) is in scope; option B (world-subset blocking = task
  441) is out of scope. All accurate against current source.
- **CONFIRMED**: the plan's proposed exponent `R = (|U|−|branch∩U|)+(|U|−|exp∩U|)` (`:472`) is the
  correct measure. This report validates it and supplies the missing piece the plan flagged as unknown:
  "labels are `modalNextWorld`-minted and currently unbounded a priori, so `U` cannot be a fixed finite
  set without first proving a world-count bound" (`:467-469`). §6 supplies that bound (`W = Sf^(d+1)`,
  via depth stratification) and rates it the top risk.
- **CORRECTION 1 (measure basis)**: the plan's earlier prose (`:417-421`) and the addendum both lean on
  the phrase "`3^complexity` measure … modal analogue must add to absorb world-creation," implying a
  *complexity* exponent augmented for worlds. This is **imprecise**: the modal exponent must be a
  **pure counting** measure `|U\b| + |U\e|`, NOT complexity-based, because the persistent modal rules
  (`Saturation.lean:116-117`, `expanded` unchanged) make any complexity sum over `b\e` **non-decreasing**
  (§2.1). The plan's `R` formula (`:472`) is right; its surrounding "3^complexity analogue" narrative
  (`:417`, `:473`) should be read as "3^(counting-R)", not "3^complexity". Deliverable-5 correction.
- **CORRECTION 2 (`modalFuel` "should suffice; adjust only if gap")**: plan task-line `:519-520`
  ("`modalFuel φ` should suffice; adjust ONLY if the invariant exposes a gap") is **superseded** — the
  gap is real and the fuel MUST be redefined to `3^(2|U|)` (double/triple-exponential). The addendum
  `:521-525` already records this deviation; this report finalizes the concrete replacement value (§Executive).
- **CONFIRMED (infra reuse)**: `forall₂_*` hoist into `LoopInduction.lean` is DONE (`:507-509`);
  `accFreshInv`/`modalExpandBranches_closed_unsat` acc-threading is the reuse target (`:510-512`);
  `classicalStepBranch_none_saturated`/`_hintikka_inv` are Unit-label reference patterns (`:513-518`).
  All verified present and correctly cited.
- **CONFIRMED (statement)**: the plan's intended `modalExpandBranches_hintikka` signature (`:497-504`)
  matches the classical template contract; the modal version additionally threads `accs`/`acc`.

---

## 6. Adversarial Self-Verification (H4)

Each load-bearing claim challenged; confidence and residual risk recorded.

**C1 — "The counting measure `R = |U\b|+|U\e|` strictly decreases on every rule."**
Challenge: does it really drop on prop-β (2 children) without doubling the worklist term?
Verification: both β-children share `e' = e++[sf]` ⇒ both have `R ≤ R−1`; the `3^R` sum gives
`3^{R-1}+3^{R-1}+1 ≤ 3^R` (`pow3_two_add_one_le`, `:674`, hypotheses met since `1 ≤ R` from the
consumed `sf∈b\e`). β is world-preserving (`sf.label` unchanged), so `|U\b'|≤|U\b|` — no world blow-up.
**Confidence: HIGH.** Grounded in code + the exact classical lemma that already discharges the identical
inequality shape.

**C2 — "Only linear rules create worlds, so branching never multiplies the world dimension."**
Challenge: could a persistent rule ever branch or mint a world? Verification: `modalApplyOne`
(`Rules.lean:68-153`): `.branching` arises ONLY from `tryAllPropRules` (prop, world-preserving);
`boxPos`/`diamondNeg` are `.persistent` to **existing** `successorsOf w` (no mint); `diamondPos`/`boxNeg`
are `.linear` single-child and are the ONLY minters (`modalApplyOne_fresh`, `Soundness.lean:87`).
**Confidence: HIGH.**

**C3 (TOP RISK) — "The a-priori world bound `W = Sf^(d+1)` is provable and NOT circular with the FMP
we are proving."**
Challenge A (circularity): does bounding `#worlds` secretly assume the finite-model property (the very
termination we want)? Answer: **No, but the distinction must be stated carefully.** The FMP as a
*semantic* statement (every K-satisfiable formula has a small Kripke model) is NOT used. What we prove
is a *syntactic combinatorial* bound on the algorithm's world labels: worlds form a forest whose edges
(recorded in `acc`, `Branch.lean:64`) go from a world seeded at modal-depth-budget `k` to a child seeded
only with **strict subformulas** (witness = immediate subformula; `boxProps`/`diaNegProps` = bodies of
`□`/`◇` formulas present at the parent). So child worlds carry formulas of strictly smaller modal depth
⇒ forest depth ≤ `modalDepth φ0`; and at each world the number of distinct existential (`diamondPos`/
`boxNeg`) source formulas is ≤ `|modalSubfmls φ0|` ⇒ branching ≤ `Sf`. Hence `#worlds ≤ Σ_{i≤d} Sf^i ≤
Sf^(d+1)`. This argument is a fixed-φ syntactic induction (on modal depth), **independent of the fuel
run** — it does not presuppose termination.
Challenge B (formalization feasibility): the danger is that the depth-stratification invariant is heavy
to state against a **flat** `maxWorld+1` naming scheme with `acc.edges` as an unordered list. Verified
mitigations: (i) `modalNextWorld_gt`/`label_le_modalMaxWorld` (`Branch.lean:104,135`) and
`modalMaxWorld_le_append`/`modalNextWorld_le_append` (`:146,169`) already give the monotonicity plumbing;
(ii) `accFreshInv` (`Soundness.lean`) already encodes "edge endpoints < next fresh world," the precise
hook to attach a depth field; (iii) the invariant can be carried in the SAME `processNext` induction
that already carries `Forall₂ accFreshInv`. **Confidence: MEDIUM.** This is the single obligation that
could turn into an implementation dead-end. **Residual risk (flagged):** if the depth-stratification
invariant proves intractable against the flat naming, the fallback is to strengthen the tracked invariant
to a per-world *rank* map (label ↦ remaining modal-depth budget) threaded alongside `acc` **as proof-only
data in the invariant** (NOT an algorithm change — it lives in the `∀`-invariant of the induction, not in
`modalStepBranch`). This keeps scope compliance (no datatype/rule change) but adds proof bulk. Planner
should allocate P2 generously and gate P3-P5 behind it; if P2 stalls after one genuine attempt, mark P2
[BLOCKED] and escalate rather than weaken the bound.

**C4 — "`modalFuel := 3^(2|U|)` is actually ≥ the entry measure."**
Challenge: off-by-one or wrong direction? Verification: `R(b,e) ≤ |U| + |U| = 2|U|` because each
`countP ≤ U.length` (`List.countP_le_length`); `modalExpMeasure [b][e] = 3^{R} ≤ 3^{2|U|}` by
`Nat.pow_le_pow_right (by omega) (by …)` — the exact monotonicity used at `:677`. **Confidence: HIGH.**

**C5 — "The `R`-drop needs `1 ≤ R` (the `hC` hypothesis of the pow3 lemmas)."**
Challenge: could `R = 0` at a step where a rule still fires (making `pow3_*` inapplicable)? Verification:
a `some` step fires ⇒ either `sf∈b\e` (linear/branching: `|U\e|≥1` since `sf∈U\e`) or nonempty fresh
`newForms⊆U\b` (persistent: `|U\b|≥1`). Either way `R ≥ 1`. Mirrors `classicalBranchComplexity_drop`
giving `1 ≤ C` at `:876`. **Confidence: HIGH**, contingent on C3 (sf,newForms ∈ U).

**C6 — "Soundness stays green after the `modalFuel` value change."**
Verification: `modalExpandBranches_closed_unsat` (`Soundness.lean:165`) and `modalTableau_sound` quantify
over `fuel : Nat` and never inspect `modalFuel`'s value; `modalTableau` (`Saturation.lean:189-192`) only
passes it. Changing the definitional body of `modalFuel` cannot break any proof that does not unfold it.
**Confidence: HIGH.** (Cheap guard: P0 ends with `lake build Cslib.Logics.Modal.Tableau.Soundness`.)

**Uncertain / to-confirm during implementation (not blockers):**
- Exact constant in `|modalSubfmls φ| ≤ 2n+1` (may be `n+1` for distinct subterms; the over-count only
  inflates fuel harmlessly). LOW risk.
- Whether `modalDepth ≤ modalComplexity` needs `max`-vs-`+` care in the `imp` case (`max` chosen above;
  trivially ≤ complexity). LOW risk.
- `Decidable (kValid φ)`: the dichotomy `modalTableau φ = .closed ∨ ∃ b acc, = .openBranch b acc` plus
  `sound` + `complete` gives decidability without `Fintype Atom`; needs the `.openBranch ⇒ ¬kValid`
  direction from P5. LOW-MEDIUM risk (standard once P5 lands).

**No forbidden outputs**: this report yields concrete Lean definitions, a numeric `modalFuel`, per-rule
obligations, and a phase-cut list — not an analysis-only verdict. No `sorry`/axiom is recommended; the
one hard obligation (P2) is isolated with an escalation path, per zero-debt policy.

---

## 7. Reuse Check Protocol Results (CSLib-specific H3)

1. **Foundations first** (`grep Cslib/Logics/Modal/`): no existing `modalDepth`/`subformula`/closure
   definition — must be created (P0). `SignedFormula`, `RuleResult`, `ClosureCondition`, `tryAllPropRules`
   reused from `Foundations.Logic.Tableau.*` (imported via `Defs.lean:11`, `Closure.lean:11`).
2. **Typeclass hierarchy**: `BEq`/`DecidableEq`/`Hashable (Proposition Atom)` already provided
   (`Defs.lean:101`, foundation instances) — enables `List.countP`/`filter` on `U`. No new typeclass.
3. **Notation**: none introduced; measure is plain `def`s.
4. **Mathlib instantiable**: `List.countP`, `List.Sublist.countP_le`, `List.Sublist.length_le`,
   `Nat.pow_le_pow_right`, `Nat.one_le_pow`, `List.monotone_filter_right`, `List.filter_sublist`,
   `List.countP_le_length` — all present (loogle + already used in the classical file).
5. **Logics/Languages namespace**: the classical template (`Cslib.Logic.Tableau` propositional layer)
   supplies the entire proof skeleton to port; the modal green files supply the acc-threading. Maximal reuse.

**Bibliography note (BibKey)**: the modal tableau files cite `[Fitting1983]` and `[Smullyan1968]`
(e.g. `Saturation.lean:57-58`, `Rules.lean:42-43`). A `references.bib` was **not located** at the repo
root in this session (no file matched); the citation keys `Fitting1983`/`Smullyan1968` are used
consistently in-source and should be verified against the library's bibliography during PR (flag: confirm
these BibKeys resolve, or add them). The FMP world-bound argument (depth stratification, `Sf^(d+1)`) is
standard finite-model-property material for K (Fitting1983, Ch. 2); no new external source is required —
the task is transcription of an existing algorithm's termination, not a new theorem.

---

## Source-to-Implementation Mapping (Tier 1)

| Source claim | BibKey | Lean target | Translation notes |
|---|---|---|---|
| K has the finite model property; a satisfiable K-formula has a model of size ≤ subformula-tree bound | Fitting1983 (Ch.2) | `modalWorldBound`, `modalStepBranch_maxWorld_lt` (P2) | Formalized *syntactically* as a world-label bound `Sf^(d+1)` on the algorithm, via depth stratification — NOT via a semantic model-size theorem (avoids circularity, §6/C3). |
| Signed tableau saturation / Hintikka set yields a countermodel | Smullyan1968 (Ch.V), Fitting1983 | `modalHintikkaSet` (`Saturation.lean:218`, exists), `modalOpenBranch_countermodel` (`Completeness.lean:560`, GREEN) | Consumed unchanged; this task only proves the loop *reaches* a Hintikka set. |
| α/β rule complexity decrease drives tableau termination | Smullyan1968 | replaced by counting measure `R` (§2) | Modal persistent (re-firing) rules break the α/β complexity-decrease; counting measure over finite `U` restores strict decrease. |

---

**Report path**: `specs/442_modal_tableau_fmp_fuel_measure/reports/01_fmp-fuel-measure-research.md`
