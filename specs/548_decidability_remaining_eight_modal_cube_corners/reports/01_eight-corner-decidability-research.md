# Decidability for the Remaining Modal-Cube Corners — Research

**Task**: 548 | **Type**: cslib | **HEAD**: `895179d1`
**Session**: `sess_1786228817_675b2c`
**Verification basis**: every line anchor below was re-read at HEAD. Anchors quoted from the task
description that did not verify are corrected in §1.2. No Lean file was created or edited.

---

## 0. Executive Summary

Six findings, in order of decision weight.

1. **The matrix is 7/15, not 6/15. S4 landed.** `instDecidableS4Valid`
   (`FrameCompleteness.lean:8281`), `s4Valid_decides` (`:8269`),
   `modalTableauS4KeyedOrdered_complete` (`:8221`) and `_sound` (`:8176`) all exist and are
   green. Task 511 closed them (`b2488f0e`, "task 511 phase 5: S4 decidability capstone"). The
   task description's "S4 is in flight (tasks 506/511/535 own the loop-checking termination)" is
   **stale**. So is its dependency gate — 511 is `[COMPLETED]`, 535 is archived-completed, 597 is
   `[COMPLETED]`. The remaining ragged corners are **8**, exactly as stated, but the transitive
   template they depend on now exists.

2. **The task description's premise "extend the generic tableau driver to the remaining corners"
   was formally evaluated and rejected.** Task 597's decision report
   (`specs/597_modal_tableau_driver_abstraction_decision/reports/01_driver-abstraction-decision.md`,
   747 lines) concluded: *keep the three per-regime drivers as separate bespoke implementations;
   the per-regime split is the correct steady state.* The abstraction already exists at two
   independent axes (`AuxStepPreserved`/`ModalLoopInvHintikka`, `CompletenessLoop.lean:263-420`;
   `RuleApplySt`, `Saturation.lean:493-758`), and the one further generalisation anyone measured
   came out at **+80 lines across 40 re-verification sites** (task 564). This report does not
   re-litigate that decision; it works within it.

3. **Two of 597's three gates are cleared; two are still open, and neither has an owning task.**
   Gate A (S4 completion) — **CLEARED** by 511. Gate B (the §7.2 universal-cluster rule-combinator
   prototype on the `Kb5''`-from-`Five` pair, which gates the Tier-B corners) — **NOT DONE, no
   task exists**. Gate C (retire the unordered S4 stepper stack before templating K4/D4 on it) —
   **NOT DONE**; `modalTableauS4Keyed` is still live at `LoopChecking.lean:156` with 152
   in-library references to the unordered stepper family, and `LoopChecking.lean:192` still
   earmarks the retirement as a future destructive phase. Task 506 (`[PARTIAL]`) is the nearest
   owner but does not name it.

4. **New finding, not in 597: D's seriality rule does not fit `RuleApplicationSpec` as stated.**
   The spec's field `boxPosNotExpanding` (F9, `GenericDriver.lean:239-243`) requires that a
   `T(□ψ)@w`-shaped input yield `.notApplicable` or `.persistent` — **never `.linear`**, i.e.
   never a mint. But D's seriality rule must mint a successor precisely at a dead-end world
   carrying `T(□ψ)`, and the only two mint-licensed shapes in the bundle (F11'/F12',
   `:259-277`) are box-negative and diamond-positive. §5.1 works through why the three
   mint-avoiding alternatives (self-loop-at-dead-ends closure, a fresh sink world, and the
   `F(□⊥)@w` seeding trick) each fail, two on soundness and one on termination. **This
   downgrades 597's "D = Tier A (assessed), proceed now" to "Tier A cost, but blocked on a
   spec-shape decision first."** It is additive-fixable (a sibling `RuleApplicationSpecSerial`)
   rather than fatal, but it is a real design gate that must be decided before D, DB, D4, D5, or
   D45 — five of the eight corners — can be templated.

5. **TB is the one corner that is genuinely free of every gate.** Both its ingredient rules exist
   and are pure-`persistent`, never-minting (`modalApplyOneT`, `FrameRules.lean:85`;
   `modalApplyOneB`, `:362`), both discharge the full `RuleApplicationSpec`, and both closure
   operators exist in Mathlib (`Relation.ReflGen`, `Relation.SymmGen`). TB should be tranche 1,
   alone.

6. **This task as scoped cannot be completed as one task without violating the zero-debt gate.**
   The measured per-corner cost is 1,700 lines (Tier A) / 3,600 (Tier B) / 13,540-and-counting
   (Tier C). Eight corners is a 25,000–40,000-line workstream against a 45,307-line subsystem.
   §8 recommends the acceptance criterion's second arm — *"an explicit documented out-of-scope
   note per corner"* — be used deliberately for the gated corners, with the matrix note landing
   as this task's own deliverable and the corner work re-tranched into successor tasks. That is
   the acceptance criterion's own sanctioned outcome ("so the matrix is intentionally complete
   rather than accidentally ragged"), not a deferral.

---

## 1. Ground Truth at HEAD

### 1.1 The decidability column, verified

All eight existing `Decidable` instances, re-read at HEAD:

| System | Instance | File:line | Driver it runs |
|---|---|---|---|
| K | `instDecidableKValid` | `Tableau/CompletenessLoop.lean:2295` | `modalTableau` |
| T | `instDecidableTValid` | `Tableau/FrameCompleteness.lean:1317` | `modalTableauT` |
| B (KB) | `instDecidableBValid` | `Tableau/FrameCompleteness.lean:1933` | `modalTableauB` |
| S5 | `instDecidableS5Valid` | `Tableau/FrameCompleteness.lean:2426` | `modalTableauS5` |
| K5 (Five) | `instDecidableFiveValid` | `Tableau/FrameCompleteness.lean:3204` | `modalTableauFive` |
| KB5 | `instDecidableKb5Valid` | `Tableau/FrameCompleteness.lean:4080` | `modalTableauKb5''` |
| **S4** | **`instDecidableS4Valid`** | **`Tableau/FrameCompleteness.lean:8281`** | `modalTableauS4KeyedOrdered` |

Seven of fifteen. The eight ragged corners — **D, K4, K45, D4, D5, D45, DB, TB** — have no
`Valid` predicate, no frame condition, no tableau driver, and no `Decidable` instance. Confirmed
by exhaustive grep: the only `frameValid` instantiations in the tree are `tValid` (:969),
`s4Valid` (:1060), `bValid` (:1470), `s5Valid` (:1576), `fiveValid` (:1585), `kb5Valid` (:1594),
all in `FrameSoundness.lean`, plus `kValid` (`Soundness.lean:347`) which predates `frameValid`.

### 1.2 Corrections to the task description's anchors

Five of the seven anchors the task description quotes are wrong, four of them non-trivially.
Corrected values are the ones in §1.1.

| Claim in task description | Verified at HEAD | Delta |
|---|---|---|
| K at `CompletenessLoop.lean:2295` | `:2295` | correct |
| T at `FrameCompleteness.lean:1318` | `:1317` | −1 |
| KB at `:1933` | `:1933` | correct |
| S5 at `:2429` | `:2426` | −3 |
| K5/Five at `:3220` | `:3204` | −16 |
| KB5 at `:4165` | `:4080` | −85 |
| "S4 is in flight" | `instDecidableS4Valid` exists at `:8281` | **superseded** |

Also stale in the task description: *"dependencies 511/535/597 have all landed"* — true, but the
framing "the tableau driver abstraction decision" landed as a decision **against** the extension
the task then proposes (§0.2). And the freeze clause names task **534**, which is `[NOT STARTED]`
with no `specs/534_*` directory and produced nothing — that third of the freeze clause is
vacuous (§7).

### 1.3 Tree state

- HEAD `895179d1`; **no `.lean` file has changed since `b2488f0e`** (511's capstone), so the tree
  sits at 511's verified-green state: full `lake build`, zero sorry in the tableau subtree,
  standard axiom triple only.
- Tableau subsystem: **45,307 lines across 32 files** (was 44,692/32 at 597's measurement).
- Every `sorry` match under `Cslib/Logics/Modal/Tableau/` is inside a docstring or comment
  (15 matches, all prose: "sorry-free", "standing `sorry`", "their `sorry`s were an unsound
  foundation"). **There is no live `sorry` in the tableau subtree.** The 39 `sorry` matches under
  `Cslib/Logics/Modal/` are concentrated in `Metalogic/Constructive/**` and
  `Metalogic/Intuitionistic/**` — entirely outside this task's territory.

---

## 2. The Architecture the Corners Must Plug Into

Five layers, all verified by reading the definitions.

### 2.1 Validity: `frameValid` (`FrameSoundness.lean:75-88`)

```lean
abbrev FrameCondition := ∀ {World : Type}, (World → World → Prop) → Prop        -- :75
def frameValid (FC : FrameCondition) (φ : Proposition Atom) : Prop :=            -- :85
  ∀ (World : Type) (m : Model World Atom), FC m.r → ∀ (w : World), Satisfies m w φ
```

Adding a corner's `Valid` predicate is **two lines**: an `FC` and a `frameValid FC` alias. This
is the cheapest part by a wide margin, and it is independent of every gate below. The relation
primitives all exist in `Cslib/Foundations/Relation/`: `Serial` (`Defs.lean:74`), `IsTrans`,
`Std.Symm`, `Std.Refl`, `Relation.RightEuclidean` (`Euclidean.lean`).

### 2.2 Countermodel extraction: Strategy B, closure-at-extraction

```lean
def extractModelWith (Cl : (WorldIndex → WorldIndex → Prop) → (WorldIndex → WorldIndex → Prop))
    (b : ...) (acc : Accessibility) : Model WorldIndex Atom where
  r := Cl (fun w w' => acc.hasEdge w w' = true)                       -- FrameCompleteness.lean:85
  v w p := b.any (...)
```

The frame condition then comes **free** off the closure operator's instance
(`extractModelT_refl` `:120`, `extractModelS4_trans` `:175`, `extractModelFive_rightEuclidean`
`:2466`). Instantiations at HEAD:

| Extractor | `Cl` | File:line |
|---|---|---|
| `extractModel` (K) | `id` | `Completeness.lean:59` (bridge `extractModelWith_id`, `:98`) |
| `extractModelT` | `Relation.ReflGen` | `FrameCompleteness.lean:105` |
| `extractModelS4` | `Relation.ReflTransGen` | `:145` |
| `extractModelB` | `Relation.SymmGen` | `:430` |
| `extractModelS5` | `Relation.EqvGen` | `:504` |
| `extractModelFive` | `Relation.EuclGen` | `:2447` |
| `extractModelKb5` | symmetric `EuclGen` variant | `:3221` |

`Relation.EuclGen` is CSLib's own (`Foundations/Relation/Euclidean.lean:141`), written because
Mathlib ships no Euclidean closure; it carries `instance : RightEuclidean (EuclGen r)` (`:146`),
`instance [Std.Symm r] : Std.Symm (EuclGen r)` (`:167`), and `EuclGen.least` (`:174`).

### 2.3 Rules: layered wrappers, not a combinator

The rule stack is built by literal wrapping, each layer merging its own arms into the inner
layer's `persistent` output:

```
modalApplyOne          (K)          Rules.lean:78
  └─ modalApplyOneT    (K+T)        FrameRules.lean:85     ← + modalTBoxSelf/modalTDiaNegSelf
       └─ modalApplyOneS4Rules (K+T+4) FrameRules.lean:158 ← + modalFourBoxProp/modalFourDiaNegProp
  └─ modalApplyOneB    (K+B)        FrameRules.lean:362    ← + modalBBoxBack/modalBDiaNegBack
```

Each layer ships an agreement lemma (`modalApplyOneT_eq_of_not_boxPos_diaNeg` `:111`,
`modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg` `:184`, `modalApplyOneB_eq_of_not_boxPos_diaNeg`
`:389`) stating it collapses to the inner rule outside the two shapes it touches. **This
agreement lemma is the load-bearing reuse mechanism**: it is what lets a new corner inherit every
propositional and mint case from K unchanged and pay only for the two modal shapes it modifies.

Euclidean-family rules (`modalApplyOneS5`, `S5Simplification.lean:181`; `modalApplyOneS5w`,
`:480`; `modalApplyOneFive`, `FiveSimplification.lean:488`; `modalApplyOneKb5''`, `:1707`) are
**not** in this wrapping chain — they replace K's mint arm with a witness-reuse arm, which is why
they cannot discharge `rankStep` and live in Tier B.

### 2.4 Obligations: `RuleApplicationSpec` (`GenericDriver.lean:179-338`)

Two structures. `RuleApplicationSpecCore` (8 fields: `freshLocal`, `outputsSubsetUniverse`,
`persistentFresh`, `branchingLength`, `localShapeInvariance` F8, `boxPosNotExpanding` F9,
`diaNegNotExpanding` F10, `boxNegWitness'` F11', `diaPosWitness'` F12') carries everything the
**completeness** side consumes. `RuleApplicationSpec extends` it with three more (`rankStep`,
`outDegStep`, `knownWorldsStep`) that the K-style **termination measure** needs.

Discharged in full by: K (`modalApplyOne_spec`, `:353`), T, B. Core-only by: S5w, Five, Kb5,
Kb5''. **Not at all by S4** — `GenericDriver.lean:127-130` records why: transitive box
propagation places `T(□φ)` (unchanged modal depth) at successor worlds, falsifying `rankStep`'s
exact-decrement edge invariant.

### 2.5 Termination evidence: the `Aux` axis

`AuxStepPreserved` / `AuxBounds` / `ModalLoopInvHintikka` / `modalExpandBranchesHintikka`
(`CompletenessLoop.lean:263-420`, `:1410`) factor the world-bound conjunct out of the loop
invariant into an opaque caller-supplied predicate. Instances: `ModalLoopAuxK` (rank + potential),
`ModalLoopAuxS5w` (tag cardinality), `ModalLoopAuxFive`, `ModalLoopAuxKb5''`. S4 supplies a
sibling argument instead (`S4LoopInv`, `S4/Invariant.lean:85`, a pigeonhole bound on
`2 ^ (2 * |modalSubfmls φ₀|)` birth keys) plus its own fuel `modalFuelS4`.

**This is the abstraction the task description asks to "extend".** It already exists and is
already instantiated at four systems.

---

## 3. What a Corner Actually Costs

597's measured per-corner figures, re-confirmed against HEAD file sizes:

| Tier | Reference corners | Decls | Lines | Distinguishing constraint |
|---|---|---|---|---|
| **A** | T, B | 62 / 56 | 1,796 / 1,627 | full `RuleApplicationSpec` dischargeable; arms are pure-`persistent`, never mint |
| **B** | S5+S5w, Five+FiveProp, Kb5''+Kb5''Prop | 94 / 89 / 87 | 3,776 / 3,553 / 3,636 | `rankStep` refuted; witness-reuse mint + bespoke world bound + own `Aux` |
| **C** | S4 + Keyed + KeyedOrdered | 240 | 13,540 | loop-checking + threaded state + soundness-critical ordered traversal |

Cross-system skeleton census (597 §4.4): 104 declaration skeletons instantiated at ≥2 systems,
covering **330 declarations = 29% of the subsystem**. The widest are `modalApplyOne@` (11×),
`modalTableau@` / `modalStepBranch@` / `modalExpandBranches@` (8× each), `extractModel@` (6×),
the six `RuleApplicationSpec` field discharges (5× each).

---

## 4. Per-Corner Analysis

Frame conditions read off `Cube.lean` (all fifteen systems are defined there, `:27-85`; the
Hilbert side is complete at `Metalogic/Systems/{B,D,D4,D45,D5,DB,K,K4,K45,K5,KB5,S4,S5,T,TB}`
with conservativity at `Metalogic/InterSystem/Conservativity.lean`).

| Corner | `Cube.lean` | Frame condition needed | Closure operator | Rule ingredients | Tier | Gate |
|---|---|---|---|---|---|---|
| **TB** | `:73` | `Std.Refl ∧ Std.Symm` | `ReflGen ∘ SymmGen` — both exist | `modalApplyOneT` + `modalApplyOneB` arms, both non-minting | **A** | **none** |
| **D** | `:53` | `Relation.Serial` | none suffices (§5.1) | new serial mint rule | A-cost | **spec-shape (§5.1)** |
| **DB** | `:69` | `Serial ∧ Std.Symm` | `SymmGen` + serial repair | D rule + `modalApplyOneB` arms | A/B | spec-shape (§5.1) |
| **K4** | `Four`, `:41` | `IsTrans` | `Relation.TransGen` | `modalFourBoxProp`/`modalFourDiaNegProp` **without** the T arms | **C** | **unordered-stack retirement (§6.3)**; T-arm removal (§5.2) |
| **D4** | `:57` | `Serial ∧ IsTrans` | `TransGen` + serial repair | K4 rule + D rule | **C** | both of the above |
| **K45** | `:49` | `IsTrans ∧ RightEuclidean` | `EuclGen` (+ transitivity, §5.3) | `FiveSimplification` rooted-cluster family | **B** | 597 §7.2 combinator prototype |
| **D5** | `:61` | `Serial ∧ RightEuclidean` | `EuclGen` + serial repair | Five family + D rule | **B** | combinator prototype + spec-shape |
| **D45** | `:65` | `Serial ∧ IsTrans ∧ RightEuclidean` | as K45 + serial repair | K45 family + D rule | **B** | combinator prototype + spec-shape |

### 4.1 TB — the one ungated corner

Everything TB needs already exists and is already proven at the two ingredient corners:

- `tbFC : FrameCondition := fun {_} r => Std.Refl r ∧ Std.Symm r`; `tbValid := frameValid tbFC` —
  two lines in `FrameSoundness.lean`, mirroring `s4FC`/`s5FC`/`kb5FC` exactly.
- `extractModelTB := extractModelWith (Relation.ReflGen ∘ Relation.SymmGen)`. Reflexivity comes
  free (`Relation.reflexive_reflGen`); symmetry of the composite is already in-tree as
  `Relation.ReflGen.compRel_symm` (`Foundations/Relation/Confluence.lean:368`) — **exactly the
  lemma TB's frame instance needs, and it is already proved**.
- Rule: wrap `modalApplyOneB` with T's self-propagation arms (`modalTBoxSelf`/`modalTDiaNegSelf`,
  `FrameRules.lean:62,69`), or equivalently wrap `modalApplyOneT` with B's backward arms — the
  same layering pattern `modalApplyOneS4Rules` uses over `modalApplyOneT`. Both arm families are
  pure-`persistent` at **existing** worlds and never mint, so `freshLocal` is discharged by
  agreement with `modalApplyOne` on every mint-shaped input and F9/F10 are satisfiable in the
  existentially-quantified form the bundle already uses.
- Truth lemma: the box-positive/diamond-negative clauses combine T's self-conjunct
  (`hintikkaT_box_pos`, `FrameCompleteness.lean` T section) with B's backward conjunct
  (`hintikkaB_box_pos`, B section); the other two modal shapes reuse the free generic bridges
  `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` (`Completeness.lean`).

Expected cost: at the low end of Tier A (~1,300–1,800 lines), because both arm families and both
truth-lemma conjuncts already exist and only their *conjunction* is new.

### 4.2 The Euclidean tranche (K45, D5, D45)

`FiveSimplification.lean` (3,802 lines) already implements the rooted-Euclidean technique:
mint-with-witness-reuse plus root-aware universal propagation
(`modalFiveBoxAll`/`modalFiveDiaNegAll`), with the structural fact that rooted Euclidean frames
are exactly "root + universal cluster" (`Relation.RightEuclidean.equiv_cod`,
`Euclidean.lean:123`; `rooted_cluster_universal`, `:327`).

597 §7.2's measured observation is the lever here: **`modalApplyOneKb5''` is character-for-character
`modalApplyOneFive` with `modalApplyOneFiveProp` substituted by `modalApplyOneKb5''Prop`** — same
root guard, same `witnessWorldFive`, same two mint arms — yet the difference is re-proved across
all 38 twin declarations (median similarity ≈0.85, 10/38 at >0.90). A rule combinator
parameterised on the propagation helper collapses that clone band. **This is why the Euclidean
tranche is gated on the prototype rather than on its own difficulty**: cloning `FiveSimplification`
three more times at 3,600 lines each replicates a duplication cost that has already been measured
and identified as removable.

Open question flagged and **not** resolved here: whether `k45Valid` is decidable by the *existing*
`modalTableauFive` because `EuclGen`-extracted models happen to be transitive on the cluster. If
`extractModelFive`'s relation were provably `IsTrans`, `modalTableauFive` would decide `k45Valid`
directly (closure ⟹ `fiveValid` ⟹ `k45Valid` since K45 frames ⊆ Euclidean frames; openness ⟹ a
Euclidean **and** transitive countermodel). `EuclGen` is *not* transitive in general (the root
edge is not absorbed), so this almost certainly fails at the root, but it is a cheap probe worth
running before committing 3,600 lines to K45. It is a probe, not a finding.

### 4.3 The transitive tranche (K4, D4)

`GenericDriver.lean:127-130` states the constraint definitively: transitive box propagation
"requires loop-checking (`#worlds ≤ 2^|Sf|`) rather than the depth-based `modalWorldBound` this
bundle presupposes; S4 needs a structurally different termination argument." Transitivity is the
sole discriminator, so K4 and D4 inherit it.

The S4 template is now complete and is the right one. But two adjustments are needed and neither
is free:

1. **T-arm removal.** The S4 rule chain is `modalApplyOneS4 → modalApplyOneS4Rules →
   modalApplyOneT → modalApplyOne`. K4 needs `K + 4` **without** T, i.e. a chain that skips the
   `modalApplyOneT` rung. The 4-arms themselves (`modalFourBoxProp` `:133`,
   `modalFourDiaNegProp` `:146`) are already independent of T and can be wrapped directly over
   `modalApplyOne`. What is *not* free is the S4/* invariant cluster (10 modules, 10,573 lines),
   which is written against `modalApplyOneS4Keyed φ` concretely, not against a base-rule
   parameter. Whether the birth-key pigeonhole argument survives T-arm removal is very likely
   yes (the T arms are pure-`persistent` and contribute nothing to world creation) but is
   **unverified** and is the single largest sizing uncertainty in this report.
2. **Extraction closure changes from `ReflTransGen` to `TransGen`.** `Relation.TransGen` is in
   Mathlib with an `IsTrans` instance. But `extractModelS4`'s truth lemma leans on `ReflTransGen`
   reflexivity in the base case (`Relation.ReflTransGen.refl`); the K4 truth lemma has no such
   base case and its box-positive clause must be re-proved by induction on `TransGen` paths.

**Gate C is a hard prerequisite, not advice.** 597 §9 states it plainly: *"K4 and D4 must be
templated on the ordered stack only, after that retirement — not on the current two-stack state.
Cloning the present S4 cluster twice would replicate the retirement debt as well as the
machinery."* The two-stack duplication is measured at **3,801 lines across 14 twin
invariant-preservation pairs** (`_preserves_accFresh` 0.78, `_accKnown` 0.76, `_bClosure` 0.74,
`_eClosure` 0.74, `_eNodup` 0.69, `_keyLowerBd` 0.66, `_keysDistinct` 0.43, `_keysInUniverse`
0.72, `_keysOriginS4` 0.88, `_keysTotal` 0.79, `_keysWorldsKnown` 0.65, `_worldsContiguousS4`
0.83, `S4LoopInv` 0.27, `S4KeyedHintikkaInv` 0.45), plus the two ~250-line twins 511 added.
Cloning it twice adds ~7,600 lines of debt on day one.

---

## 5. Three Findings That Change the Plan

### 5.1 D's seriality rule conflicts with `RuleApplicationSpec` F9 — NEW

`RuleApplicationSpec.boxPosNotExpanding` (`GenericDriver.lean:239-243`):

```lean
boxPosNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
    sf.sign = .pos → ∀ (ψ : Proposition Atom), sf.formula = .box ψ →
    ∀ (b : ...) (acc : Accessibility),
    (apply sf b acc).1 = .notApplicable ∨ ∃ out, (apply sf b acc).1 = .persistent out
```

`.linear` — the constructor that accompanies world minting (`freshLocal`, `:184-188`) — is
explicitly excluded at the box-positive shape, and dually at diamond-negative (F10, `:247-251`).
The field's own docstring names its consumer: it "is what makes `modalLoopGen_eBoxOnlyNeg` go
through: a `boxPos`-shaped formula can never be the `sf_exp` appended to `e`"
(`CompletenessLoop.lean:565`, private; 59 references to the `eBoxOnlyNeg`/`eDiamondOnlyPos`
family across the library). The mint-licensed shapes F11'/F12' (`:259-277`) are box-**negative**
and diamond-**positive** — exactly K's own two mint arms.

A correct D tableau must mint at a dead-end world *because of* its box-positive content. The
three mint-avoiding alternatives all fail:

1. **Self-loop-at-dead-ends closure** (`serialClosure r w w' := r w w' ∨ (¬∃u, r w u) ∧ w = w'`)
   is a legitimate closure operator and is genuinely serial, so `extractModelWith serialClosure`
   type-checks and discharges the frame condition. But it makes the tableau **unsound**: to use
   it, the rule must infer `T(ψ)@w` from `T(□ψ)@w` at dead-end `w`, and that inference is the T
   axiom, not the D axiom. Seriality does not give reflexivity. Concretely, `d_subset_t`
   (`Cube.lean:118`) proves D-validities are T-validities and `boxImp_not_fiveValid`-style
   separation already establishes the inclusions are strict, so a D procedure that licensed the
   T inference would report `□p → p` as D-valid, which it is not.
2. **A fresh sink world** (extend to `WorldIndex ⊕ Unit` with `∗ → ∗`, dead-ends → `∗`) relocates
   but does not discharge the obligation: `T(□ψ)@w` at a dead-end now requires `ψ` true at `∗`,
   and `∗` carries no branch content to certify it.
3. **Seeding `F(□⊥)@w`** (the D-axiom instance `◇⊤`) at every dead-end world *does* route through
   K's existing box-negative mint arm and *is* sound. But `□⊥` has constant modal depth 1, so the
   minted successor is itself a dead end needing its own `F(□⊥)`, and `rankStep`'s
   exact-decrement invariant never fires. Non-terminating without loop-checking — which would
   promote D from Tier A to Tier C, an ~8× cost increase for the cube's cheapest corner.

**The resolution that fits CSLib's reuse-first philosophy and 597's per-regime-split decision** is
a sibling structure, additive and with zero blast radius:

```lean
structure RuleApplicationSpecSerial (apply : RuleApply Atom) : Prop where
  -- F1-F8, F11', F12' verbatim from RuleApplicationSpecCore
  -- F9/F10 replaced by: boxPos/diaNeg may additionally yield a .linear mint,
  --   provided the mint is confined to dead-end source worlds (a new guard field)
```

together with a generalised `modalLoopGen_eBoxOnlyNeg` that admits the guarded-mint case. That
generalisation is the genuine unknown: it is `private` in `CompletenessLoop.lean` with 59
downstream references to its family, so the change must be **additive** (a `_serial` sibling
lemma) rather than a widening of the existing one. Widening in place would put 107
`RuleApplicationSpec` references at risk and is exactly the Chronicle failure mode task 564
measured at +80 lines / 40 sites.

**Consequence for the plan**: this decision must be made and prototyped on D alone before DB, D4,
D5, or D45 are attempted. Five of eight corners depend on it.

### 5.2 The gates 597 set are still open, and unowned

| Gate | 597 §ref | Status at HEAD | Owning task |
|---|---|---|---|
| A. Finish S4 to the six-corner standard | §8 action 1 | **CLEARED** — `instDecidableS4Valid` at `FrameCompleteness.lean:8281` | 511 `[COMPLETED]` |
| B. Prototype the universal-cluster rule combinator on `Kb5''`-from-`Five`, measure, then gate the Tier-B corners on the measurement | §8 action 2, §7.2 | **NOT DONE** — no combinator exists; `modalApplyOneKb5''` (`FiveSimplification.lean:1707`) and `modalApplyOneFive` (`:488`) remain separate clones | **none** |
| C. Retire the unordered S4 stepper stack before templating K4/D4 | §9 warning | **NOT DONE** — `modalTableauS4Keyed` live at `LoopChecking.lean:156`; `:192` and `S4/Driver.lean:630,2511` still say "Phase 15 retires"; 152 in-library refs to `modalStepBranchS4Keyed`/`modalExpandBranchesS4Keyed` | 506 `[PARTIAL]`, does not name it |
| D. *(new, §5.1)* Decide the serial-rule spec shape | — | **NOT DONE** | none |

Gates B, C, and D are the actual critical path. None is a research question this report can close
by reading — B and D require prototyping and measurement, C is a destructive refactor.

### 5.3 Rule-application order is soundness-critical (inherited constraint)

597 §6.2, machine-checked: the unordered keyed S4 driver's soundness is **false**, with a
countermodel in `CslibTests/S4LoopGuardRegression.lean`. The repair was not to the guard predicate
but to *when* a minting shape may fire (settled-context scheduling,
`modalTableauS4KeyedOrdered`, `LoopChecking.lean:203`). This is why `instDecidableS4Valid`'s
docstring (`FrameCompleteness.lean:8278-8280`) explicitly names which driver it may and may not
use: *"NOT the unordered `modalTableauS4Keyed`, whose soundness is false, and NOT the live-guard
`modalTableauS4`, which has no completeness proof of its own."*

**Implication for K4/D4**: their drivers must replicate the ordered scheduling, and any shared
traversal abstraction is unsound-by-construction unless it also carries the ordering obligation.
597 §8 action 3: *do not build the traversal rung.*

---

## 6. Frozen Deliverables

The task's freeze clause ("keep all frozen deliverables from tasks 300/534/506 untouched") has no
enumerated list anywhere in those tasks' artifacts. Reconstructed from their handoffs and
summaries:

### Task 300 (`[BLOCKED]`; Phase 1 complete, Phase 2 blocked)
Source: `specs/300_modal_extensions_t_s4_s5/handoffs/phase2-blocked-handoff.md`.

| File | Frozen declarations |
|---|---|
| `Cslib/Logics/Modal/Tableau/FrameRules.lean` | `modalTBoxSelf` (:62), `modalTDiaNegSelf` (:69), `modalApplyOneT` (:85), `modalApplyOneT_eq_of_not_boxPos_diaNeg` (:111) |
| `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` | `FrameCondition` (:75), `trivialFC` (:79), `frameValid` (:85), `branchSatisfiableIn` (:112), `modalTableau_sound_frame` (:918), `reflFC` (:965), `tValid` (:969), `branchSatisfiableIn_reflFC_boxPos_mem`/`_diaNeg_mem`, `modalTBoxSelf_sound`, `modalTDiaNegSelf_sound` |
| `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` | `extractModelWith` (:85), `extractModelWith_id` (:98), `extractModelT` (:105), `extractModelT_r` (:113), `extractModelT_refl` (:120), `extractModelT_hasEdge_imp_r` (:132) |
| `Cslib.lean` | barrel registration of `FrameRules` |

### Task 506 (`[PARTIAL]`; Phases 1-7 complete, 8-9 blocked)
Source: `specs/506_.../summaries/01_s4-loopchecking-termination-decidability-summary.md`.

| File | Frozen declarations |
|---|---|
| `Tableau/FrameRules.lean` | `modalFourBoxProp` (:133), `modalFourDiaNegProp` (:146), `modalApplyOneS4Rules` (:158), `modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg` (:184) |
| `Tableau/LoopChecking.lean` **and its `S4/` split** | `formulasAtWorld`, `sameRelevantSet` (+ refl/symm/trans), `blockingWorld`, `modalApplyOneS4`, `modalStepBranchS4`/`modalExpandBranchesS4`/`modalTableauS4`, `modalHintikkaSetS4`, `hintikkaS4_*` bridges, `modalWorldBoundS4`, `modalUniverseS4`, `S4LoopInv` |
| `Tableau/FrameCompleteness.lean` | `extractModelS4` (:145), `extractModelS4_hasEdge_imp_r` (:183), `modalTruthLemmaS4` (:234), `modalOpenBranchS4_countermodel` (:405) |
| `Tableau/FrameSoundness.lean` | `s4FC` (:1056), `s4Valid` (:1060), `branchSatisfiableIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`, `modalFourBoxProp_sound`, `modalFourDiaNegProp_sound` |
| `Cslib.lean` | barrel entry for `LoopChecking` |

**Path-drift warning**: most of what 506 called `LoopChecking.lean` now lives in
`Cslib/Logics/Modal/Tableau/S4/` (10 modules, 10,573 lines; the split landed under task 565).
Current homes: `modalApplyOneS4`/`modalTableauS4` → `S4/Driver.lean:122,219`; `modalHintikkaSetS4`
→ `S4/Hintikka.lean:74`; `S4LoopInv` → `S4/Invariant.lean:85`; `modalWorldBoundS4`/`signedSubfmls`
→ `S4/Universe.lean:208,280`; `blockingWorldS4Keyed` → `S4/Guard.lean:173`;
`successorBirthContent` → `S4/BirthKey.lean:79`.

**Additional explicit no-touch, from 506's own plan** (`plans/01_...md:201,586`):
`Cslib/Logics/Modal/Tableau/FmpMeasure.lean` must remain untouched — a corner needing a new
termination measure builds a sibling invariant, never extends `ModalPotentialInv`. 506's summary
confirms its `FmpMeasure.lean` diff was empty across the whole task. **This constrains every
serial and transitive corner in §4.**

### Task 534 — nothing frozen
`[NOT STARTED]`, no `specs/534_*` directory, zero artifacts. Its own description imposes a freeze
on *other* tasks' assets (`instDecidableFiveValid`/`instDecidableKb5Valid`, the equivalence
route). **The 534 third of 548's freeze clause is vacuous and should be dropped from the plan.**

### Implied freeze, not in the clause but load-bearing
All seven existing `Decidable` instances and their sound/complete/decides triples (§1.1), plus
`CslibTests/S4LoopGuardRegression.lean` (the machine-checked unsoundness countermodel for the
unordered keyed driver) and `CslibTests/ModalFrameSeparation.lean` /
`CslibTests/TableauConformance.lean`.

---

## 7. Tactic Survey

No proof goals were opened — this dispatch is architectural reconnaissance, and every question it
answers is answered by reading definitions and measuring, not by closing goals. Recording the
survey as not-applicable rather than fabricating results.

What the *implementation* dispatches will need, based on the existing corners' proof style
(sampled from `modalApplyOneT_persistentFresh`, `LoopChecking.lean:229-320`, and the T/B truth
lemmas): `rcases`/`split_ifs` shape dispatch on `sf.sign`/`sf.formula`, `simp_all` to close
agreement lemmas, `List.mem_filterMap`/`List.mem_append` for the propagation-helper membership
characterisations, and `infer_instance` for every frame-condition discharge off a closure operator
(the pattern at `extractModelT_refl:124`, `extractModelS4_trans:179`,
`extractModelFive_rightEuclidean:2470`). No `omega`/`ring`/`linarith` surface appears in the
rule/extraction layer; the arithmetic is confined to `FmpMeasure.lean`'s `geomCap` engine, which
is frozen.

---

## 8. Recommendation

**Do not attempt eight corners in one task.** Measured cost is 25,000–40,000 lines against a
45,307-line subsystem; three of the four gates in §5.2 are open and unowned; and the one new
finding (§5.1) blocks five of the eight corners behind a design decision that has not been made.
Attempting it as scoped produces either a partial implementation (which the zero-debt gate
forbids) or a `[BLOCKED]` at the first serial corner.

**Do use the acceptance criterion's second arm deliberately.** It reads: *"either a Decidable
instance per corner, or an explicit documented out-of-scope note per corner stating why (e.g.
cost/benefit), so the matrix is intentionally complete rather than accidentally ragged."* The
matrix note **is** a first-class deliverable, and it is the one this task can land completely and
sorry-free. Recommended shape:

**Tranche 1 — this task.** Land two things, both fully closable now:
1. **TB end-to-end** (§4.1): `tbFC`, `tbValid`, `extractModelTB`, the TB rule, its
   `RuleApplicationSpec` discharge, truth lemma, soundness, completeness, `tbValid_decides`,
   `instDecidableTBValid`. Every ingredient exists; `Relation.ReflGen.compRel_symm`
   (`Confluence.lean:368`) is already in tree and is exactly the frame instance TB needs.
   This takes the matrix from 7/15 to 8/15.
2. **The intentional-completeness note**: a documented section (in `FrameCompleteness.lean`'s
   module docstring or a sibling `Cube` doc) stating, per remaining corner, the frame condition,
   the assessed tier, the specific gate, and the cost estimate — i.e. §4's table with §5's
   findings attached. This is what converts "accidentally ragged" into "intentionally
   incomplete", which is the acceptance criterion's own standard.

**Tranche 2 — successor task, serial-rule spec decision.** Prototype `RuleApplicationSpecSerial`
+ the additive `modalLoopGen_eBoxOnlyNeg_serial` sibling on **D alone**, and measure the re-cut
proof sites before generalising. Unblocks D, DB, D5, D45, D4.

**Tranche 3 — successor task, 597 §7.2 combinator prototype.** `Kb5''`-from-`Five`, measured.
Gates K45, D5, D45.

**Tranche 4 — successor task, unordered S4 stack retirement** (`LoopChecking.lean:192`'s
"Phase 15"). Gates K4, D4.

**Tranche 5 — the gated corners**, in whatever order the measurements from 2–4 justify.

Tranches 2, 3, and 4 are mutually independent and can run in parallel.

**Zero-debt compliance**: nothing above defers behind a `sorry` or introduces an axiom. The
out-of-scope notes are the acceptance criterion's sanctioned alternative, not a deferral, and
they carry a named gate and a cost figure each rather than "revisit later". Where a route was
found not to work (§5.1's three alternatives), it is refuted with the reason, not parked.

---

## 9. Limits of This Report

Stated rather than hidden.

- **The §5.1 F9 conflict is verified from the field statement; the proposed fix is not
  prototyped.** That `RuleApplicationSpecSerial` + an additive `_serial` loop lemma suffices is a
  design assessment, not a measured fact. The 59-reference `eBoxOnlyNeg` family is the risk
  surface.
- **The K4 T-arm-removal question (§4.3 item 1) is unverified.** Whether the S4/* birth-key
  pigeonhole argument survives dropping the T rung is very likely yes but was not checked against
  the invariant fields. It is the largest sizing uncertainty here.
- **The K45-via-`modalTableauFive` probe (§4.2) is stated as a probe, not a finding.** `EuclGen`
  is almost certainly not transitive at the root, but that was not proved or refuted.
- **No `lake build` was run.** The green claim rests on `git log` showing no `.lean` change since
  511's verified capstone (`b2488f0e`), plus a grep confirming every `sorry` token in the tableau
  subtree is prose.
- **Tier assignments for the new corners are assessments from frame conditions and templates**,
  inheriting 597 §9's own caveat. The load-bearing parts — K4/D4 as Tier C (which follows from
  transitivity alone via `GenericDriver.lean:127-130`) and TB as ungated — are the parts this
  report verified directly.

---

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, CUP 2001 — §4.5, §4.8-4.9 (rooted normal forms,
  Euclidean tableaux), §6.6 p.382 (S5 decidability / NP-completeness). Cited in-tree at
  `Cube.lean:19`, `FrameCompleteness.lean:2428`, `FiveSimplification.lean` §References.
- `specs/597_modal_tableau_driver_abstraction_decision/reports/01_driver-abstraction-decision.md`
  — the driver-abstraction decision, its five-axis census, per-corner cost tiers, and the
  three-gate tranching this report updates.
- `specs/511_s4_loop_checking_termination/summaries/03_s4-ordered-driver-completeness-summary.md`
  — S4 capstone; the evidence that Gate A is cleared.
- `specs/506_.../summaries/01_s4-loopchecking-termination-decidability-summary.md` and
  `plans/01_...md:201,586` — 506's frozen set and the `FmpMeasure.lean` no-touch constraint.
- `specs/300_modal_extensions_t_s4_s5/handoffs/phase2-blocked-handoff.md` — 300's frozen set.
