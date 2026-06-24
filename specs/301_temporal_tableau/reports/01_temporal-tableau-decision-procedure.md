# Research Report: Tableau Decision Procedure for Temporal Logic (Task 301)

## Metadata

- **Task**: 301 — `temporal_tableau`
- **Task type**: cslib
- **Session**: sess_1782337264_0e4361
- **Agent**: cslib-research-agent
- **Date**: 2026-06-24
- **Status**: researched
- **Estimated size**: 2,000–2,500 lines across 8 files under `Cslib/Logics/Temporal/Tableau/`

## Summary

Task 301 asks for a tableau decision procedure for the existing temporal logic
`Cslib.Logic.Temporal.Formula` (primitives `atom, bot, imp, untl, snce`, Łukasiewicz
encoding), with until/since decomposition rules, time labels, temporal-ordering tracking,
and density/discreteness frame-class rules.

Two distinct analogue systems exist in the repo and the task threads them together:

1. **Shared Foundations tableau layer** — `Cslib/Foundations/Logic/Tableau/*` (namespace
   `Cslib.Logic.Tableau`): a fully generic, `F`/`L`-parameterized tableau kernel
   (`Sign`, `SignedFormula F L`, `Branch F L`, `ClosureReason`/`ClosureCondition`,
   `RuleResult F L`, `PropTableauRule`/`applyPropRule`). The `RuleResult.persistent`
   variant and the whole layer were explicitly built "for downstream modal and temporal
   tableau tasks (tasks 299–301)". **This is the substrate the task says to build on.**

2. **Bimodal decidability system** — `Cslib/Logics/Bimodal/Metalogic/Decidability/*`
   (~6,000 lines, namespace `Cslib.Logic.Bimodal.Metalogic.Decidability`): a complete,
   pre-Foundations tableau with its **own** `SignedFormula`, `Branch`, `TimeOrdering`,
   and `RuleResult` types (all monomorphic over `Bimodal.Formula`, which has a `box`
   constructor temporal logic lacks). It already implements the exact until/since
   event-witness/guard-continue branching, Reynolds co-decomposition, `TimeOrdering`
   tracking, and density/discreteness rules the task needs — but as **algorithms to port**,
   not types to reuse.

The correct architecture: instantiate the **Foundations** generic kernel at
`F = Temporal.Formula Atom`, `L = Nat` (time index), reuse Modal/Tableau's
world-introduction pattern (`Accessibility` → a temporal `TimeOrdering`) as the structural
template, and **port the bimodal until/since/frame-class rule bodies** onto that kernel.
The proof architecture (Soundness/Completeness/DecisionProcedure) should follow the
**Propositional Classical** template (the only fully-proved soundness in the codebase),
extended with the temporal truth-lemma cases and an eventuality-defect closure mode.

Two reuse caveats are load-bearing: (a) the temporal `Formula` already has everything the
tableau needs to plug in — `DecidableEq` (derived), `complexity`, a rich `Subformulas`
API with `untl_left/right_mem`, `snce_left/right_mem`, transitivity — but needs a
`Hashable` instance added; (b) the genuinely *new* obligation with no propositional/modal
analogue is **eventuality fulfilment / loop-blocking** for `until`/`since` and its
soundness, which is where the riskiest proofs live.

## Findings

### 1. The temporal `Formula` type (confirmed)

`Cslib/Logics/Temporal/Syntax/Formula.lean:88`:

```lean
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Formula Atom)
  | untl (φ₁ φ₂ : Formula Atom)   -- Burgess: untl event guard
  | snce (φ₁ φ₂ : Formula Atom)
deriving DecidableEq
```

All other connectives are Łukasiewicz/Burgess `abbrev`s: `neg φ = imp φ bot`,
`top = imp bot bot`, `or`, `and`, and derived temporal ops
`someFuture φ = untl ⊤ φ` (F), `allFuture = ¬F¬` (G), `somePast = snce ⊤ φ` (P),
`allPast = ¬P¬` (H), `next = untl ⊥ φ` (X), `prev = snce ⊥ φ` (Y), plus
`release`, `trigger`, `weakUntil`, `strongRelease`, etc.

**Burgess convention** (event, guard) — critical for rule writing and matches the bimodal
system exactly: `untl event guard` at `t` ≡ `∃ s > t, event(s) ∧ ∀ r ∈ (t,s), guard(r)`
(`Semantics/Satisfies.lean:61`). `snce` mirrors to the past. `someFuture φ = untl φ ⊤`
holds φ as the *event*; the generic until is filtered from `someFuture` by checking
`guard == ⊤` (the bimodal `asUntil?`/`asSince?` helpers do exactly this).

Already-present support the tableau can lean on:
- `Formula.complexity` (Formula.lean:205) — pattern-aware, can seed the fuel bound.
- `Formula.atoms`, `temporalDepth`, `countImplications`, `swapTemporal` (involution +
  duality lemmas).
- `Syntax/Subformulas.lean`: `subformulas`, `subformulaCount`, and membership/transitivity
  lemmas including `untl_left_mem_subformulas`, `untl_right_mem_subformulas`,
  `snce_left_mem_subformulas`, `snce_right_mem_subformulas`, `subformulas_trans`,
  `self_mem_subformulas`. **These are exactly what the termination/closure (subformula
  property) argument needs** and are already proven.
- `Syntax/Context.lean`: `Context Atom := List (Formula Atom)`.

### 2. Semantic target for Soundness/Completeness (confirmed)

`Semantics/Model.lean:42`: `TemporalModel D Atom` is just `valuation : D → Atom → Prop`
over `[LinearOrder D]` (the frame **is** the linear order — no accessibility relation,
no world histories; single time-line). `Semantics/Satisfies.lean` gives the recursive
`Satisfies` with `@[simp]` constructor lemmas (`untl_iff`, `snce_iff`, `someFuture_iff`,
`allFuture_iff`, …).

`Semantics/Validity.lean` already defines the **exact validity hierarchy the frame-class
tableau must target**:
- `Valid` — all nontrivial `LinearOrder`s.
- `ValidSerial` — `+ NoMaxOrder + NoMinOrder`.
- `ValidDense` — `+ DenselyOrdered`.
- `ValidDiscrete` — `+ SuccOrder + PredOrder + IsSuccArchimedean`.

So `Tableau` `FrameClass.Base/Dense/Discrete` results connect cleanly to
`Valid(Serial)/ValidDense/ValidDiscrete` respectively. This removes a major design
question — the semantic side already exists.

`Logics/Temporal/ProofSystem/Axioms.lean:40` already defines a matching
`FrameClass { Base, Dense, Discrete }` with `deriving DecidableEq, BEq, Hashable`, an
`LE` instance, `DecidableRel (≤)`, an `Axiom.density` constructor, and
`Axiom.minFrameClass` (`density → .Dense`). **Reuse this enum** — do not introduce a new
one. (Note: this mirrors the bimodal `FrameClass` lattice where `Dense`/`Discrete` are
incomparable maxima above `Base`; linearity is baked into the Base axioms, not a toggle.)

### 3. Foundations generic kernel — reuse directly (set F = Temporal.Formula Atom, L = Nat)

| Foundations declaration (`Cslib.Logic.Tableau`) | Reuse for temporal |
|---|---|
| `Sign` (`Sign.lean:46`) + `flip/isPos/isNeg` | direct |
| `SignedFormula F L` (`SignedFormula.lean:49`) + `pos/neg/flip/withLabel` | direct; `F = Temporal.Formula Atom`, `L = Nat` (time index, modal uses `WorldIndex := Nat` the same way) |
| `Branch F L := List (SignedFormula F L)` (`Branch.lean:47`) + full API (`contains`, `extend`, `extendMany`, `positives/negatives`, `hasPosAt/hasNegAt`, `formulasAt`, `labels`, `findContradiction`, `hasContradiction`, `hasBotPos`) | direct |
| `ClosureReason F L` (`Closure.lean:54`), `ClosureCondition` class + `ClassicalClosure` instance | direct for the `T(⊥)` + same-label `T(φ)/F(φ)` closure; **must extend** with eventuality-defect closure |
| `RuleResult F L` (`RuleResult.lean:58`): `linear / branching / persistent / notApplicable` | direct — `persistent` was added specifically for task 301's until/since propagation |
| `PropTableauRule`, `applyPropRule`, `tryAllPropRules` (`PropositionalRules.lean`) | direct for the classical base connectives — supply temporal `*Of?` decomposition functions |

`applyPropRule` recognizes connectives via caller-supplied decomposition functions
(`andOf?`, `orOf?`, `impOf?`, `negOf?`), so it works on the Łukasiewicz encoding with no
modification. All propositional results preserve the input time-label (no new time point),
exactly right.

### 4. Modal/Tableau — the world-introduction structural template

The Modal K tableau (`Cslib/Logics/Modal/Tableau/`) is the precedent for a rule that
**introduces a new label (world)** — the structural twin of `until` needing a new time
point. Copy its shape, retyped to time:

- `Accessibility` (`Modal/Tableau/Branch.lean:54`): `{ edges : List (WorldIndex × WorldIndex) }`
  with `addEdge/successorsOf/hasEdge/allWorlds`. The docstring states it is threaded
  "analogously to the `TimeOrdering` in the Bimodal tableau". → A temporal `TimeOrdering`
  (see §5) replaces it.
- `modalNextWorld := modalMaxWorld + 1` with freshness lemma `modalNextWorld_gt`
  (`Branch.lean:104`). → temporal fresh-time generator + freshness lemma.
- `modalApplyOne sf b acc : RuleResult … × Accessibility` (`Rules.lean:68`) returns a
  **pair** `(RuleResult, updated relation)`. This is the exact signature the temporal
  `applyOne` should use, threading the `TimeOrdering`.
- Rule kinds: `boxPos`/`diamondNeg` → `.persistent` (propagate to *recorded* successors,
  re-fire as new ones appear); `diamondPos`/`boxNeg` → `.linear` (create fresh world,
  add edge, propagate existing universals). The K-soundness note ("propagate only to
  recorded successors, not all worlds") maps directly: temporal universals (G/H) and
  Reynolds co-decomposition must propagate only along the recorded `TimeOrdering`.
- `Modal/Tableau/Saturation.lean`: `ModalTableauResult` (`closed | openBranch branch acc`),
  `modalFuel`, `modalStepBranch` (note: `persistent` results keep `sf` *off* the expanded
  set so it re-fires — Saturation.lean:117), `modalExpandBranches` worklist,
  `modalHintikkaSet`. World-subset blocking is the termination device → temporal needs
  time-subset blocking plus eventuality fulfilment.
- `Modal/Tableau/Closure.lean` simply aliases the Foundations `ClassicalClosure`.

### 5. The hardest part — until/since decomposition (literature-grounded + ported)

This is the core of the task and has **no modal analogue**. The bimodal system already
contains a complete, tested implementation in
`Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` that should be ported (retyped
from `Bimodal.Formula` to `Temporal.Formula`, dropping all box/diamond/world machinery —
temporal logic has a single time-line, so `Label` collapses to a bare time index).

**Standard tableau theory (Wolper/Reynolds/Goré) for strict until/since.** The strict-until
fixpoint identity is:

```
U(event, guard) @ t  ≡  ∃ s>t. [ event@s  (witness now-next) ]
                                ∨ [ guard@s ∧ U(event,guard)@s  (defer: guard holds, obligation recurs) ]
```

This yields the **event-witness vs guard-continue** branching. The dual `since` mirrors
to the past. The negative `F(U(event,guard))` is the dual (box-like, conjunctive)
"Reynolds co-decomposition": at each recorded future time, either the event fails or the
guard fails-and-the-co-obligation continues — propagated *persistently* across the recorded
order. The eventuality (`event`) must eventually be *fulfilled*; an open branch that loops
without fulfilling a positive `until` is **closed by eventuality defect** — the one new
closure mode (see §7).

**Bimodal `untlPos` rule body** (`Tableau.lean:688`, the literal port template):

```lean
| .untlPos, .pos, φ =>
    match asUntil? φ with
    | some (event, guard) =>
      let freshTime := branch.nextTime
      let freshLabel := { world := l.world, time := freshTime }
      let newOrd := timeOrd.addFuture l.time freshTime
      let branch1 := [SignedFormula.pos event freshLabel]                  -- event witnessed
      let branch2 := [SignedFormula.pos guard freshLabel,
                       SignedFormula.pos (.untl guard event) freshLabel]   -- guard + until recurs
      ... auto-propagate T(Gψ)/F(Fψ)/F(U..) to freshTime ...
      (.branching [branch1 ++ autoProp, branch2 ++ autoProp], newOrd)
```

`sncePos` (Tableau.lean:732) mirrors via `addPast`. `untlNeg` (Tableau.lean:774) /
`snceNeg` (Tableau.lean:836) are the **persistent** Reynolds co-decomposition over
`timeOrd.futureOf`/`pastOf`, re-including the source on both branches, with a
`0 < timeCount < 4` gate to create a future time when none exists.

For temporal logic the box/diamond auto-propagation (`gProps`, `boxDiamondPersistence`,
modal cross-terms) is **dropped**; only G/H/F/P-universal propagation and U/S-negative
propagation along the `TimeOrdering` remain.

### 6. TimeOrdering (port the bimodal structure)

`Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean:684` — a standalone strict-
before constraint store, not embedded in worlds:

```lean
structure TimeOrdering where
  constraints : List (TimeIndex × TimeIndex)   -- (a,b) means a < b
```

API: `empty`, `addFuture t t_new` (adds `(t,t_new)`), `addPast t t_new` (adds `(t_new,t)`),
`futureOf t` (direct successors), `pastOf t` (direct predecessors), `timeCount`,
`ancestorTimes t fuel` (transitive closure with fuel). It stores **direct edges only** —
no transitive/dense closure; `branchTruth` for until/since is defined over the direct
successor/predecessor edges. The temporal version is essentially identical (it can drop the
`world` coordinate). **Decision point:** keep direct-successor semantics (simplest, matches
bimodal `branchTruth`) vs. add a transitive/dense closure (needed if completeness is to be
proven over genuine dense `DenselyOrdered` models — see Risks).

### 7. Density and discreteness frame-class rules

Two complementary encodings exist in the bimodal system; port both idioms.

**(a) Dynamic expansion rules** (`Tableau.lean`), gated by `decide (FrameClass.X ≤ fc)` in
`isApplicable` and assembled by `allRulesForFC fc` (`Tableau.lean:1054`):
- `denseIndicatorClosure` (Tableau.lean:897): `T(U(⊤,⊥))` closes the branch (since
  `¬U(⊤,⊥)` is a Dense axiom). Applicable only `fc ≥ .Dense`.
- `densityRule` (Tableau.lean:901): given `T(Gφ)@t` and a recorded future `t'`, insert a
  fresh intermediate `t''` with `t < t'' < t'` (`addFuture l.time t''` then
  `addFuture t'' t'`) and assert `T(φ)@t''`. This is the literal "between any two points
  there is another" rule. Applicable only `fc ≥ .Dense`.
- `priorUZ`/`priorSZ` (Tableau.lean:929): discrete "nearest point" —
  `T(Fφ) → T(U(φ,¬φ))`, `T(Pφ) → T(S(φ,¬φ))`. Applicable only `fc ≥ .Discrete`.
- `z1Rule` (Tableau.lean:948): discrete backward-induction — from `T(G(Gφ→φ))` and
  `T(F(Gφ))` derive `T(Gφ)`. Applicable only `fc ≥ .Discrete`.

**(b) Static axiom-negation closure** (`AxiomMatcher.lean` + `Closure.lean`): `matchAxiom`
is an ordered `<|>` chain over the axiom schemata; `checkAxiomNeg` closes on `F(axiom)`
when `witness.minFrameClass ≤ fc`. Density/discreteness patterns appear inline
(`density: GGφ → Gφ`, `dense_indicator`, `discrete_*`, `prior_UZ/SZ`, `z1`).

For temporal logic, idiom (a) is the primary mechanism (the temporal
`ProofSystem/Axioms.lean` already has `Axiom.density` and `minFrameClass`). Idiom (b) can
be a thinner matcher over just the temporal axioms.

### 8. Proof architecture — Soundness/Completeness template

The **Propositional Classical** tableau is the only fully-proved soundness in the repo and
is the template (`Cslib/Logics/Propositional/Tableau/Classical/`):

- **Soundness** (`Soundness.lean`, no `sorry`): `branchConsistent v b` →
  `branchSatisfiable`; per-rule rewrite lemmas; `classicalRule_preserves_sat`;
  `classically_closed_unsatisfiable`; loop invariant
  `classicalExpandBranches_closed_unsat` (fuel induction + inner `processNext` list
  induction); main `classicalTableau_sound : tableau = .closed → Tautology φ` by
  contrapositive.
- **Completeness** (`Completeness.lean`, **3 `sorry`s remain** in the loop→Hintikka bridge):
  `extractValuation`, `classicalHintikkaSet`, `classicalTruthLemma` (induction on φ),
  `classicalOpenBranch_countermodel`, main `classicalTableau_complete`.
- **DecisionProcedure** (`DecisionProcedure.lean`): `classicalTableau_decides : closed ↔
  Tautology`, `instDecidableTautology`.

The bimodal `CountermodelExtraction.lean` shows the **labeled** completeness pattern with
temporal modalities already handled: `SemanticCountermodel`, `branchTruth`,
`extractSemanticCountermodel`, the `sat_*` saturation-invariant family (each with a
`*_not_expanded` companion: `sat_untl_pos`/`untlPos_not_expanded`, `sat_untl_neg`,
`sat_someFuture_neg`, `sat_snce_pos`, …), `truthLemma_pos`/`truthLemma_neg`, and the
capstone `branchTruthLemma` (Tableau saturated + open ⇒ extracted model satisfies every
signed formula). **These `sat_*`/truth-lemma proof shapes are the exact templates for the
temporal until/since truth-lemma cases.**

Caveat: bimodal full tableau *completeness*/FMP theorems are **deferred** (only
`branchTruthLemma` is proven); modal `Soundness.lean` is largely `sorry`; propositional
`Completeness.lean` has 3 `sorry`s. The temporal proofs may rely on these only as
*statement/skeleton* templates, not as completed dependencies.

### 9. What must be reimplemented (temporal-specific, with no direct reuse)

- **`Hashable (Temporal.Formula Atom)`** instance (Modal supplies `instHashableModalProposition`;
  bimodal supplies `Formula.hashFormula`). Required by the `SignedFormula`/`Branch` deriving.
  `DecidableEq` is already derived on `Formula`.
- Temporal decomposition functions (`tempImpOf?`, `tempNegOf?`, `tempOrOf?`, `tempAndOf?`,
  `asUntil?`, `asSince?`, `asSomeFuture?`, `asSomePast?`, `asAllFuture?`, `asAllPast?`) —
  port the bimodal `as*?` family (Tableau.lean:197–286), dropping `asDiamond?`.
- The bespoke `untl`/`snce`/G/H/F/P rule cases in a `temporalApplyOne`.
- **Eventuality-defect closure + time-subset blocking** — the one genuinely new closure
  mode (Foundations `ClosureReason` does not model an unfulfilled `until` on a looping
  branch). Port the bimodal `Eventuality`/`EventualityTracker` (SignedFormula.lean:585–635),
  `Branch.timeType`/`isSubsetBlocked`/`isTemporallyBlocked`/`findBlockedTime`
  (SignedFormula.lean:645–784), and `subformula_property` (Saturation.lean:535) using the
  already-existing temporal `Subformulas` lemmas.
- Temporal model extraction (`extractModel` building a `TemporalModel`/`Satisfies` structure
  over recorded time points, not a flat `BoolValuation`).

## Recommendations

### Architecture

Build on the **Foundations generic kernel** (`F = Temporal.Formula Atom`, `L = Nat`),
imitate **Modal/Tableau** for label-introduction + worklist + Hintikka, **port the bimodal
algorithms** for until/since/TimeOrdering/frame-class rules, and follow **Propositional
Classical** for the proof skeleton. Reuse the existing temporal `FrameClass`,
`Subformulas`, `complexity`, and `Validity` hierarchy. **Do not** reuse the bimodal
`SignedFormula`/`Branch`/`RuleResult` types directly (they are typed over `Bimodal.Formula`
with a `box` constructor) — reuse the Foundations ones and port only the rule *bodies*.

### Phased breakdown aligned to the 8 files

1. **Defs.lean** (~250 ln) — instantiate Foundations kernel: `Hashable (Formula Atom)`
   instance, time-index label `L = Nat`, decomposition functions (`as*?` family ported,
   box/diamond dropped), fuel measure from `Formula.complexity`. *Low risk.*
2. **TimeOrdering.lean** (~150 ln) — port bimodal `TimeOrdering` (drop world coord):
   `empty/addFuture/addPast/futureOf/pastOf/timeCount/ancestorTimes` + basic lemmas.
   *Low risk.*
3. **Rules.lean** (~400 ln) — `temporalApplyOne : SignedFormula → Branch → TimeOrdering →
   RuleResult × TimeOrdering`. Propositional via `tryAllPropRules`; G/H/F/P universal
   (`persistent`) vs existential (`linear`); **until/since event-witness/guard-continue
   branching + Reynolds co-decomposition** (port `untlPos/untlNeg/sncePos/snceNeg`);
   frame-class rules (`denseIndicatorClosure`, `densityRule`, `priorUZ/SZ`, `z1Rule`) gated
   by `decide (FrameClass.X ≤ fc)`. *High risk — this is the core.*
4. **Branch.lean** (~250 ln) — temporal `Branch` collectors + `Eventuality`/
   `EventualityTracker` + `timeType`/`isSubsetBlocked`/`isTemporallyBlocked`/
   `findBlockedTime` (port from bimodal). *Medium risk.*
5. **Closure.lean** (~200 ln) — Foundations `ClassicalClosure` for `T(⊥)`/contradiction +
   **eventuality-defect closure** + `*_mono` monotonicity suite + `closed_extend_closed`,
   `add_neg_causes_closure`. *Medium risk (eventuality-defect is new).*
6. **Saturation.lean** (~350 ln) — `temporalApplyOne` worklist
   (`stepBranch`/`expandBranches`/`buildTableau`), fuel = `soundFuel φ`, time-subset
   blocking + eventuality fulfilment, `temporalHintikkaSet`, `subformula_property` (uses
   existing `Subformulas` lemmas), `expandBranch_sound`. *High risk — termination +
   blocking-soundness.*
7. **Soundness.lean** (~350 ln) — per-rule `*_preserves_sat` against `Satisfies`,
   `closed_unsat`, loop invariant by fuel induction, `temporalTableau_sound : closed →
   Valid(fc) φ`. Connect `FrameClass.Dense/Discrete` to `ValidDense/ValidDiscrete`.
   *High risk — until/since soundness, density/discreteness soundness.*
8. **Completeness.lean** (~400 ln) — `extractModel`, `temporalTruthLemma` (induction with
   until/since cases — port bimodal `sat_*`/`truthLemma` shapes), `openBranch_countermodel`,
   `temporalTableau_complete`, `temporalTableau_decides`, `Decidable` instance. *Highest
   risk — until eventuality fulfilment in the truth lemma; dense/discrete countermodel
   construction.*

### Riskiest proof obligations (flagged)

1. **Until/since completeness via eventuality fulfilment** (Completeness.lean): proving that
   an open *saturated, non-blocked* branch yields a real model where every positive `until`
   eventuality is genuinely satisfied (not just deferred forever). The bimodal system only
   proves `branchTruthLemma` with *direct-successor* `branchTruth` semantics and **defers**
   full FMP-completeness — task 301 cannot inherit a completed proof here. **This is the
   single highest risk.** If a sorry-free completeness proof over genuine `DenselyOrdered`/
   discrete models proves intractable in scope, recommend `[BLOCKED]` for user review and
   plan decomposition — **do not** defer with sorry or add axioms (zero-debt policy).
2. **Termination / blocking soundness** (Saturation.lean): the subformula-property +
   time-subset-blocking argument that guarantees the worklist terminates and that a blocked
   open branch is genuinely saturatable. Mitigated by existing `Subformulas` transitivity
   lemmas and the bimodal `expandBranchWithFuel_sound` template.
3. **Density/discreteness rule soundness** (Soundness.lean): `densityRule` must be sound
   over `DenselyOrdered D` (intermediate point exists); `priorUZ/SZ`/`z1Rule` sound over
   `SuccOrder/PredOrder/IsSuccArchimedean D`. The temporal `Validity` hierarchy supplies
   the right typeclasses, but each rule needs its own soundness lemma.
4. **Reynolds co-decomposition (`untlNeg`/`snceNeg`) correctness**: the persistent
   re-firing across recorded times without nontermination — the `timeCount`-gated
   future-creation needs a careful termination argument.

### Reusable lemmas/patterns inventory

**Reuse directly (Foundations `Cslib.Logic.Tableau`):** `Sign`, `SignedFormula F L`,
`Branch F L` (+ full API), `ClosureReason`, `ClosureCondition`/`ClassicalClosure`,
`RuleResult F L` (incl. `persistent`), `PropTableauRule`/`applyPropRule`/`tryAllPropRules`.

**Reuse directly (Temporal existing):** `FrameClass` (+ `LE`, `DecidableRel`,
`minFrameClass`), `Formula.complexity`, `Subformulas` API (`untl_left/right_mem`,
`snce_left/right_mem`, `subformulas_trans`, `self_mem_subformulas`), `Context`,
`TemporalModel`, `Satisfies` (+ `@[simp]` constructor lemmas), `Valid/ValidSerial/
ValidDense/ValidDiscrete`, `swapTemporal` + duality lemmas (useful to halve since-from-until
proofs).

**Port as templates (bimodal Decidability):** `TimeOrdering` (drop world coord);
`untlPos/untlNeg/sncePos/snceNeg` rule bodies; `as*?` decomposition family;
`Eventuality`/`EventualityTracker`; `timeType`/`isSubsetBlocked`/`isTemporallyBlocked`/
`findBlockedTime`; `subformula_property`; `denseIndicatorClosure`/`densityRule`/
`priorUZ`/`priorSZ`/`z1Rule`; `allRulesForFC` gating idiom; `matchAxiom` ordered-`<|>`
pattern; `SemanticCountermodel`/`branchTruth`/`extractSemanticCountermodel`;
`sat_*`/`*_not_expanded`/`truthLemma_pos`/`truthLemma_neg`/`branchTruthLemma` proof shapes;
`expandBranchWithFuel`(+`_sound`)/`saturateBlocked`/`buildTableau`.

**Imitate as structure (Modal/Tableau):** `Accessibility` → `TimeOrdering` threading;
`modalNextWorld`(+`_gt`) → fresh-time generator; `modalApplyOne` pair signature;
`modalStepBranch`/`modalExpandBranches`/`ModalTableauResult`/`modalFuel`;
`modalHintikkaSet`.

**Follow as proof skeleton (Propositional Classical):** `branchConsistent`/
`branchSatisfiable`, `*Rule_preserves_sat`, `*_closed_unsat`, `expandBranches_closed_unsat`
loop invariant, `extractValuation`/`Hintikka`/`truthLemma`/`openBranch_countermodel`,
`*_decides` + `Decidable` instance.

### Zero-debt compliance note

No approach recommended here requires `sorry` or new axioms. The bimodal system proves the
until/since rule *machinery* sorry-free; the deferred parts there are FMP-completeness
theorems. For task 301, if the full Completeness proof (risk #1) cannot be closed sorry-free
within scope, the correct action is `[BLOCKED]` + plan decomposition, **not** sorry deferral
or axiom introduction.

## References

- Burgess, J. (1984). Basic Tense Logic. (Burgess event/guard convention — matches repo.)
- Kamp, H. (1968). Tense Logic and the Theory of Linear Order. (cited in Formula.lean)
- Wolper, P. (1985). The tableau method for temporal logic. (until fixpoint unfolding)
- Reynolds, M. (until/since co-decomposition; cited in bimodal `untlNeg` docstring)
- Goré, R. (1999). Tableau Methods for Modal and Temporal Logics. (cited in bimodal Tableau.lean)
- Repo: `Cslib/Foundations/Logic/Tableau/*`, `Cslib/Logics/Modal/Tableau/*`,
  `Cslib/Logics/Propositional/Tableau/Classical/*`,
  `Cslib/Logics/Bimodal/Metalogic/Decidability/*`, `Cslib/Logics/Temporal/{Syntax,Semantics,ProofSystem}/*`.
