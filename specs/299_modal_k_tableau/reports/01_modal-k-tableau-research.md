# Research Report: Modal K Tableau Decision Procedure (Task 299)

**Task type:** cslib | **Session:** sess_1782335770_b2cbfa_299 | **Date:** 2026-06-24

## Executive Summary

CSLib already contains nearly all the reusable scaffolding needed for a modal-K
tableau, and the foundational layer was *explicitly designed* for this task
(`RuleResult.persistent` was added "from day one to support downstream modal and
temporal tableau tasks 299-301"). The recommended approach is:

1. **Reuse the fully label-generic Foundations layer** (`SignedFormula F L`,
   `Branch F L`, `RuleResult F L`, `ClosureCondition F L`, `applyPropRule`) with
   `F = Cslib.Logic.Modal.Proposition Atom` and `L = WorldIndex` (a `Nat`).
2. **Follow the 5-file architecture of the classical propositional tableau**
   (`Expansion`/`Soundness`/`Completeness`/`DecisionProcedure` + barrel), which is
   the canonical CSLib tableau template.
3. **Borrow the modal-rule and countermodel-extraction mechanics from the proven
   Bimodal tableau** (`Cslib/Logics/Bimodal/Metalogic/Decidability/`), which is
   **sorry-free** and already implements world labels, fresh-world generation,
   box/diamond rules, and Kripke countermodel extraction — but adapt the box rule
   from S5 ("propagate to all worlds") to K ("propagate only to R-accessible worlds").

**Top risk:** The classical `Completeness.lean` loop-invariant
(`classicalExpandBranches_hintikka`) is left as `sorry` (3 sorries), and the
intuitionistic labeled tableau — the closest propositional analogue with `L = Nat`
world labels — has `sorry` in *both* soundness and completeness, including the
fresh-world-disjointness lemmas. The modal completeness loop invariant is the single
riskiest deliverable and must be budgeted as a dedicated phase. Per zero-debt policy,
if the loop invariant cannot be closed, the task should be decomposed or marked
`[BLOCKED]`, **never** shipped with `sorry`.

## Namespace / Type Facts (verified)

- Modal namespace is **`Cslib.Logic.Modal`** (singular "Logic"), NOT `Cslib.Logics.Modal`.
  Files live under directory `Cslib/Logics/Modal/`.
- The modal formula type is **`Proposition Atom`**, NOT `Formula`. The task description's
  "`Cslib.Logic.Modal.Formula`" is inaccurate; the actual type is
  `Cslib.Logic.Modal.Proposition` with constructors `atom | bot | imp | box`
  (`deriving DecidableEq, BEq`). File: `Cslib/Logics/Modal/Basic.lean:70`.
- and/or/neg/diamond are **derived abbrevs** (Lukasiewicz encoding), not constructors:
  - `neg φ := imp φ bot`
  - `or φ ψ := imp (imp φ bot) ψ`
  - `and φ ψ := imp (imp φ (imp ψ bot)) bot`
  - `diamond φ := neg (box (neg φ)) = imp (box (imp φ bot)) bot`
- Kripke model: `structure Model (World Atom) where r : World → World → Prop; v : World → Atom → Prop`
  (`Cslib/Logics/Modal/Basic.lean:63`).
- Satisfaction: `Satisfies m w φ` with `box φ => ∀ w', m.r w w' → Satisfies m w' φ`
  (`Basic.lean:145`). Diamond characterization `Satisfies.diamond_iff`:
  `Satisfies m w (◇φ) ↔ ∃ w', m.r w w' ∧ Satisfies m w' φ` (`Basic.lean:156`).
- **K validity is over ALL models** (no frame conditions). The K completeness file
  states weak completeness as `∀ World (m : Model World Atom) w, Satisfies ...`
  (`Systems/K/Completeness.lean:367-382`). This is the *simplest* soundness target —
  no `Std.Refl`/`Serial`/etc. typeclass constraints.

## Reusable Infrastructure (Reuse-First Findings)

### Foundations/Logic/Tableau/ — FULLY GENERIC, reuse directly

Namespace `Cslib.Logic.Tableau`. All types are generic over formula `F` and label `L`;
**nothing is tied to a specific formula type.** The only constraints used anywhere are
`BEq F`, `BEq L`, `Hashable`, `DecidableEq`, `HasBot F`.

| Type / def | Signature | Reuse for K |
|---|---|---|
| `SignedFormula F L` | `{ sign : Sign, formula : F, label : L }` deriving `DecidableEq, Hashable` | `F = Proposition Atom`, `L = WorldIndex` |
| `Branch F L` | `abbrev := List (SignedFormula F L)`; ops `extend`, `extendMany`, `findContradiction`, `hasContradiction`, `hasBotPos`, `labels`, `formulasAt`, `hasPosAt`/`hasNegAt` | direct |
| `RuleResult F L` | `linear` / `branching` / `persistent` / `notApplicable` | **`persistent` is the box-rule mechanism** |
| `applyPropRule` / `tryAllPropRules` | generic over `andOf? orOf? impOf? negOf? : F → Option ...` | direct — supply Lukasiewicz decomposition fns |
| `ClosureCondition F L` | class with `findClosure : Branch F L → Option (ClosureReason F L)`; `isClosed`/`isOpen` | reuse `ClassicalClosure` instance directly (K closes on T(⊥) or T(φ)/F(φ) at same label) |
| `ClosureReason F L` | `botPos l` / `contradiction phi l` | direct |
| `Sign` | `pos | neg`, `flip`, `isPos`, `isNeg` | direct |

**Files:** `Cslib/Foundations/Logic/Tableau/{Sign,SignedFormula,Branch,RuleResult,
PropositionalRules,Closure,ClosureCondition}.lean`.

### Classical propositional tableau — THE ARCHITECTURE TEMPLATE

Namespace `Cslib.Logic.PL`. Files in `Cslib/Logics/Propositional/Tableau/Classical/`.
Instantiates `F = Proposition Atom`, `L = Unit`. Sizes: Expansion 165, Soundness 639,
Completeness 509, DecisionProcedure 94 lines (total ~1,400 with no labels).

Key reusable patterns (copy structure, change `L = Unit` → `WorldIndex`):

- **Result type** `inductive ClassicalTableauResult := closed | openBranch (Branch ...)`.
- **`classicalApplyOne sf := tryAllPropRules propAndOf? propOrOf? propImpOf? propNegOf? sf`**
  — for K, extend with box/diamond cases.
- **Fuel-based saturation loop** `classicalExpandBranches (branches) (expandedSets) (fuel)`
  with nested `processNext` worklist; maintains the invariant
  `expandedSets.length = branches.length`. `expanded` list prevents re-expansion.
- **Entry point** `classicalTableau φ := expandBranches [[F(φ)]] [[]] fuel`, with
  `fuel := 4 * (φ.complexity + 1) + 1`. Starts from `F(φ)` (refute φ).
- **Soundness** (`Soundness.lean`, verified **sorry-free** in the actual proof body):
  `theorem classicalTableau_sound (φ) (h : classicalTableau φ = .closed) : Tautology φ`.
  Strategy: invariant "branch satisfiability preserved by every rule + closed branches
  unsatisfiable", via `classicalRule_preserves_sat` and `classically_closed_unsatisfiable`,
  lifted by fuel-induction lemma `classicalExpandBranches_closed_unsat` (induction on fuel,
  inner induction on pending worklist). Contrapositive main theorem.
- **Completeness** (`Completeness.lean`) — the countermodel-extraction pattern:
  - `extractValuation b := fun p => b.any (T(atom p) on b)` (read valuation off branch).
  - `classicalHintikkaSet b` — downward-saturation predicate: open AND every rule's
    outputs already present (for branching, at least one sub-branch's outputs present).
  - `classicalTruthLemma` (induction on φ, **sorry-free**): branch sign of φ ⇒ evaluation.
  - `classicalOpenBranch_countermodel` + `classicalTableau_complete` (contrapositive).
  - **3 SORRIES** at `Completeness.lean:462,470,486`: `classicalExpandBranches_hintikka`
    (loop invariant: returned open branch is a Hintikka set), `classicalTableau_hintikka`,
    and the `F(φ) ∈ b` membership step. Two complete helpers exist:
    `mem_extendMany_of_mem`, `hintikka_inv_mono`.
- **DecisionProcedure**: `classicalTableau_decides : classicalTableau φ = .closed ↔ Tautology φ`
  and a `Decidable` instance via `isTrue`/`isFalse` (requires only `DecidableEq + Hashable`,
  no `Fintype Atom`).

Recurring Mathlib lemmas to expect: `List.any_eq_true(.mp/.mpr)`, `List.mem_cons`,
`List.mem_append`, `List.mem_map`, `List.findSome?_*`, `Bool.and_eq_true`,
`Bool.or_eq_true`, `eq_of_beq`, fuel `induction ... with | zero | succ`, `omega` for
length bookkeeping, `by_contra` + `push Not`.

### Bimodal tableau — THE PROVEN MODAL-MECHANICS TEMPLATE (sorry-free)

Directory `Cslib/Logics/Bimodal/Metalogic/Decidability/`. **Zero sorries.** This is the
strongest reference for world labels, fresh-world generation, modal rules, and Kripke
countermodel extraction. CAVEAT: it defines its OWN `Sign`/`SignedFormula`/`Branch`
(predates the Foundations layer) and its modal logic is **S5** (all worlds mutually
accessible), so its box rule "propagate T(box A) to ALL known worlds" — **this is NOT K**.

Verified facts:
- `abbrev WorldIndex := Nat`; `structure Label := { world : WorldIndex, time : TimeIndex }`;
  `Label.initial := {world := 0, time := 0}`. For K, drop `time` → `Label = WorldIndex`.
- Fresh world generation: `branch.nextWorld` (= `maxWorld + 1`); `knownWorlds`, `maxWorld`.
- Modal rule enumeration `TableauRule` includes `boxPos` (T(□A): persistent, propagate to
  worlds), `boxNeg` (F(□A): fresh witness world with F(A)), `diamondPos` (T(◇A): fresh
  witness world with T(A)), `diamondNeg` (F(◇A): persistent, propagate F(A) to worlds).
  `RuleResult` has the same 4 cases as Foundations (`linear`/`branching`/`persistent`/
  `notApplicable`); box-pos uses `.persistent` so it re-fires when new worlds appear.
- **The exact K-accessibility template already exists as `TimeOrdering`**
  (`SignedFormula.lean:684`): `structure TimeOrdering := { constraints : List (TimeIndex ×
  TimeIndex) }` with `addFuture`/`addPast`/`futureOf`/`pastOf`. This is a `List (Nat × Nat)`
  edge set threaded as a separate accumulating parameter through `applyRule`/`expandOnce`/
  `expandBranchWithFuel`. For K: introduce `Accessibility := { edges : List (WorldIndex ×
  WorldIndex) }`, add edge `(w, fresh)` on diamond/box-neg expansion, and propagate box-pos
  to `successorsOf w` instead of `knownWorlds`.
- Countermodel extraction (`CountermodelExtraction.lean`):
  `structure SemanticCountermodel` (fields: worlds, times, timeOrdering, atomValuation),
  `buildAtomValuation b : WorldIndex → TimeIndex → Atom → Bool` (= `b.hasPosAt (.atom p) ⟨w,t⟩`),
  `extractSemanticCountermodel φ b ord`, `branchTruth` (recursive eval), plus per-rule
  satisfaction invariants `sat_box_pos`, `sat_box_neg`, `sat_imp_neg`,
  `valuation_reflects_pos/neg`, and the `*_not_expanded` idiom proving formulas cannot
  survive saturation.
- **`branchTruth`'s `box` clause is `∀ w' ∈ cm.worlds` (S5 total relation)** — but its
  `untl` clause is ALREADY `∃ t' ∈ timeOrdering.futureOf t, ...` (relational style). So K's
  box clause `∀ w' ∈ accessibility.successorsOf w, ...` is a one-line restyle mirroring the
  existing temporal clause. The truth lemma `branchTruthLemma` is proved sorry-free by two
  mutual structural inductions (`truthLemma_pos`/`truthLemma_neg`).
- **CRITICAL GAP in bimodal: there is NO top-level constructive completeness theorem.**
  `Correctness.lean:35-40` defers FMP completeness to "Task 43"; only `branchTruthLemma`
  (open saturated branch ⇒ model satisfying all its signed formulas) exists. Soundness
  there is proof-system soundness (`decide_sound`), with tableau-level
  `expandBranchWithFuel_sound` (`Saturation.lean:649`, strong induction on fuel).
  **Task 299 must write the open-branch ⇒ ¬⊨φ wrapper itself** — the truth lemma is given,
  the packaging is not.
- Termination: `termination_by fuel`; fuel bound `soundFuel φ = n·2^n` capped (FMP-derived,
  `n = subformulaCount`); proportional fuel split on branching; `AppliedSet` (HashSet) stops
  persistent rules re-firing; temporal subset blocking (`findBlockedTime`/`timeType`/
  `isSubsetBlocked`) — **for K, retarget subset blocking from times to WORLDS** (loop-check:
  a fresh world whose formula-set ⊆ an ancestor's is blocked → finite model property).
- Saturation/termination, correctness files are all sorry-free.

## The K-Specific Design (what must be NEW)

These are the genuinely new pieces task 299 must author (no existing reuse):

1. **Modal subformula / complexity measure.** Modal `Proposition` has NO Subformula
   or complexity module (`Cslib/Logics/Propositional/Subformula.lean` is `PL`-specific).
   Need `Modal.Proposition.complexity` (mirror the prop version; `box` adds 1) for the
   fuel bound. For K, fuel must also account for world creation — diamond rules create
   new worlds, so the fuel measure is more subtle than the propositional `4*(complexity+1)`.
2. **Lukasiewicz decomposition functions** for the modal `Proposition`. Because and/or/neg
   are encoded via `imp`/`bot`, the `andOf?`/`orOf?`/`negOf?` passed to `applyPropRule`
   must pattern-match the encoded shapes:
   - `negOf? (imp a bot) = some a`
   - `orOf? (imp (imp a bot) b) = some (a, b)`
   - `andOf? (imp (imp a (imp b bot)) bot) = some (a, b)`
   - `impOf?` must EXCLUDE the encoded neg/or/and shapes to avoid mis-decomposition
     (ordering of matches matters — this is the trickiest definitional point; cf. the
     `propImpOf?` neg-exclusion in `Propositional/Tableau/Defs.lean`).
   - `boxOf? (box a) = some a`; diamond is `neg (box (neg a))` so `diaOf?` matches
     `imp (box (imp a bot)) bot`.
   None of these exist yet (verified: no `andOf?`/`boxOf?`/`diaOf?` in Modal or Bimodal).
3. **K accessibility tracking.** Unlike S5, K must record the accessibility *edges* between
   worlds. Recommended: track edges implicitly via fresh-world provenance — when
   `diamondPos`/`boxNeg` at world `w` creates fresh world `w'`, record edge `w → w'`.
   Box-positive `T(□A)` at `w` then propagates `T(A)` to exactly the `w'` with `w → w'`
   (the persistent variant must be scoped to accessible worlds, not all worlds). Options:
   (a) carry a separate edge list alongside the branch, or (b) encode edges as a
   distinguished signed-formula form. Option (a) is cleaner and matches the
   `SemanticCountermodel` extraction (build `r` from the edge list).
4. **K modal rules** (the fundamental pattern from the task description):
   - `boxPos` T(□φ) at `w`: for every accessible `w'` (edge `w→w'`), add T(φ) at `w'`.
     Universal/persistent — must re-fire when new accessible worlds appear later.
   - `diamondPos` T(◇φ) = T(¬□¬φ) at `w`: create fresh `w'`, edge `w→w'`, add T(φ) at `w'`
     (and re-apply all box-positives of `w` to `w'`). Existential.
   - `boxNeg` F(□φ) at `w`: create fresh `w'`, edge `w→w'`, add F(φ) at `w'`. Existential
     (since `F(□φ)` means some accessible world fails φ).
   - `diamondNeg` F(◇φ) at `w`: universal `F(φ)` at every accessible `w'`.
   The interaction "boxPos must re-fire whenever a new accessible world is created" is the
   core complication; the bimodal S5 code handles this via "auto-propagate universals" on
   world creation — borrow that machinery but scope to the edge relation.
5. **K countermodel extraction → `Model World Atom`.** From an open saturated branch:
   - `World := WorldIndex` (the labels appearing on the branch).
   - `r w w' := edge (w, w')` is recorded (the accessibility list).
   - `v w p := T(atom p) at w on branch` (mirror `buildAtomValuation`).
   Then a modal truth lemma by induction on φ (box case uses Hintikka saturation:
   every accessible world has the propagated T(φ); diamond case uses the witness world).
   Connect to `Satisfies.box_iff_forall` / `Satisfies.diamond_iff_exists` (`Basic.lean`).
6. **K-specific `ClosureCondition`.** The existing `ClassicalClosure` instance already
   gives the right K closure (T(⊥) or T(φ)/F(φ) at same label) — reuse directly, no new
   instance needed.

## Soundness / Completeness Proof Strategy

- **Soundness** (target: ALL models, simplest case). Mirror classical
  `classicalTableau_sound`: define `branchSatisfiable b := ∃ (m : Model W Atom) (assignment
  of labels→worlds), branch consistent`. Each rule preserves satisfiability:
  - prop rules: as classical (via the `Satisfies.and_iff`/`or_iff`/`impl_iff` lemmas in
    `Basic.lean` — all `@[scoped grind =]`, very usable).
  - boxPos: if `Satisfies m w (□φ)` and `w→w'`, then `Satisfies m w' φ` — direct from
    `Satisfies.box_iff_forall`.
  - diamondPos: `Satisfies m w (◇φ)` gives a witness world via `Satisfies.diamond_iff_exists`
    — extend the label→world assignment to the fresh label.
  - Closed branches unsatisfiable (reuse `ClassicalClosure` reasoning).
  Lift via fuel induction (same shape as `classicalExpandBranches_closed_unsat`).
- **Completeness** (the hard part). Build the countermodel from an open saturated branch and
  prove a modal truth lemma. The classical truth-lemma induction is sorry-free and is the
  template; the box/diamond cases are new and use Hintikka saturation + the edge relation.
  **The loop invariant `expandBranches_hintikka` is the documented sorry in the classical
  template and will be at least as hard here** because world creation interleaves with
  expansion. Budget a dedicated phase; consider proving a stronger structural invariant up
  front (saturation + edge-closure of box-positives).

## File Plan (matches task's requested layout, adjusted to CSLib conventions)

Under `Cslib/Logics/Modal/Tableau/` (namespace `Cslib.Logic.Modal.Tableau` or reuse
`Cslib.Logic.Modal`):

- `Defs.lean` — `WorldIndex`, modal `Proposition.complexity`, Lukasiewicz decomposition
  fns (`andOf?`/`orOf?`/`impOf?`/`negOf?`/`boxOf?`/`diaOf?`), `Hashable (Proposition Atom)`
  instance (mirror `instHashableProposition`), reduction `@[simp]` lemmas.
- `Rules.lean` — modal rule enum + `modalApplyOne` (prop rules via `tryAllPropRules` +
  box/diamond cases producing `linear`/`branching`/`persistent` `RuleResult`s + edge
  creation).
- `Branch.lean` — K-specific branch helpers: edge list, `nextWorld`/`knownWorlds`,
  accessible-worlds query, box-propagation helper. (Reuse Foundations `Branch` as the base.)
- `Closure.lean` — re-export/instantiate `ClassicalClosure` for the modal types
  (likely thin; closure is reused).
- `Saturation.lean` — fuel-based `modalExpandBranches`/`stepBranch`/`processNext`,
  `ModalTableauResult`, entry `modalTableau φ`, Hintikka predicate.
- `Soundness.lean` — `modalTableau_sound`.
- `Completeness.lean` — `extractModel`, modal truth lemma, `modalTableau_complete`,
  and (recommended additional) a `DecisionProcedure`-style iff + `Decidable` instance.

Estimate of 1,500-2,000 lines is realistic; the completeness loop invariant is the dominant
cost and the dominant risk.

## Risks & Zero-Debt Compliance

1. **Completeness loop invariant (HIGH).** Unproven in the classical template; harder here.
   Mitigation: dedicate a phase; if unclosable, decompose (e.g., split out the invariant as
   its own task) or mark `[BLOCKED]`. **Do NOT ship with `sorry` or axioms.**
2. **Termination / fuel bound (MEDIUM).** Diamond rules create worlds; naive fuel may be
   insufficient or non-terminating. K does have the finite-model property; the fuel bound
   must reflect the subformula-closure × world bound (worlds ≤ number of distinct
   `◇`/`F(□)` subformula occurrences). Reference Gore (1999) tableau termination (cited in
   the Bimodal file) for the K bound.
3. **Lukasiewicz decomposition ordering (MEDIUM).** `impOf?` vs `negOf?`/`orOf?`/`andOf?`
   match-ordering is subtle and a source of definitional bugs; write `@[simp]` reduction
   lemmas and test each shape.
4. **S5 vs K box rule (MEDIUM).** Do not copy the Bimodal "propagate to all worlds" box
   rule — it is unsound for K. Scope propagation to the recorded accessibility relation.
5. **Namespace/type mismatch in task description (LOW).** Task says
   `Cslib.Logic.Modal.Formula`; actual is `Cslib.Logic.Modal.Proposition`. Plan accordingly.

## Reuse Check Conclusion

- Foundations tableau layer: **REUSE WHOLESALE** (designed for this task).
- Classical tableau: **REUSE ARCHITECTURE** (5-file split, fuel loop, truth-lemma pattern).
- Bimodal tableau: **REUSE MECHANICS** (world labels, fresh-world gen, countermodel
  extraction shape) but **adapt box rule S5→K**.
- Modal semantics (`Model`, `Satisfies`, `box_iff_forall`, `diamond_iff_exists`, all the
  `@[scoped grind]` characterization lemmas): **REUSE DIRECTLY** for soundness/completeness.
- New work: modal complexity, Lukasiewicz decomposition fns, K accessibility tracking, K
  box/diamond rules, K countermodel `extractModel` + modal truth lemma.

## Key File References (absolute)

- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Basic.lean` (Model, Proposition, Satisfies, char lemmas)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` (K validity = all models; canonical-model completeness for reference)
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Tableau/{Sign,SignedFormula,Branch,RuleResult,PropositionalRules,Closure,ClosureCondition}.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Classical/{Expansion,Soundness,Completeness,DecisionProcedure}.lean` (+ `Defs.lean` for decomposition pattern)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Subformula.lean` (complexity template)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Decidability/{SignedFormula,Tableau,Saturation,Closure,DecisionProcedure,CountermodelExtraction,Correctness}.lean` (proven modal mechanics)
