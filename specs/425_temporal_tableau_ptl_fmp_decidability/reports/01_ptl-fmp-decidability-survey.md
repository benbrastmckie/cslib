# Research Report: PTL Finite Model Property and Temporal Tableau Decidability

**Task:** Establish the finite model property (FMP) for Propositional Temporal Logic (PTL) and
use it to discharge `temporalTruthLemma_untl` / `temporalTruthLemma_snce` (Until/Since eventuality
fulfilment), unblocking `eventualityDefect_unsat`, `temporalTableau_sound`, `openBranch_branchSat`,
`temporalTableau_complete`, and the final `instDecidableValid` in
`Cslib/Logics/Temporal/Tableau/`.

**Status:** Researched. No sorries or axioms exist in the target directory today — the target
lemmas *do not yet exist as declarations*; they are described as remaining work in module
docstrings. This is genuine new formalization, not a sorry-discharge. There is **no theoretical
blocker** (PTL FMP is a classical result), so this task must be **planned and implemented**, not
marked `[BLOCKED]`. It is, however, a large multi-phase effort gated on one critical design
decision (see §4).

---

## 1. Executive Summary

- The temporal tableau (`Cslib/Logics/Temporal/Tableau/`) is a **linear-time, bidirectional
  (Until *and* Since), ℤ-indexed** decision procedure. Its termination relies on **time-subset
  blocking** (loop detection) plus an **`EventualityTracker`** of pending Until/Since obligations.
- All eight named targets in the task are **absent declarations**, referenced only in comments.
  The Tableau directory currently has **0 real `sorry`** (the three grep hits in `Completeness.lean`
  are the string "sorry-free" in prose).
- The "FMP" required here is **not** the canonical-model filtration FMP used by Bimodal/Minimal
  (task 421). It is the **tableau-internal ultimately-periodic (lasso) model construction**:
  unfold the subset-blocked loop periodically across ℤ so that every Until/Since eventuality on an
  open branch is fulfilled within one period.
- **Critical design finding (§4):** the *existing* `extractModelℤ` definition is **insufficient**
  for the Until/Since truth lemmas. It leaves every ℤ-instant not touched by the finite branch
  **empty** (all atoms false), so the guard of an `U(guard,event)` cannot be shown to hold across
  the infinitely many intermediate instants. The countermodel must be **redesigned** as a periodic
  model before `temporalTruthLemma_untl/snce` are even true of it. This is the crux and the single
  highest-risk item.
- **Reuse-first assessment (§5):** the literal Bimodal/Minimal FMP infrastructure and the LTL
  ω-automata route are **not directly reusable** (different route / different time model). What
  *is* reusable: the task-421 *pattern* (a `noncomputable` `Decidable` via a finite-model bridge),
  the already-landed sorry-free run-level `temporalTableau_instantStrict`, the propositional truth
  lemma (`temporalTruthLemma_propositional_aux`), the subset-blocking/`EventualityTracker`
  machinery, and — as an *argument template only* — the sorry-free Chronicle eventuality-resolution
  lemmas (`tUntilEventualityResolution` / `tSinceEventualityResolution`).

---

## 2. Target Lemmas and Current State

All target names below are **not yet declared**; they appear only in the "Blocked Obligations" /
"Remaining Work" docstrings of `Soundness.lean` and `Completeness.lean`.

| Target | File (intended) | Role | Blocks |
|--------|-----------------|------|--------|
| `eventualityDefect_unsat` | `Tableau/Soundness.lean` (§ BlockedObligations, ~L189 as a comment-stated signature) | Soundness: a branch closed by eventuality-defect is unsatisfiable | `temporalTableau_sound` |
| `temporalTruthLemma_untl` | `Tableau/Completeness.lean` | Completeness: `T(U(g,e))@t` on open branch → satisfied in countermodel | `openBranch_branchSat` |
| `temporalTruthLemma_snce` | `Tableau/Completeness.lean` | Symmetric Since case | `openBranch_branchSat` |
| `openBranch_branchSat` | `Tableau/Completeness.lean` | Open saturated branch → `branchSat b ord` | `temporalTableau_complete` |
| `temporalTableau_sound` | `Tableau/Soundness.lean` | `.closed` result → `¬ satisfiable` | `instDecidableValid` |
| `temporalTableau_complete` | `Tableau/Completeness.lean` | `.openBranch` result → `satisfiable` | `instDecidableValid` |
| `instDecidableValid` | `Tableau/Completeness.lean` (or a new `DecisionProcedure.lean`) | `Decidable (Temporal.valid φ)` | task 301 |

**Already landed (sorry-free, verified) and reusable as-is:**

- `temporalTableau` (`Saturation.lean:534`) — the top-level decision function returning
  `TemporalTableauResult` (`.closed` | `.openBranch b ord`).
- `temporalTableau_instantStrict` (`Saturation.lean:545`) — run-level `InstantStrict ord` for any
  returned open branch. The task description's "run-level `InstantStrict` proof" blocker is
  **already discharged**; only the FMP truth-lemma component of `openBranch_branchSat` remains.
- `classicallyClosed_unsat` (`Soundness.lean:97`) — the classical (non-eventuality) half of
  soundness. `temporalTableau_sound` needs only the eventuality-defect half glued on.
- The propositional fragment of the truth lemma:
  `temporalTruthLemma_propositional_aux` / `temporalTruthLemma_propositional`
  (`Completeness.lean:425`, `:946`) — atom/bot/imp cases by strong induction on
  `Formula.complexity`, plus all `extractModel` / `extractModelℤ` atom/bot property lemmas.

**Semantics of the eventualities** (`Semantics/Satisfies.lean:61-115`, Pnueli convention, guard
is the FIRST argument, event is the SECOND):

- `U(ψ,φ)` at `t`: `∃ s > t, φ(s) ∧ ∀ r ∈ (t,s), ψ(r)`  (ψ = guard, φ = event).
- `S(ψ,φ)` at `t`: `∃ s < t, φ(s) ∧ ∀ r ∈ (s,t), ψ(r)`.
- Characterization lemmas `untl_iff` / `snce_iff` exist and are the entry points for the truth
  lemma proofs.

---

## 3. What the PTL FMP Actually Requires Here

The tableau builds a **finite** open branch `b` (finite because subset-blocking caps the number of
distinct "time types" at `2^n`, `n = subformulaCount φ`; see `temporalFuel`, `Saturation.lean:76`).
The countermodel domain is **ℤ** with `f = ord.instant : TimeIndex → ℤ` (`extractModelℤ`,
`Completeness.lean:133`). Order-preservation `f t < f t'` is guaranteed by
`TimeOrdering.InstantStrict` (`temporalTableau_instantStrict`, already proved).

The FMP content is the **eventuality-fulfilment ↔ loop-unfolding equivalence**:

- **Completeness direction (`_untl` / `_snce`):** On an *open* branch, `isTemporalClosed` is false,
  so `findEventualityDefect` returned `none` — meaning **no** subset-blocked time carries an
  unfulfilled pending eventuality (see `isTemporallyBlocked` / `allEventualitiesFulfilledOrDuplicated`,
  `Branch.lean:146-167`). Therefore every `T(U(g,e))@t` on the branch is *fulfilled*: either the
  witness `T(e)@t'` literally appears at some `ord`-future `t'` (via `fulfillEventualities`,
  `Saturation.lean:108`), or it is "duplicated at the blocking ancestor," i.e. it recurs in the loop.
  The truth lemma must turn *fulfilment-or-recurrence* into an actual satisfying instant in the
  ℤ-model — which forces the periodic-unfolding construction (§4).

- **Soundness direction (`eventualityDefect_unsat`):** A branch closed by eventuality-defect is
  subset-blocked at some `t` with a pending eventuality that recurs but is never witnessed. The
  argument (pumping / König-style): if such a branch *were* satisfiable in some linear model, the
  loop segment could be pumped so the guard holds forever and the event never occurs, contradicting
  the semantics of `U`. Concretely: `U(g,e)` true at `t` forces a *least* witness instant, but the
  subset-blocked loop with no witness means the guard-only pattern repeats unboundedly — no least
  witness exists — contradiction. This is a finite, self-contained argument over the (finite) loop
  structure; it does **not** require constructing the full ℤ model, only reasoning about any
  hypothetical model of the branch.

**Design guidance for the plan:** implement `eventualityDefect_unsat` (soundness) **first**. It is
the smaller and lower-risk half (no model redesign; it reasons *about* an arbitrary model rather than
*building* one), and it independently unblocks `temporalTableau_sound` → the `.closed` half of
`instDecidableValid`.

---

## 4. CRITICAL DESIGN FINDING — `extractModelℤ` Must Be Redesigned

`extractModelℤ` (`Completeness.lean:133-135`) defines the valuation as:

```
valuation z p := b.any fun sf => sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p
```

This makes atom `p` true at instant `z` **iff** some branch time maps to `z` and carries
`T(atom p)`. Because the branch is finite, only finitely many `z ∈ ℤ` are populated; at **all other
instants every atom is false** and no signed formula is present.

Consequence: for `T(U(guard,event))@t` with witness `T(event)@t'` and `ord.instant t < ord.instant t'`,
the semantic obligation `∀ r ∈ (ord.instant t, ord.instant t'), guard(r)` ranges over **every**
integer strictly between the two instants — including the (generally many) integers that are *not*
the image of any branch time, where `guard` (an arbitrary formula) is not forced true. **The current
model does not satisfy the Until in general**, so `temporalTruthLemma_untl` is *false of the model as
defined*. This is why the task is genuinely hard: it is a model-construction task, not a lemma-only
task.

**Required redesign (recommended):** replace the "island" ℤ-model with an **ultimately-periodic
(lasso) ℤ-model** built from the branch's subset-block structure:

1. Extract the **loop**: the subset-blocked ancestor pair `(t_anc, t_new)` identified by
   `isSubsetBlocked` gives a repeating time-type segment. The prefix `[min .. t_anc]` and the loop
   body `(t_anc .. t_new]` define a lasso.
2. Define the ℤ valuation by **periodic extension**: for `z` beyond the populated range, reduce
   `z` modulo the loop length back into the loop body and read the time-type there (forward for the
   future tail, and — because BX is bidirectional — a symmetric backward loop for the past tail).
   Instants *interior* to the populated prefix keep their branch time-type.
3. Prove the truth lemma over this periodic model by induction on `Formula.complexity`, reusing the
   propositional cases verbatim and adding the untl/snce cases. The guard-between obligation now
   holds because every intermediate instant carries a *complete* time-type (a Hintikka set) in which
   the guard is present whenever the Until has not yet been discharged.

**Alternative (higher risk, discouraged):** keep `D = ℤ` but restrict the model to the finite
populated window and quotient to a **finite** cyclic order `ZMod k` (a `Fintype` domain), then embed.
This is closer to the task-421 "finite `Fintype` domain" shape but conflicts with the existing
`branchSat` interface which fixes `D` as an arbitrary `LinearOrder`/`Nontrivial` type and with
`InstantStrict`'s ℤ-valued `instant`. The periodic-ℤ route (above) preserves all existing landed
infrastructure and is the lower-risk path.

**Plan implication:** the redesign of `extractModelℤ` (and re-proving the already-landed
`extractModelℤ_*` property lemmas against the new definition) is a **prerequisite phase** before any
untl/snce truth-lemma phase. Budget for touching `Completeness.lean:133-330`.

---

## 5. Reuse-First Assessment (CSLib philosophy)

Ran the Reuse Check Protocol against Foundations, sibling Logics, and the cited task-421 work.

### 5a. Directly reusable (keep / call)

- **Run-level order structure:** `temporalTableau_instantStrict`, `TimeOrdering.InstantStrict`,
  `temporalStepBranch_preserves`, `OrdFreshWRT` — all sorry-free (`Saturation.lean`,
  `TimeOrdering.lean`). These fully discharge the order-preservation component of
  `openBranch_branchSat`.
- **Classical soundness half:** `classicallyClosed_unsat` (`Soundness.lean:97`).
- **Propositional truth lemma + model property lemmas:** `temporalTruthLemma_propositional_aux`,
  `extractModel_atom_sat_iff`, `extractModel_bot_false`, `openBranch_noBotPos`,
  `openBranch_noContradiction`, `extractModel_atom_neg_notSat` and their ℤ analogues
  (`Completeness.lean:99-330`). Note: the ℤ ones will need re-proof after the §4 redesign, but the
  `Nat`-model (`extractModel`) versions and the proof *structure* transfer directly.
- **Loop/eventuality machinery:** `EventualityTracker`, `Eventuality`, `registerEventualities`,
  `fulfillEventualities`, `isSubsetBlocked`, `timeType`, `ancestorTimes`,
  `allEventualitiesFulfilledOrDuplicated`, `isTemporallyBlocked`, `findBlockedTime`,
  `findEventualityDefect`, `isTemporalClosed`, `temporalHintikkaSet` (`Branch.lean`, `Closure.lean`,
  `Saturation.lean`). These *are* the FMP scaffolding; the new lemmas consume them.

### 5b. Reusable as an argument template only (do NOT import — different structure)

- **Chronicle eventuality resolution:** `tUntilEventualityResolution` / `tSinceEventualityResolution`
  (`Metalogic/Chronicle/Frame.lean:234-252`, sorry-free). These resolve Until/Since in the
  **canonical MCS chain** (`TPoint`), not on a tableau branch, so they are not callable in the
  tableau setting — but they encode the exact "eventuality → forward/backward witness" argument the
  tableau truth lemma re-runs over signed formulas. Mirror their shape.
- **Task-421 pattern:** `MinDecidability.lean` builds a `noncomputable def
  decidableDerivableMinPropAxiomFMP` from a finite canonical Kripke model
  (`MinFinWorld φ` embeds into `φ.subformulas.powerset`, `Fintype.ofInjective`) plus a
  `min_fin_truth_lemma` and the `min_fmp` biconditional. The *reusable pattern* is: finite model
  → truth lemma → FMP biconditional → `Decidable` via `decidable_of_iff`. The *concrete
  filtration* does not transfer (propositional Kripke, not linear-temporal lasso).

### 5c. NOT reusable (surveyed and rejected, with reason)

- **Bimodal FMP** (`Bimodal/Metalogic/Decidability/FMP/*` — Filtration, FiniteModel,
  TruthPreservation, DiscreteFMP, DenseFMP): canonical-model **filtration** route over an MCS
  frame, structurally disjoint from the tableau. Would require re-deriving the whole tableau→MCS
  bridge to reuse. Rejected.
- **LTL ω-automata** (`Logics/LTL/Semantics/OmegaRegular.lean`, `GNBA`, `OmegaRegularLanguage`):
  **ℕ-indexed, future-only** ω-sequences with a Büchi-automaton decision route. PTL/BX here is
  **ℤ-indexed and bidirectional** (Since as well as Until). Different time model and directionality;
  no direct transfer. Rejected as a reuse source, though it confirms the ultimately-periodic idea is
  the right shape.
- **Temporal Chronicle Hilbert completeness** (`Metalogic/Completeness.lean`, sorry-free): gives
  `valid φ ↔ Derivable φ`, but decidability of `Derivable` is not independently established, so this
  does not yield `instDecidableValid` without the tableau. It *does* provide an independent
  soundness/completeness cross-check for validating the tableau result. Keep as an oracle, not a
  dependency.

---

## 6. Recommended Approach (Sorry-Free, Phased)

Zero-debt compliant: no `sorry`, no new axioms, no vacuous `def _ := True`. Decompose rather than
defer. Suggested phase ordering (each phase ends green with `lake build
Cslib.Logics.Temporal.Tableau.<Module>`):

1. **Phase A — Soundness half (lowest risk, independent).** Prove `eventualityDefect_unsat`
   (`Soundness.lean`) by the pumping argument of §3, consuming `findEventualityDefect` /
   `isSubsetBlocked` / `allEventualitiesFulfilledOrDuplicated`. Then glue with
   `classicallyClosed_unsat` to prove `temporalTableau_sound` via the fuel-induction loop invariant
   (reuse the `processNext` / strong-fuel-induction skeleton already used for
   `temporalTableau_instantStrict`, `Saturation.lean:366-547`).

2. **Phase B — Countermodel redesign (critical, §4).** Replace `extractModelℤ` with the
   ultimately-periodic lasso model; re-prove the `extractModelℤ_*` atom/bot property lemmas against
   the new definition. Add helper lemmas: loop extraction from `isSubsetBlocked`, periodic-index
   reduction, and "every instant carries a complete Hintikka time-type."

3. **Phase C — Until truth lemma.** Prove `temporalTruthLemma_untl` over the Phase-B model using
   `untl_iff`, the fulfilment guarantee from openness (`findEventualityDefect = none`), and the
   propositional `ih`. Mirror `tUntilEventualityResolution`'s forward-witness structure.

4. **Phase D — Since truth lemma.** `temporalTruthLemma_snce` symmetrically (past direction). The
   `swapTemporal` duality already present in `Formula.lean:384-386` and Satisfies may let this reuse
   Phase C via a mirror lemma rather than a full re-proof — investigate first.

5. **Phase E — Assemble completeness.** `openBranch_branchSat` (combine order-preservation from
   `temporalTableau_instantStrict` with the full truth lemma), then `temporalTableau_complete`.

6. **Phase F — Decidability instance.** `instDecidableValid : Decidable (Temporal.valid φ)` via
   `valid φ ↔ temporalTableau (¬φ) = .closed`, using `temporalTableau_sound` +
   `temporalTableau_complete` and `decidable_of_iff`. Note task-301 wiring also needs sibling tasks
   423/424 landed; this phase should expose the instance but final `instDecidableValid` registration
   may await them (flag to orchestrator).

**Size estimate:** ~800–1500 lines across the phases; Phase B is the schedule risk. Each phase is
independently buildable and independently valuable (Phase A alone closes the soundness gate).

---

## 7. Infrastructure / Tactic Inventory (advisory)

- **Induction skeletons to reuse:** strong induction on `fuel` + structural induction on the
  worklist (as in `temporalTableau_instantStrict`); strong induction on `Formula.complexity` (as in
  `temporalTruthLemma_propositional_aux`). Both are already load-bearing and sorry-free.
- **Finiteness lemmas likely needed from Mathlib:** pigeonhole / `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
  (for the pumping/loop-existence argument), `List.eraseDups` / `List.Subset` reasoning (subset
  blocking is a `List.all`/`List.any` predicate over `timeType`). Verify exact names during
  implementation with `lean_leansearch` / `lean_loogle` — not pre-verified here to avoid rate-limit
  spend on a research pass.
- **Entry-point lemmas:** `untl_iff`, `snce_iff` (`Satisfies.lean:104,113`); `Satisfies.imp_iff`,
  `Satisfies.bot_false` (already used in the propositional case).
- **Duality lever:** `swapTemporal` (`Formula.lean`) may collapse Phase D into a corollary of Phase C.

---

## 8. Risks and Open Questions

1. **Highest risk — Phase B model redesign.** If the periodic-ℤ construction proves intractable in
   Lean, the fallback is the finite `ZMod k` domain route (§4 alternative), which requires changing
   the `branchSat` / countermodel interface and re-checking `InstantStrict` — a larger blast radius.
   Recommend spiking Phase B's core definition + one property lemma before committing the full plan.
2. **`branchSat` domain generality.** `branchSat` (`Soundness.lean:79`) existentially quantifies `D`
   as arbitrary `LinearOrder` + `Nontrivial`. Confirm the periodic ℤ-model still satisfies
   `Nontrivial` and the order-preservation clause end-to-end.
3. **Guard-between over unpopulated instants.** The correctness of Phase C hinges on *every* instant
   in the loop carrying a full Hintikka time-type. Confirm `temporalHintikkaSet` saturation actually
   forces the guard onto every intermediate branch time (via the persistent G/H propagation rules) —
   spot-checked as plausible from `Saturation.lean:34` but not exhaustively verified.
4. **Task-301 final wiring** needs tasks 423 and 424 landed; `instDecidableValid` registration may
   need to be staged. Independent in principle (task text confirms).

---

## 9. References

- `Cslib/Logics/Temporal/Tableau/{Branch,Closure,Defs,Rules,Saturation,Soundness,Completeness,TimeOrdering}.lean`
  — the target module (design docstrings in `Soundness.lean:169-198`, `Completeness.lean:34-63,374-417`).
- `Cslib/Logics/Temporal/Semantics/{Satisfies,Validity}.lean` — Until/Since semantics, `valid`.
- `Cslib/Logics/Temporal/Metalogic/Chronicle/Frame.lean:234-252` — `tUntilEventualityResolution`,
  `tSinceEventualityResolution` (argument template).
- `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean` — task-421 FMP→Decidable *pattern*.
- `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/*` — surveyed, rejected (filtration route).
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` — surveyed, rejected (ℕ-indexed ω-automata).
- [R. Reynolds, *An axiomatization of Prior's tense logic*][Reynolds1994] — cited throughout the module.
- Standard PTL FMP / ultimately-periodic models: Wolper; Lichtenstein–Pnueli–Zuck (background only).
