# Research Report: Validity-Notion Determination and FMP Grounding for the Temporal Tableau

- **Task**: 425 - temporal_tableau_ptl_fmp_decidability
- **Started**: 2026-07-24
- **Completed**: 2026-07-24
- **Effort**: ~3 hours (hard-mode, literature-grounded)
- **Dependencies**: Resolves the Phase A `[BLOCKED]` finding in `plans/01_ptl-fmp-decidability-plan.md`; input to `/revise 425`
- **Sources/Inputs**:
  - Prior artifacts: `handoffs/01_phase-a-blocker-handoff.md`, `plans/01_ptl-fmp-decidability-plan.md`, `reports/01_ptl-fmp-decidability-survey.md`
  - Code (machine-verified this dispatch): `Semantics/Validity.lean`, `Semantics/Satisfies.lean`, `Tableau/Soundness.lean`, `Tableau/Rules.lean`, `Tableau/TimeOrdering.lean`, `Tableau/Branch.lean`, `Tableau/Closure.lean`
  - Literature (verified against chunk text): Burgess 1982 I `[Burgess1982I]`, Hodkinson-Reynolds 2006 (Handbook ch. 11), Caleiro-Viganò-Volpe 2013 (mosaics), Gabbay-Hodkinson-Reynolds book `[GHR94]`, Reynolds 1994 `[Reynolds1994]`, Blackburn-de Rijke-Venema `[Blackburn2001]`
- **Artifacts**: `specs/425_temporal_tableau_ptl_fmp_decidability/reports/02_validity-notion-fmp-grounding.md`
- **Standards**: report-format.md, reference-grounding.md (H3 lean4), anti-analysis.md (H2 lean4), citation-conventions.md

## Executive Summary

- **VERDICT (certain): the tableau soundly and completely decides `Temporal.validDiscrete`, not
  `Temporal.valid` and not `Temporal.validSerial`.** Machine-verified: `TimeOrdering.addFuture`/
  `addPast` place each fresh time at `instant t ± 1` (the immediate integer successor/predecessor,
  `TimeOrdering.lean:78,88`), and `untlPos` branch1 = `[T(event)@t']` places the Until witness at
  that immediate successor with **no** guard-between clause (`Rules.lean:270`) — semantically sound
  only when the open interval `(t, t')` is empty, i.e. under discreteness.
- **Literature confirms the separation.** `[Burgess1982I]` §1.5 (p. 3, results table) gives
  *distinct* sound-and-complete axiomatizations of the Since/Until tense logic per order class; the
  **Discreteness axiom is `G'⊥ ∧ H'⊥`** (an immediate next/previous instant with nothing between),
  and the all-linear-orders logic `J₀` is complete via a model built **over the rationals** (a dense
  order; `[Burgess1982I]` §2, p. 5). The discreteness axiom is therefore in the `validDiscrete \
  valid` gap: a concrete witness formula the tableau would (correctly, for `validDiscrete`) accept
  but that is *not* `valid`.
- **`branchSat`'s current signature is the wrong notion.** It existentially quantifies over
  arbitrary `[LinearOrder D] [Nontrivial D]` (`Soundness.lean:82`), i.e. all-linear-orders
  satisfiability. This is why `eventualityDefect_unsat` (`¬branchSat`) is provably too strong — the
  implementer's explicit two-witness consistent assignment (blocker finding #2) is a genuine
  countermodel over a *dense* domain. The fix is to restrict `branchSat`'s domain to the
  discrete-serial frame class (`NoMaxOrder + NoMinOrder + SuccOrder + PredOrder +
  IsSuccArchimedean`), matching `validDiscrete`.
- **`eventualityDefect_unsat` needs two things the bare lemma lacks**: (i) a **run-level
  tracker/branch faithfulness invariant** tying `tracker.pending` entries to actual
  `⟨.pos, e.formula, e.label⟩ ∈ b` members (established by induction over the `temporalStepBranch`
  run, mirroring `temporalTableau_instantStrict`), and (ii) the **discrete domain** so that
  `IsSuccArchimedean` gives a finite successor-distance to any witness, enabling the
  loop/pigeonhole "no least witness" contradiction. It is a semi-local argument over the finite
  loop — it does *not* construct the ℤ model — but it *does* require discreteness.
- **FMP construction is the bidirectional ultimately-periodic (bi-lasso) ℤ-model**, grounded in the
  classical discrete-PTL FMP (Hodkinson-Reynolds 2006 §5.8; the ℤ analogue of Sistla-Clarke/Wolper).
  Deciding the *all-linear-orders* logic instead would require the **mosaic method** (Caleiro 2013
  §4.3), a structurally different technique — confirming the plan's rejection of that route and the
  choice of the periodic construction for the discrete logic.
- **Net effect on the plan**: no phase is theoretically blocked. The redesign is (1) introduce a
  `satisfiableDiscrete` predicate + restrict `branchSat`'s domain; (2) restate the four public
  targets against `validDiscrete`/`satisfiableDiscrete`; (3) add the run-level faithfulness invariant
  as a Wave-1 prerequisite. Phase F targets `Decidable (Temporal.validDiscrete φ)`.

## Context & Scope

The task introduces seven declarations (`eventualityDefect_unsat`, `temporalTableau_sound`,
`temporalTruthLemma_untl/snce`, `openBranch_branchSat`, `temporalTableau_complete`,
`instDecidableValid`). A first implementation dispatch halted before writing code, finding the
plan semantically unsound on three counts. This report resolves all three with code + literature
evidence and specifies the corrected target statements so `/revise 425` can proceed.

Reference-grounding tier: **Tier 1 (literature-backed)** — the validity-notion choice and the FMP
construction are grounded in published tense-logic results.

## Findings

### Source-to-Implementation Mapping (H3, Tier 1 — 5-column)

| Source | Prop/Location | Lean Identifier | Type Signature (target) | Status |
|--------|---------------|-----------------|--------------------------|--------|
| `[Burgess1982I]` | §1.5 results table (Discreteness axiom `G'⊥∧H'⊥`), p. 3; §2 dense/rationals model, p. 5 | `Temporal.validDiscrete` (existing) | `∀ D [LinearOrder][Nontrivial][NoMaxOrder][NoMinOrder][SuccOrder][PredOrder][IsSuccArchimedean] M t, Satisfies M t φ` | transcribed (exists, `Validity.lean:96`) |
| `[Burgess1982I]` §2 / Hodkinson-Reynolds 2006 §5.8 | discrete-time satisfiability predicate (dual of discrete validity) | `Temporal.satisfiableDiscrete` (NEW) | `∃ D [LinearOrder][Nontrivial][NoMaxOrder][NoMinOrder][SuccOrder][PredOrder][IsSuccArchimedean] M t, Satisfies M t φ` | pending |
| Hodkinson-Reynolds 2006 | §5.8 Filtration & FMP, p. 706; §5.4 Tableaux, p. 702 | `branchSat` (RESTRICT domain) | `∃ D (discrete-serial instances) M f, (order-preserving) ∧ (branch faithful)` | pending (revise `Soundness.lean:79`) |
| Hodkinson-Reynolds 2006 §5.8 + `[GHR94]` | ultimately-periodic model for discrete PTL (bi-lasso over ℤ) | `extractModelℤ` (REDESIGN) | `TBranch → TimeOrdering → TemporalModel ℤ Atom` | pending (`Completeness.lean:133`) |
| `[Burgess1982I]` C4a/C5a witness lemmas §2, p. 4-5; Reynolds `[Reynolds1994]` | Until eventuality → forward witness (discrete) | `temporalTruthLemma_untl` | `openBranch … → Satisfies (extractModelℤ …) (instant t) (U(g,e))` | pending |
| `[Burgess1982I]` mirror C4b/C5b | Since eventuality → backward witness | `temporalTruthLemma_snce` | symmetric | pending |
| Hodkinson-Reynolds 2006 §5.4 (tableau soundness) | closed branch → no discrete model | `eventualityDefect_unsat`, `temporalTableau_sound` | `… → ¬ branchSat` / `.closed → ¬ satisfiableDiscrete φ` | pending |
| Caleiro-Viganò-Volpe 2013 | §4.3 Decidability via mosaics (the *rejected* all-linear-orders route) | — (no Lean target; documents why NOT `valid`) | — | n/a (rejection evidence) |

BibKey verification against `references.bib`: `Burgess1982I` ✓, `GHR94` ✓, `Reynolds1994` ✓,
`Blackburn2001` ✓ present. **Missing (must be added before citing in-source):** a Handbook-ch.11
key (`HodkinsonReynolds2006`), a mosaics key (`CaleiroViganoVolpe2013`), and the 1993 "gaps" article
(distinct from the `GHR94` book). Use full citation until added.

### Finding 1 — Which validity notion the tableau decides (the deep question)

**Machine-verified code facts** (this dispatch):

1. `Temporal.valid` = all nontrivial linear orders (`Validity.lean:76-79`). `Temporal.validDiscrete`
   = `+ NoMaxOrder + NoMinOrder + SuccOrder + PredOrder + IsSuccArchimedean` (`Validity.lean:96-101`).
   Dense/discrete documented incomparable (`Validity.lean:38`).
2. `TimeOrdering.addFuture t tNew` sets `instant tNew = instant t + 1`; `addPast` sets
   `instant t - 1` (`TimeOrdering.lean:78,88,63`). Every existential rule advances by an **immediate
   integer step**. `extractModelℤ` uses `ord.instant : TimeIndex → ℤ` (`Completeness.lean:133`).
3. `untlPos` branch1 = `[⟨.pos, event, t'⟩] ++ props` with `t' = branchNextTime b`,
   `newOrd = ord.addFuture t t'` — event asserted at the immediate successor, **no** guard clause on
   `(t, t')` (`Rules.lean:264-272`). The Until semantics require `∀ r, t < r → r < s → guard(r)`
   over the *whole* open interval (`Satisfies.lean:70-72`, `untl_iff` `:104`). Branch1 is sound iff
   `(instant t, instant t')` is empty — i.e. `t'` is the immediate successor: **discreteness**.
4. ℤ carries every instance in `validDiscrete`'s frame class (`LinearOrder`, `Nontrivial`,
   `NoMaxOrder`, `NoMinOrder`, `SuccOrder`, `PredOrder`, `IsSuccArchimedean` — all Mathlib
   instances). So the extracted model is a `validDiscrete`-class model.

**Decision-procedure biconditional analysis** (`valid φ ↔ temporalTableau (¬φ) = .closed`):

- (→) `open → ¬valid`: an open branch yields a discrete ℤ model of `¬φ`; ℤ is a nontrivial linear
  order, so `φ` fails there ⇒ `¬valid φ`. Holds for `valid` (and for `validDiscrete`).
- (←) `closed → valid`: **FAILS for `valid`.** Contrapositive needs `¬valid φ → open`. `¬valid φ`
  can hold because `¬φ` is satisfiable *only over a dense order*; the discrete tableau then still
  **closes** `¬φ`. So `closed ⇏ valid`.

**Concrete witness (literature-grounded).** `[Burgess1982I]` §1.5 (p. 3): the discrete Since/Until
logic is `J₀ + (G'⊥ ∧ H'⊥)`, and `J₀` alone is complete for **all** linear orders via a model over
the **rationals** (`[Burgess1982I]` §2, p. 5, "the order being the usual order on the rationals").
Hence the discreteness axiom `D := G'⊥ ∧ H'⊥` satisfies `validDiscrete D` but **not** `valid D`
(it fails over ℚ, where `G'⊥` is false). The tableau accepts `D` as valid — correct for
`validDiscrete`, wrong for `valid`. This is a definitive, non-two-witness proof that the tableau
does not decide `valid`.

By the same argument the tableau does **not** decide `validSerial` (the `(←)` direction fails for
any formula whose negation is dense-only-satisfiable; serial ⊇ dense serial). The unique matching
notion is **`validDiscrete`**: `closed ⟹ "¬φ has no discrete serial model" ⟹ validDiscrete φ`, and
`validDiscrete`'s frame class (`NoMax+NoMin+SuccOrder+PredOrder+IsSuccArchimedean`, ≅ ℤ for the
connected archimedean case) is exactly the tableau's model class.

### Finding 2 — Corrected target statements

1. **New predicate** in `Semantics/Validity.lean` (mirrors `satisfiable`, discrete frame class):
   ```lean
   def satisfiableDiscrete (φ : Formula Atom) : Prop :=
     ∃ (D : Type) (_ : LinearOrder D) (_ : Nontrivial D)
       (_ : NoMaxOrder D) (_ : NoMinOrder D)
       (_ : SuccOrder D) (_ : PredOrder D) (_ : IsSuccArchimedean D)
       (M : TemporalModel D Atom) (t : D), Satisfies M t φ
   ```
   plus the discrete dual `validDiscrete_iff_not_satisfiableDiscrete_neg :
   validDiscrete φ ↔ ¬ satisfiableDiscrete (¬φ)` (mirror of `satisfiable_not_valid_neg`,
   `Validity.lean:197`).

2. **`branchSat`** (`Soundness.lean:79-87`): add the five discrete-serial instance binders to the
   existential, keeping the order-preservation and branch-faithfulness clauses unchanged:
   ```lean
   def branchSat (b : TBranch Atom) (ord : TimeOrdering) : Prop :=
     ∃ (D : Type) (_ : LinearOrder D) (_ : Nontrivial D)
       (_ : NoMaxOrder D) (_ : NoMinOrder D)
       (_ : SuccOrder D) (_ : PredOrder D) (_ : IsSuccArchimedean D)
       (M : TemporalModel D Atom) (f : TimeIndex → D),
       (∀ t t', (t, t') ∈ ord.constraints → f t < f t') ∧
       ∀ sf ∈ b, (sf.sign = .pos → Satisfies M (f sf.label) sf.formula) ∧
                 (sf.sign = .neg → ¬ Satisfies M (f sf.label) sf.formula)
   ```
   `classicallyClosed_unsat` (`Soundness.lean:97`) is unaffected structurally (it only destructs the
   existential; the extra binders are discarded with `_`).

3. **Soundness**: `temporalTableau_sound : temporalTableau φ = .closed → ¬ satisfiableDiscrete φ`.

4. **Completeness**: `temporalTableau_complete :
   (∃ b ord, temporalTableau φ = .openBranch b ord) → satisfiableDiscrete φ`, with
   `openBranch_branchSat` witnessing `branchSat` via `D := ℤ`.

5. **Decision instance**: `instDecidableValid : Decidable (Temporal.validDiscrete φ)` via
   `validDiscrete φ ↔ temporalTableau (¬φ) = .closed` and `decidable_of_iff`
   (`noncomputable` acceptable, task-421 pattern).

### Finding 3 — The correct eventuality-defect unsatisfiability argument + invariant threading

The blocker's findings #1 and #2 are both confirmed and both are resolved by the same two additions.

**(a) Run-level faithfulness invariant (resolves finding #1).** `findEventualityDefect b ord tracker
= some t` (`Closure.lean:88-91`) only asserts `tracker.hasPending` plus a subset-block +
`allEventualitiesFulfilledOrDuplicated` witness (`Branch.lean:146-167`). Nothing ties
`e ∈ tracker.pending` to `⟨.pos, e.formula, e.label⟩ ∈ b`. That link is created only by
`registerEventualities`/`fulfillEventualities` during the run (`Saturation.lean:85-100`). The lemma
must therefore take a hypothesis:
```lean
def TrackerBranchFaithful (b : TBranch Atom) (ord : TimeOrdering)
    (tracker : EventualityTracker Atom) : Prop :=
  ∀ e ∈ tracker.pending,
    ⟨.pos, e.formula, e.label⟩ ∈ b ∧ (e.isUntil = true → e.formula.isUntl) ∧ …
```
established by induction over `temporalStepBranch` (the same `run_level_P1`/fuel-induction skeleton
that already discharges `temporalTableau_instantStrict`, `Saturation.lean:366-547`), analogous to
the existing `WorklistInv`/`OrdFreshWRT` machinery. `eventualityDefect_unsat` then takes
`(hfaithful : TrackerBranchFaithful b ord tracker)` alongside the `findEventualityDefect … = some t`
hypothesis.

**(b) Discreteness makes the defect genuinely unsatisfiable (resolves finding #2).** The
two-witness consistent assignment the implementer constructed lives in a *dense* domain — it is a
real countermodel to `¬branchSat` under the *old* general signature, but not under the discrete
signature. With `branchSat` over discrete serial `D`:
- `U(g,e)@f(t_anc)` true in a discrete serial model forces, by `IsSuccArchimedean`, a **least**
  witness instant `s` reachable in *finitely many* successor steps (`Succ`-iterates), because the
  successor-distance `f(t_anc) → s` is finite and `ℕ`-well-founded.
- The subset-block `isSubsetBlocked b t t_anc` (`Branch.lean:120-123`, `timeType b t ⊆ timeType b
  t_anc`) with the recurring pending eventuality (`allEventualitiesFulfilledOrDuplicated`,
  `Branch.lean:146-154`) means the guard-only time-type at the blocked point `t` **equals** the
  ancestor's on the relevant formulas, so the "distance to a witness" cannot strictly decrease
  around the loop — contradicting the strictly-decreasing least-witness measure. Formally: a
  pigeonhole/`König`-style argument over the finite `timeType` space (candidate Mathlib lemma
  `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`, to be verified with `lean_loogle` at
  implementation) combined with `IsSuccArchimedean` well-foundedness.

This is a **semi-local** argument: it reasons about an *arbitrary discrete serial model* of the
branch and derives a contradiction from the finite loop; it does **not** build the ℤ model (that is
the completeness side). Report 01 §3's "reasons about a model rather than building one" framing was
correct — but only once the domain is discrete; over the general `LinearOrder` domain the lemma is
false, exactly as the implementer found.

**Does it need the full lasso machinery?** No — the *soundness* side (`eventualityDefect_unsat`)
needs only the finite loop + `IsSuccArchimedean`. The **completeness** side
(`temporalTruthLemma_untl/snce`, `openBranch_branchSat`) is what needs the full bidirectional
ultimately-periodic (bi-lasso) ℤ-model construction of report 01 §4.

### Finding 4 — FMP construction and the rejected all-linear-orders route (grounding the plan)

- **Chosen route (discrete PTL FMP).** Hodkinson-Reynolds 2006 §5.8 ("Filtration and the finite
  model property", p. 706) and `[GHR94]` give the discrete-time FMP: a satisfiable discrete PTL
  formula has an ultimately-periodic model. Over ℤ (two-way infinite, Since *and* Until) this is a
  **bi-lasso**: periodic past tail + finite middle + periodic future tail — exactly report 01 §4's
  redesign (prefix `[min..t_anc]`, loop body `(t_anc..t_new]`, periodic extension both directions).
  Grounded and correct.
- **Rejected route (all linear orders).** Deciding `Temporal.valid` (all linear orders) is a
  *different* problem requiring the **mosaic method** — Caleiro-Viganò-Volpe 2013 §4.3
  ("Decidability Via Mosaics": "`L(C, ⟨⟩)`, for `C` a class of linear orders, is decidable" via a
  finite set of mosaics, not a single periodic model). This independently confirms the plan's
  rejection of a filtration/automata route *and* explains *why* the tableau's periodic construction
  cannot decide `valid`: the periodic model is intrinsically discrete.

## Decisions

1. The tableau decides **`Temporal.validDiscrete`**. All public targets are restated against
   `validDiscrete`/`satisfiableDiscrete`; `instDecidableValid : Decidable (validDiscrete φ)`.
2. `branchSat`'s existential domain is restricted to the discrete-serial frame class; a new
   `satisfiableDiscrete` predicate is added to `Semantics/Validity.lean`.
3. `eventualityDefect_unsat` gains a `TrackerBranchFaithful` run-level invariant hypothesis, proved
   by fuel-induction over the run (reusing the `temporalTableau_instantStrict` skeleton).
4. No target is theoretically blocked; the task returns to `/revise` → `/plan` → `/implement`.

## Recommendations (plan revision — phase restructure)

Prioritized, for `/revise 425`:

1. **New Wave-0 phase (Semantics)** — add `satisfiableDiscrete` + the discrete dual lemma to
   `Semantics/Validity.lean`; restrict `branchSat`'s domain in `Soundness.lean`. Small, unblocks
   everything, and re-verifies `classicallyClosed_unsat` still builds. (~1-2 h)
2. **New Wave-1 phase (Faithfulness invariant)** — define `TrackerBranchFaithful` and prove it as a
   run-level invariant over `temporalStepBranch` (mirror `temporalTableau_instantStrict`). This is
   the genuine new prerequisite the old plan lacked; it gates Phase A. (~3-4 h)
3. **Revise Phase A** — `eventualityDefect_unsat` over the discrete `branchSat`, consuming the
   faithfulness invariant + the `IsSuccArchimedean` least-witness/pigeonhole argument; then
   `temporalTableau_sound : .closed → ¬ satisfiableDiscrete φ`. (~4 h)
4. **Phases B-E unchanged in structure** (bi-lasso `extractModelℤ`, `_untl`/`_snce`,
   `openBranch_branchSat`, `temporalTableau_complete`) but with `branchSat`/witness typed at the
   discrete domain `D := ℤ` (ℤ already carries all five instances — a *simplification*, since the
   old plan's Risk "`branchSat` domain generality not satisfied by periodic ℤ-model" now vanishes).
5. **Revise Phase F target** to `Decidable (Temporal.validDiscrete φ)` via
   `validDiscrete φ ↔ temporalTableau (¬φ) = .closed`.
6. **Add BibKeys** `HodkinsonReynolds2006`, `CaleiroViganoVolpe2013` (and the 1993 gaps article) to
   `references.bib`, and update the `## References` sections of `Soundness.lean`/`Completeness.lean`
   to the canonical `[Author, *Title*][BibKey]` format (they currently carry only the legacy
   `[Reynolds1994]` citation).
7. **Zero-debt**: no `sorry`, no new axioms. If the `IsSuccArchimedean` pumping proves intractable
   in Lean, the fallback is a `Fin`-indexed cyclic quotient — but this is now *lower* risk than in
   the old plan because the domain is already committed to discrete.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `TrackerBranchFaithful` induction over the run is large | M | M | Reuse `temporalTableau_instantStrict`'s exact fuel/worklist skeleton (`Saturation.lean:366-547`); it already threads a run-level `P1`-style invariant |
| `IsSuccArchimedean` least-witness measure hard to formalize | M | M | Mathlib `Order.SuccPred.Archimedean` (already imported by `Validity.lean:12`) provides `Succ.rec`/archimedean lemmas; spike the measure before Phase A commits |
| `validDiscrete ↔ closed` dual lemma direction errors | L | L | Mirror the proved `satisfiable_not_valid_neg` (`Validity.lean:197`) verbatim with discrete binders |
| Missing BibKeys block clean `## References` | L | H | Add three `references.bib` entries in Wave-0 |

## Context Extension Recommendations

- **Topic**: Which `Temporal.valid*` notion a discrete successor-based tableau decides.
  **Gap**: No context file records that ℤ/successor `TimeOrdering` designs decide `validDiscrete`
  (not `valid`/`validSerial`), nor the `untlPos`-branch1-empty-interval discreteness dependency.
  **Recommendation**: capture as a memory candidate (below) and, if it recurs, a short note under
  `.claude/extensions/cslib/context/project/cslib/` on the validity-hierarchy ↔ tableau-frame-class
  correspondence.

## Adversarial Self-Verification (H4)

Every load-bearing claim was re-challenged; challenges and resolutions:

- **Challenge: "Could it be `validSerial` (covers discrete)?"** No. `validSerial` ranges over all
  serial orders incl. dense; the `(←)` biconditional direction fails for any dense-only-satisfiable
  negation. Verified via the same discreteness-axiom witness. **Confidence: high.**
- **Challenge: "Is branch1's issue soundness or completeness?"** Resolved as a *frame-class* issue
  manifesting in the decision biconditional's `(←)` direction for `valid`, and independently in the
  *extracted* model being discrete. Both point to `validDiscrete`. Machine-checked `Rules.lean:270`
  vs `Satisfies.lean:70-72`. **Confidence: high.**
- **Challenge: "Is `IsSuccArchimedean` actually needed / available?"** Needed for finite
  successor-distance (least witness); available (`Mathlib.Order.SuccPred.Archimedean`, imported at
  `Validity.lean:12`; ℤ instance exists). Without it, non-archimedean discrete chains (ℤ+ℤ) could
  host an unwitnessed eventuality. **Confidence: high.**
- **Challenge: "Does a dense-only-satisfiable formula really exist (to rule out `valid`)?"**
  Yes — the discreteness axiom `G'⊥∧H'⊥` itself, grounded in `[Burgess1982I]` §1.5 (extra axiom for
  the discrete class) and §2 (all-linear-orders completeness over the dense rationals). This is a
  *literature-verified* witness, not an instinct. **Confidence: high.**
- **Challenge: "Is `eventualityDefect_unsat` a two-point argument after all?"** No — the implementer's
  two-witness countermodel is correct over dense domains; the correct argument is a finite-loop
  pigeonhole under `IsSuccArchimedean`. Confirmed by re-deriving. **Confidence: high.**
- **Citation verification (H4/H3):** Burgess 1982 I claims verified against the actual chunk text
  (`burgess_1982_i/…md` lines 14, 47, 83-88, 238 read this dispatch — discreteness axiom `G'⊥∧H'⊥`
  and the rationals model confirmed verbatim). Caleiro 2013 §4.3 mosaic-decidability claim verified
  against `sec07_43-decidability-via-mosaics.md` line 11. Hodkinson-Reynolds 2006 §5.4/§5.8
  section titles verified against the ToC (lines 41,45,47); the FMP *content* claim is cited at
  section granularity (single corroborating source) — **medium confidence on the exact page-level
  FMP statement**, high confidence on its existence given `[GHR94]` corroboration.
- **BibKey checks** run against the real `references.bib`; three missing keys flagged rather than
  fabricated. No citation is asserted with an unverified BibKey.

Verification outcome: **the core verdict strengthened** (the discreteness-axiom witness upgraded the
`valid`-exclusion from a two-witness heuristic to a literature-grounded proof; `validSerial` was
additionally excluded). No fundamental flaw found; **no `## Revised Direction` restart needed.**

## Appendix

- Code anchors: `Validity.lean:76-101` (hierarchy), `:197` (dual template); `Satisfies.lean:66-118`
  (semantics, `untl_iff`/`snce_iff`); `Soundness.lean:79-101` (`branchSat`, `classicallyClosed_unsat`);
  `Rules.lean:246-284` (existential + Until/Since rules); `TimeOrdering.lean:57-91` (`instant`,
  `addFuture`/`addPast` ±1); `Branch.lean:44-167` (`Eventuality`, tracker, `isSubsetBlocked`,
  `allEventualitiesFulfilledOrDuplicated`); `Closure.lean:88-108` (`findEventualityDefect`);
  `Saturation.lean:85-100,366-547` (`registerEventualities`/`fulfillEventualities`, run induction).
- Literature: `[Burgess1982I]` = J. P. Burgess, *Axioms for Tense Logic I: "Since" and "Until"* (1982);
  `[GHR94]` = Gabbay, Hodkinson, Reynolds, *Temporal Logic* (1994); `[Reynolds1994]`; Hodkinson &
  Reynolds, *Temporal Logic* (Handbook of Modal Logic, ch. 11, 2006); Caleiro, Viganò, Volpe,
  *On the Mosaic Method for Many-Dimensional Modal Logics* (2013); `[Blackburn2001]`.
