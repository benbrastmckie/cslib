# Teammate D Findings — Strategic Horizons (Task 448)

**Task type**: cslib (research — horizons/trajectory alignment, read-only)
**Date**: 2026-07-01
**Role**: Teammate D — long-term strategic direction; challenge the framing where a better path exists.
**Ground-truth basis**: report 419/04; `ProofSystemMorphism.lean` (whole); `GenericMCS.lean`;
per-logic `GenericMCSBridge.lean` (Modal/Temporal/Bimodal); ROADMAP; task descriptions 41, 407,
415, 412, 414; Modal Systems soundness skeleton. All claims below are grounded in files read this
session.

---

## Key Findings

1. **CSLib already has a shared-metatheory substrate — and it is not `Deriv σ`.**
   `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` is explicitly "the **algebraic seam** of
   CSLib's MCS infrastructure." It builds **one** generic `DerivationSystem` and proves
   `HasDeductionTheorem` **once**; every logic inherits the full MCS machinery
   (`closed_under_derivation`, `implication_property`, `negation_complete`) for free. Six logic
   configurations already route through it via per-logic `GenericMCSBridge.lean`: PL, Modal,
   Temporal-Base, Temporal-fc, Bimodal-Base, Bimodal-fc. **This is the exact "prove once, transport
   to every logic" ambition Vision B proposes — already built, already merged, already upstream.**

2. **The existing seam deliberately lives at the Prop/derivability level, which is *why* it never
   hits the large-elimination wall.** The bridge equivalences (`*_deriv_iff_algebraic`) are stated
   on `Nonempty (DerivationTree …)` — Prop-valued derivability — so the round-trip is a Prop
   iff, not a Type-level `Equiv`. The R1 refactor and backward-map machinery that Vision B needs
   exist *only* because `Deriv σ` is **Type-valued**. The library's own working substrate shows
   that the payoff metatheorems (deduction theorem, MCS closure, completeness plumbing) **do not
   require derivations-as-data at all** — Prop-level derivability suffices.

3. **The single highest-leverage generic metatheorem — the deduction theorem — is already shared
   by GenericMCS.** Vision B's own top Phase-3 candidate ("a generic deduction theorem on
   `Deriv σ`") would **re-deliver, at the Type level and behind an R1 refactor, a result the
   Prop-level seam already transports to all six logic configs.** That is duplication of the
   substrate's flagship result, not new leverage.

4. **The roadmap's remaining work is completeness, which is Prop/MCS-shaped — served by extending
   GenericMCS, not by `Deriv σ`.** ROADMAP "Remaining" = discrete/continuous/dense completeness
   (Bimodal + Temporal) + "**Abstract shared completeness infrastructure between temporal and
   bimodal**" (task 41). Task 41's own description says the scaffold goes "in
   `Foundations/Logic/Metalogic/`, **extending the existing generic MCS framework (Task 29)**,"
   and every one of its five candidate abstractions (neg_consistent_of_not_derivable, completeness
   contrapositive skeleton, canonical-order construction, dense-indicator elimination) is a
   **derivability/MCS-level** result. None needs the Type-valued derivation *structure* that
   `Deriv σ` uniquely provides.

5. **Soundness is already parameterized where it matters.** `Modal/Metalogic/Soundness.lean` is a
   "parameterized soundness theorem"; the 16 per-system files (K…S5) are thin (60–85 ln) and carry
   only irreducible per-axiom validity content. A generic `Deriv σ` soundness skeleton would sit
   *above* an abstraction that is already factored one level down.

**Bottom line:** Vision B is not aligned with the current trajectory as a *substrate* play,
because the trajectory already has its substrate (GenericMCS) at the correct (Prop) level, and the
roadmap's open work consumes that substrate, not a Type-level derivation algebra. Vision A
(`Deriv.map`, delivered) *is* aligned and complementary: it does the one thing GenericMCS does
**not** — transport derivations **across** proof systems (cross-syntax, `liftFormula`), whereas
GenericMCS shares metatheory **within** a fixed derivability abstraction.

---

## Roadmap Alignment (named tasks/areas the substrate accelerates or not)

**Would a Type-level `Deriv σ` substrate accelerate — assessed against real tasks:**

| Roadmap / task | Needs derivations-as-DATA? | Accelerated by `Deriv σ`? | Why |
|---|---|---|---|
| **Task 41** — abstract shared completeness infra (Temporal+Bimodal) | No — MCS/derivability | **No** | Explicitly extends **GenericMCS**; candidates are Prop-level (consistency, Lindenbaum, canonical order) |
| **Tasks 36/37/39/40** — discrete/continuous/dense completeness | No — canonical model | **No** | Semantic completeness via MCS; uses derivability facts already shared |
| **Task 407** — MPL structure-first; "structural metatheory proved ONCE at MPL" | Partly (weakening/subst/cut) | **Marginal** | Its genericity target is the property-module/typeclass layer, not a new derivation inductive |
| **Task 415** — audit propositional lifting; conservativity asymmetry (finding #2), GenericLindenbaum debt (finding #3) | No | **No** (but adjacent) | Wants a *parametric conservativity-lift framework* and GenericLindenbaum consolidation — Prop-level; note `Deriv.map` (Vision A) is the natural home for the *lift* half |
| **Tasks 412/414** — normalization-lemma proof simplification | No | **No** | `grind`/`simp` cleanup, orthogonal |
| **Modal/Temporal tableau** (299/300/301/425/426/442) | No | **No** | Tableau decision procedures, separate architecture from Hilbert `Deriv` |

**What `Deriv σ` uniquely *could* accelerate (and whether the roadmap wants it):** metatheorems
that induct on derivation **structure with computational content** — cut-elimination/normalization,
height/subformula induction producing *data*, proof-transformations. **CSLib's completeness is
semantic (canonical model), not proof-theoretic (cut elimination), so the roadmap currently
contains no such consumer.** This is the crux: the substrate's unique value class is empty on the
current roadmap.

**Is metatheory duplication a real recurring cost?** Yes — and it is *already being amortized at
the layer that matters.* The three `GenericMCSBridge.lean` files (Modal 267, Temporal 370, Bimodal
405 ln) are the *bridging cost* of the existing seam, paid once per logic; in exchange the
deduction theorem + MCS closure are written **zero** times per logic. Remaining duplication is
concentrated in (a) per-axiom **soundness** validity (irreducible content, already parameterized)
and (b) **conservativity/Lindenbaum** (tasks 415/407 target this at the Prop/typeclass level). A
Type-level `Deriv σ` substrate does not touch either of these more cheaply than the existing
Prop-level approach.

---

## Highest-Leverage First Metatheorem (the strategic Phase-3 pick)

**Disqualification first:** the brief's implicit favourite — a **generic deduction theorem on
`Deriv σ`** — must be **struck from the candidate list.** GenericMCS already proves it once and
transports it to all six logic configs. Re-proving it on `Deriv σ` behind an R1 refactor is
negative-leverage (new code, new maintenance, zero new reach).

**If Vision B is pursued at all, the only defensible first pick is the generic *soundness
skeleton*:** given a semantic algebra + axiom-soundness + per-closure soundness, derive soundness
of `Deriv σ` once, pull back per logic via the `Equiv`. Rationale: soundness is the one
metatheorem that *genuinely inducts on derivation structure*, and it has the widest per-system
surface (16 Modal systems + Temporal + Bimodal families). It is the maximal-reuse structural
target.

**But even this pick is weak**, and honesty requires saying so: Modal soundness is *already*
parameterized over the axiom predicate (`Modal/Metalogic/Soundness.lean`), so a `Deriv σ`
skeleton would abstract *above* an existing abstraction, and the residual per-axiom validity
proofs (the actual bulk) remain irreducible and un-shared regardless. The net new amortization is
small.

**Strategic recommendation on the metatheorem:** do **not** target a `Deriv σ` metatheorem as the
next move. The genuinely highest-leverage generic-metatheory investment on the current trajectory
is **task 41's completeness scaffold routed through GenericMCS** (Prop-level), plus the
**parametric conservativity-lift framework** flagged by task 415 finding #2 — for which
**Vision A's `Deriv.map` is already the correct cross-system transport primitive.** In other words:
the highest-leverage "first metatheorem" is not on `Deriv σ` at all; it is a completeness/
conservativity scaffold on the *existing* Prop-level seam, with `Deriv.map` supplying the lift.

---

## Scope Alternatives (trajectory-optimal path, incl. de-risking order)

I evaluated four scopings against the trajectory:

1. **All three phases (R1 → backward Equivs → `Deriv σ` metatheorem).** Rejected as lead option.
   Pays R1 + backward-map + round-trip cost across 3 overlays to reach a Phase-3 whose best
   candidate (deduction theorem) is already delivered by GenericMCS and whose only unique-value
   class (structural/proof-theoretic metatheorems) has no roadmap consumer.

2. **Phase 1 only, as enabling infrastructure, defer 2/3.** Rejected. Report 419/04 §5 already
   names this the "subtle mess": R1 without a Layer-3 consumer is plumbing paid for with no payoff.
   Building infrastructure ahead of a consumer that the roadmap does not contain is the classic
   speculative-generality trap.

3. **Invert the order — prove the candidate metatheorem against the EXISTING forward-only layer
   first, to de-risk the ROI gate BEFORE R1.** This is the brief's instinct and it is the *right
   risk posture* — but my analysis lets us discharge the gate **without writing any Lean**: the
   de-risking spike's conclusion is already visible. The flagship candidate is subsumed by
   GenericMCS; the roadmap has no structural-metatheorem consumer; therefore the ROI gate **fails
   at analysis time.** The correct, cheapest execution of "invert to de-risk" is: *do the
   inversion as a paper check (this report), conclude the gate is not met, and do not start R1.*

4. **Keep Vision A permanently; invest genericity effort in the Prop-level seam instead.**
   **Recommended.** Concretely:
   - **Re-frame task 419 from `[BLOCKED]` to forward-complete** (Vision A), with the documented
     scope line (Modal/PL full `Equiv`; Bimodal forward + HEq; backward `Equiv` intentionally out
     of scope). This matches report 419/04 §7.1.
   - **Close task 448 with the verdict: do NOT elevate to a Type-level substrate**; record the
     reason (GenericMCS already occupies the substrate role at the correct level).
   - **Redirect the "shared metatheory" energy to task 41** (completeness scaffold on GenericMCS)
     and **task 415's conservativity-lift framework**, where `Deriv.map` is the ready-made
     cross-system transport. This is where the roadmap actually consumes shared metatheory.

**Trajectory-optimal path (one line):** *Keep Vision A as delivered; decline Vision B's Type-level
substrate; invest the freed effort in extending the existing Prop-level GenericMCS seam for task 41
completeness and task 415 conservativity, using `Deriv.map` as the cross-system lift.*

**Guarded re-entry condition for Vision B:** revisit *only* if a future task introduces a genuinely
**proof-theoretic** obligation that inducts on derivation-as-data (e.g. cut elimination,
normalization, an interpolation construction transported across logics). At that point — and only
then — the de-risking order is: prove the target for **one** logic against a minimal Type-valued
backward map *before* paying R1 across all overlays.

---

## Long-Term / Upstream-Acceptance Considerations

1. **Precedent cuts in Vision B's favour on *pattern*, against it on *duplication*.** GenericMCS
   proves CSLib maintainers **already accept** a Foundations-level "prove once, transport per logic"
   substrate — so the *architecture* is culturally welcome. But that same precedent means a
   **second, parallel** substrate (`Deriv σ`, Type-level) alongside GenericMCS (Prop-level) invites
   the reviewer question *"why two derivation abstractions with two notions of transport?"* Two
   substrates is a coherence and onboarding liability, not an asset.

2. **Contributor onboarding.** A new contributor to CSLib logic metatheory today learns one story:
   tree `DerivationTree` ⇄ algebraic seam ⇄ inherited MCS/deduction. Adding `ProofSig/Deriv/
   ProofSigHom/Deriv.map` *as a metatheory substrate* forces them to learn a second, HEq- and
   large-elimination-laden story with subtle `▸`-cast reasoning (visible in `map_comp`). Kept as a
   **narrow cross-system lifting device** (Vision A), it is opt-in and low-surface; promoted to a
   **substrate**, it becomes load-bearing onboarding cost.

3. **Maintenance surface.** Vision B's R1 changes `Deriv.close`, `clMap`, `Deriv.map`, and the
   three overlays, and adds backward recursions + round-trip proofs per logic — all carrying HEq
   functor-law obligations. Every future closure-carrying logic pays this. GenericMCS's per-logic
   cost is a single `deriv_iff_algebraic` bridge with no HEq. For a community library, lower
   proof-engineering surface per added logic is the correct long-run bias.

4. **Upstream framing that *would* be accepted.** If any `Deriv σ` work goes upstream, frame it
   strictly as *complementary and non-competing*: **`Deriv.map` = cross-proof-system transport
   (lifting)**; **GenericMCS = within-system shared metatheory.** A clear division of labor is
   defensible; a rival second metatheory substrate is not. This framing also lets task 415's
   conservativity-lift work cite `Deriv.map` as the intended transport primitive — a concrete,
   roadmap-anchored upstream justification that pure Phase-1 plumbing lacks.

5. **Zero-debt / reversibility.** Vision A is already sorry-free and self-contained; declining
   Vision B incurs no debt and forecloses nothing (the guarded re-entry condition above keeps the
   door open). This is the low-regret posture for an upstream library.

---

## Confidence Level

**High** on the central strategic claim — that CSLib already possesses the shared-metatheory
substrate (GenericMCS, Prop-level), that it is the trajectory-correct one for the roadmap's
completeness work, and that a Type-level `Deriv σ` substrate would duplicate its flagship result
(deduction theorem) while serving a value class (proof-theoretic/structural metatheorems) absent
from the current roadmap. Grounded directly in `GenericMCS.lean` (the seam), the three
`GenericMCSBridge.lean` files, task 41's own description, and the parameterized Modal soundness.

**Medium** on the precise ranking of the (dispreferred) Phase-3 pick — the soundness skeleton is
the best *structural* target, but its net amortization is small given Modal soundness is already
parameterized; a future proof-theoretic consumer could change the picture.
