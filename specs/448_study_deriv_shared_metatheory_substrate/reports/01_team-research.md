# Research Report: Task #448 — Study Deriv σ as a shared-metatheory substrate (Vision B)

**Task**: Study Deriv σ as a shared-metatheory substrate (proof-system morphism Vision B)
**Date**: 2026-07-01
**Mode**: Team Research (4 teammates: Primary, Alternatives, Critic, Horizons)
**Task type**: cslib (Lean 4 formal metatheory) · **Parent**: task 419
**Ground truth**: `specs/419_generalize_derivation_lifting_intersystem/reports/04_abstract-picture-and-result-inventory.md`; `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean`

---

## Summary

**Verdict: DO NOT elevate `Deriv σ` into a Type-level shared-metatheory substrate now. Conclude task 448 as a decision memo: keep Vision A (`Deriv.map`, delivered by 419) as a complementary cross-system lifting device; decline Vision B's substrate; redirect the "shared metatheory" effort to the *existing* Prop-level seam (GenericMCS) via task 41 and task 415.**

The research is unusually convergent on the decision even though the four angles started independently. Two facts settle it:

1. **The R1 mechanic works, but the ROI gate fails at analysis time.** Teammate A *empirically compiled* the R1 core (a `Fin (closures.length)`-indexed `close` with forward+backward maps into a Type-valued inductive and a sorry-free round-trip — zero diagnostics), confirming the large-elimination wall genuinely dissolves. So Phases 1–2 are *feasible*. But Phase 3 — the explicit ROI gate the task itself says must be met before landing Phases 1–2 — has **no consumer**.

2. **CSLib already has a shared-metatheory substrate, at the correct (Prop) level.** Teammates B, C, and D each independently discovered that `Foundations/Logic/Metalogic/GenericMCS.lean` ("the algebraic seam") already proves the generic **deduction theorem** once (`algebraic_has_deduction_theorem` / `list_deduction_theorem`) on the abstract `DerivationSystem F` consequence relation, and transports it — plus Lindenbaum and full MCS closure — to **all six logic configurations** (PL, Modal, Temporal-Base/fc, Bimodal-Base/fc) via per-logic `GenericMCSBridge.lean`. This substrate is consumed by ~30 files. It never hits the large-elimination wall precisely because it lives at `Nonempty (DerivationTree …)` / Prop, not Type. Vision B's flagship Phase-3 candidate (a generic deduction theorem on `Deriv σ`) is therefore **already delivered** — re-proving it at the Type level behind an R1 refactor is duplication, not leverage.

This matches report 419/04's own recommendation (§7.2: "do not auto-pursue"; gate Vision B behind a concrete consumer).

---

## Key Findings

### Points of unanimous agreement (high confidence, source-grounded)

- **R1 dissolves the blocker.** Re-indexing `Deriv.close` by `Fin σ.closures.length` (data) makes backward dispatch legal large-elimination-into-`Type`. Teammate A compiled a faithful mini-model sorry-free (`lean_run_code`, zero diagnostics). Teammate B confirms `Fin`-indexing is the Mathlib-idiomatic encoding (index recovery from `a ∈ l` needs `[LawfulBEq α]`, which CSLib's generic `F` lacks — so R1 must *carry* the index, exactly as Mathlib's `List.Vector`/`get`/`getElem_mem` idiom does).
- **External blast radius of Phase 1 is exactly zero.** Both A and C exhaustively grepped `Cslib/`: only **4 files** reference `ProofSystemMorphism`/`Deriv.map`/`clMap`/`ProofSigHom` — the Foundations file plus the three `LiftViaMorphism.lean` overlays (Modal, PL, Bimodal). No native `DerivationTree` inductive is touched. The anti-goal A2 (maximal inductive replacement, ~193 files) is correctly avoided.
- **Within the data-encoding family, R1 is the right choice.** Teammate B ranked R1 > R2 (indexed-family, restates every signature) > R3 (per-logic tag inductive, adds a Type field) > R-store (custom data-membership inductive, no Mathlib API); R-classical (Classical.choice) is a trap (noncomputable, round-trip unprovable). Nothing in the data-encoding family beats R1.

### The decisive finding — the substrate already exists (B + C + D, independently)

- `GenericMCS.lean` = `algebraicDerivationSystem` built once for **any** `MinimalHilbert S`, with `algebraic_has_deduction_theorem` proved once and inherited by all logics; logics join via `HilbertOf Axioms` + `Nonempty (DerivationTree …)` — a **forward** `Nonempty`-wrap, no backward map, no `Equiv`, no large elimination.
- CSLib has **already mapped the generic/concrete boundary** Phase 3 assumes is unexplored. `DeductionHelpers.lean`'s `HasHilbertTree` typeclass docstring states the per-logic deduction theorems "remain concrete … because they require pattern matching on concrete `DerivationTree` constructors and use `termination_by` on concrete height functions" — i.e. the exact friction a `Deriv σ` generic theorem would re-incur *through the Equiv*. Transport friction ≥ direct-proof cost.
- The roadmap's remaining work is **semantic completeness** (canonical model), which is Prop/MCS-shaped: task 41 ("abstract shared completeness infrastructure") explicitly extends GenericMCS; tasks 36/37/39/40 (discrete/continuous/dense completeness) consume derivability facts already shared. **CSLib has no proof-theoretic / structural-metatheorem consumer** (cut-elimination, normalization, interpolation-by-construction) — which is the *only* value class a Type-valued `Deriv σ` substrate uniquely serves.

---

## Synthesis

### Conflicts found and resolved

**Conflict 1 (decisive) — the Phase-3 flagship consumer.**
- *Teammate A*: recommends the **generic deduction theorem** on `Deriv σ` as the strongest Phase-3 consumer (vacuous `close` case, transports to three logics, no new semantic infrastructure); rates Phase 3 MEDIUM-HIGH.
- *Teammates B, C, D*: the generic deduction theorem **already exists** in CSLib (`algebraic_has_deduction_theorem`/`list_deduction_theorem`, GenericMCS.lean), on the Prop-level seam, consumed by ~30 files across all logics; a `Deriv σ` version is a redundant fourth derivation abstraction.
- **Resolution → B/C/D.** Three independent, source-grounded refutations (each citing the actual declarations and their consumers) decisively outweigh A's textbook appeal. Notably A *itself* flagged Phase 3 as "the only phase with genuine cost and genuine risk" and rated it below Phases 1–2 — the disagreement is not about A's Lean craft (which is excellent and unchallenged) but about whether the chosen consumer books real ROI. It does not.

**Conflict 2 — the HEq attribution.**
- *Teammate A*: implies R1 removes the HEq that pervades the Bimodal overlay and delivers "uniformity."
- *Teammate C* (corrective): the overlay HEq comes from `Deriv.map`'s context index `Γ.map H.g` vs `Γ` (`List.map_id` is propositional, not definitional) — **not** from the closure witness. R1 does not remove it. The good news C adds: the target `bimodalEquiv` itself is already HEq-free because `toDeriv`/`ofDeriv` preserve `Γ` exactly. 
- **Resolution → C.** C's account is the technically precise one; A's Phase-2 `Equiv` mechanic still stands (the `Equiv` is clean), but the "uniformity payoff" is narrower than A framed — the `Deriv.map`-intertwining lemmas stay HEq-bound regardless of R1.

**Conflict 3 — "surgical" Phase 1.**
- *Teammate A*: Phase 1 is mechanical; the functor-law `close` cases get *simpler* (Fin equality vs proof irrelevance); HIGH confidence.
- *Teammate C*: file-count is small (true) but proof-effort is understated — `map_id`/`map_comp` are HEq/cast-delicate and routing closures through `List.get` on different-length lists *plausibly* makes them harder; a spike is needed to settle it.
- **Resolution → unresolved but moot.** This is a genuine open empirical question (A compiled the *core mechanic* but not the actual `map_comp` re-proof against the committed source). It is **moot for the decision**: since the ROI gate fails, Phase 1 should not be attempted regardless of whether it is 1 cycle or 3. If Vision B is ever revived, C's proposed spike (re-prove *only* `map_comp`'s `close` case under `Fin`) is the correct first gate.

### Gaps identified

- **No named consumer.** The single question all four converge on (C states it as the gating question; A implicitly answers "deduction theorem" and is refuted): *name one theorem in `Logics/`, currently proved or wanted, whose proof is strictly shorter or newly-possible done once on `Deriv σ` and transported via the Equivs, that is NOT already served by `algebraicDerivationSystem`/`HasHilbertTree`/`DerivationSystem`.* No teammate could name one. Until one exists, Phases 1–2 are speculative plumbing.
- **B's R-bridge — a cheaper path if consequence-relation sharing is ever wanted for `Deriv σ`.** If some future need arises to give `Deriv σ` the deduction-theorem/MCS results *without* a data-structural requirement, the minimal move is a **forward `Nonempty`-wrap of `Deriv σ` into the existing seam** (clone the `HilbertOf` pattern: ~1 tag + 2 instances), never R1. R1 is only justified by a *data-structural* consumer (new-tree-producing induction, cut-elimination, a genuine Type-level `Equiv`).

---

## Recommendations

1. **Close task 448 with the verdict: decline Vision B's Type-level substrate.** Record the reason: CSLib already occupies the shared-metatheory-substrate role at the correct (Prop) level via `GenericMCS`, and the roadmap's open work consumes *that* substrate, not a Type-valued derivation algebra. This is report 04's own recommendation, now confirmed against source by three independent angles.
2. **Keep Vision A (`Deriv.map`) as delivered and complementary.** Frame it strictly as **cross-proof-system transport (lifting)** — the one thing GenericMCS does *not* do — versus GenericMCS = **within-system shared metatheory**. A clear division of labor is upstream-defensible; a rival second substrate is not.
3. **Redirect the effort to where the roadmap actually consumes shared metatheory:**
   - **Task 41** — abstract shared completeness scaffold, routed through GenericMCS (Prop-level), as task 41's own description already mandates.
   - **Task 415** — parametric conservativity-lift framework, for which `Deriv.map` (Vision A) is the ready-made cross-system transport primitive (a concrete, roadmap-anchored upstream justification that pure Phase-1 plumbing lacks).
4. **Do NOT start R1 / Phase 1 work product.** Per the task's own gate ("do NOT land Phases 1–2 without Phase 3") and report 04 §7.2, no code should be written for Vision B absent a concrete consumer.
5. **Guarded re-entry condition (keep the door open, zero-debt).** Revisit Vision B *only* if a future task introduces a genuinely **proof-theoretic** obligation that inducts on derivation-as-data (cut elimination, normalization, interpolation-by-construction transported across logics). At that point the de-risking order is: prove the target for **one** logic against a minimal Type-valued backward map **before** paying R1 across all three overlays. R1 remains the correct data-encoding when that day comes; A's compiled mini-model and C's `map_comp` spike are the ready starting points.

**Net**: Vision A is sorry-free, self-contained, and complementary; declining Vision B incurs no debt and forecloses nothing. This is the low-regret posture for an upstream community library.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Core contribution |
|----------|-------|--------|------------|-------------------|
| A | Primary (R1 + phases) | completed | HIGH (Ph1-2), MED-HIGH (Ph3) | Empirically compiled the R1 mechanic sorry-free; confirmed 4-file containment; phase-by-phase Lean sketches. Proposed consumer (deduction theorem) refuted by B/C/D. |
| B | Alternatives / prior art | completed | HIGH (prior art), MED-HIGH (R-bridge) | R1 dominates R2/R3/R-store; Mathlib membership-as-data grounding; discovered the existing `DerivationSystem`/GenericMCS substrate (~30 consumers); proposed the R-bridge forward-wrap. |
| C | Critic | completed | HIGH (findings 1-4) | Corrected the HEq attribution; showed the generic deduction theorem already exists with live consumers; `HasHilbertTree` docstring shows transport friction is irreducible; framed the single gating question. |
| D | Horizons | completed | HIGH (central claim) | Reframed the whole decision: GenericMCS *is* the substrate, at the correct Prop level; roadmap (tasks 41, 36-40, 415) is Prop/MCS-shaped; trajectory-optimal path = decline Vision B, invest in task 41 + 415. |

**Conflicts found**: 3 · **Resolved**: 3 (Conflict 3 resolved as *moot* given the gate verdict) · **Wave 2 triggered**: no (convergence achieved in one wave).

---

## References

**Ground-truth reports**
- `specs/419_generalize_derivation_lifting_intersystem/reports/04_abstract-picture-and-result-inventory.md` — fork framing (Vision A/B), R1/R2/R3, result lattice Layers 0-3, §5.7 "subtle mess", §7.2 gate recommendation.
- `specs/419_.../reports/{01,02,03}` — spike history and structural verdict.

**Source files cited (committed)**
- `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` — `Deriv.close` Prop membership (:82), `clMap` (:137-138), `Deriv.height` (:92), `map_id`/`map_comp` (:232-311).
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — `algebraicDerivationSystem`, `algebraic_has_deduction_theorem`, `HilbertOf` + `Nonempty (DerivationTree …)` seam (:27-30, :81, :103-109).
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — `DerivationSystem F` (:56), Lindenbaum, MCS properties.
- `Cslib/Foundations/Logic/Metalogic/{ListDeduction,SetDeduction,DeductionCharacterization}.lean` — generic list/set deduction theorem, `MinimalHilbert ⟺ HasDeductionTheorem`.
- `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` — `HasHilbertTree` typeclass + generic/concrete-boundary docstring (:20-22).
- `Cslib/Foundations/Logic/{InferenceSystem,ProofSystem}.lean` — `InferenceSystem`, `MinimalHilbert…BimodalTMHilbert` hierarchy.
- `Cslib/Logics/{Modal,Propositional,Bimodal}/.../LiftViaMorphism.lean` — the three overlays; Bimodal documents the obstruction and names `Fin n → F` indexing as the fix (:41-50).
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean` — `liftFormula`/`liftAxiom`/`liftDerivationWith` (:562-636).
- Per-logic `Cslib/Logics/*/Metalogic/**/GenericMCSBridge.lean` (Modal, Temporal, Bimodal).

**Mathlib**
- `List.get_mem`/`List.getElem_mem`/`List.Vector.get_mem` (forward data→Prop, free); `List.mem_iff_get`/`mem_iff_getElem` (Prop bridge only); `List.idxOf_get`/`getElem?_idxOf` (recovery, requires `[LawfulBEq α]`); `List.Vector α n` (packaged Fin-indexed container).

**Adjacent tasks referenced**: 41 (shared completeness scaffold), 415 (conservativity-lift audit), 407 (MPL structure-first), 36/37/39/40 (completeness).
