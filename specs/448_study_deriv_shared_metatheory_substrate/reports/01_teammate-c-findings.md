# Teammate C Findings — Critic (Task 448)

**Task type**: cslib (research — adversarial critique of the Vision B / `Deriv σ` shared-metatheory-substrate plan)
**Date**: 2026-07-01
**Role**: Critic. Interrogates research quality/completeness of the proposed Phase 1 (R1) → Phase 2 (Equivs) → Phase 3 (ROI gate) programme. All criticisms grounded in current committed source.

---

## Key Findings

1. **The "surgical / non-invasive" claim for Phase 1 is *externally* true but *internally* understated.** `Deriv`/`close`/`ProofSig`/`ProofSigHom` have **exactly four consumers** in the whole tree (the Foundations file + 3 overlays; grep confirms no others — not in tests, not in specs, not in any downstream proof). So there is genuinely **zero external blast radius**. BUT the plan frames Phase 1 as a "one-line representation change," and that is false: the R1 change forces a **full re-proof of the two hardest proofs in the Foundations file** — `map_id` and `map_comp` — which are HEq-heavy and cast-delicate (they lean on `eqRec_heq`, `map_eqRec_heq`, `proof_irrel_heq`, and definitional transparency of the `close` case, `ProofSystemMorphism.lean:232–311`). R1 arguably makes these proofs *harder*, not a mechanical edit (see Assumption A2 below). The "surgical" adjective conflates *small file-count* with *small proof-effort*; only the former holds.

2. **Phase 1 does structurally unblock Phase 2's *backward map*, but the plan mis-attributes the HEq and over-sells the "uniformity" payoff.** `Fin n` is data, so backward dispatch (`ofDeriv`'s `close` case) becomes legal large-elimination-into-`Type` — this part of the plan is correct. HOWEVER: the HEq that pervades the current overlays (`toDeriv_lift`, `toDeriv_liftDerivation`, `toDeriv_liftDerivationTree`) has **nothing to do with the closure witness** — it comes entirely from `Deriv.map`'s context index `Γ.map H.g` vs `Γ` (`List.map_id` is propositional-not-definitional; see the `congr 1; exact (List.map_id Γ).symm` base cases). **R1 will not remove this HEq.** The good news the plan should state but doesn't: the *`Equiv` itself* (`modalEquiv`-style, and the target `bimodalEquiv`) is already HEq-**free** because `toDeriv`/`ofDeriv` preserve the context `Γ` exactly (no functor map). So Phase 2 delivers a clean `bimodalEquiv`, but the "uniformity" is narrower than advertised: the `Deriv.map`-intertwining lemmas stay HEq-bound regardless of R1.

3. **Phase 3 — the ROI gate — is the plan's fatal weakness, and the strongest candidate metatheorem is *already proven generically in CSLib on a different substrate, with live consumers*.** The flagship Phase-3 candidate is the **generic deduction theorem**. CSLib **already has one**: `algebraicDerivationSystem` + `algebraic_has_deduction_theorem` (`Foundations/Logic/Metalogic/GenericMCS.lean`), built on `ListDeriv`, which works "for ANY `MinimalHilbert` proof system, giving a `DerivationSystem` for free … No per-logic induction on proof trees needed" (`ListDeduction.lean:52–57`, `list_deduction_theorem`), and is *actually consumed* by MCS reasoning (`MCSProperties.lean:47,110,125`). A `Deriv σ`-based generic deduction theorem would be a **fourth** parallel derivation abstraction (alongside `DerivationSystem`, `HasHilbertTree`, `algebraicDerivationSystem`) with **no consumer that the existing three don't already serve**.

4. **CSLib has *already mapped the exact generic/concrete boundary* that Phase 3 pretends is unexplored — and it lands against Phase 3.** `DeductionHelpers.lean` defines a `HasHilbertTree` typeclass abstracting the deduction-theorem structure across **PL, Modal, Temporal, and Bimodal**, proving 4 helpers once. Its docstring (`DeductionHelpers.lean:20–22`) states the decisive fact: *"The per-logic `deduction_with_mem` and `deduction_theorem` remain concrete in each logic because they require pattern matching on concrete `DerivationTree` constructors and use `termination_by` on concrete height functions."* This is precisely the wall Phase 3 would hit through the `Equiv`: to consume a generic `Deriv σ` metatheorem, a concrete logic must transport concrete-constructor pattern matches across the equivalence — reintroducing the friction `HasHilbertTree` already shows is irreducible. **CSLib has already run this experiment via typeclasses and found where genericity stops paying.** Phase 3's premise that `Deriv σ` transport is a novel reuse win is contradicted by existing source.

---

## Unvalidated Assumptions (each with evidence / how to test)

**A1 — "Phase 1 touches only Foundations + 3 overlays" ⇒ low risk.**
- *Status*: Half-validated. External consumer set = {`ProofSystemMorphism.lean`, 3× `LiftViaMorphism.lean`} (grep for `ProofSig|Deriv σ|ProofSigHom|bimodalSig|modalEquiv|plEquiv` returns exactly these 4). *But* file-count ≠ effort.
- *Test*: Before committing to R1, spike **only** the `map_comp` `close` case under the `Fin`-indexed `close`. If it does not go through in ≤ the current 6-line proof, the "surgical" framing is refuted.

**A2 — "`Fin` index is strictly cleaner than `List.Mem`."**
- *Evidence against*: The current `close` carries the operator `m : F → F` as a **first-class value** and concludes `Deriv σ [] (m φ)`; `clMap` returns the *operator* `m'` directly, so `map_comp`/`map_id` reason about `m'` as a term. Under R1 the conclusion becomes `Deriv σ [] (σ.closures.get i φ)`, so every closure lemma must now route through `List.get` on **possibly-different-length** lists (`clMap : Fin σ₁.closures.length → Fin σ₂.closures.length`), and `map_comp` must additionally prove index-composition equalities plus `get`-naturality casts. This is *plausibly more* cast machinery, not less.
- *Test*: Write the R1 `Deriv.map` `close` case and attempt `map_id`'s `close` case (currently `congr 1; first | rw[List.map_id] | assumption | exact eq_of_heq …`). Confirm `List.get`/`Fin.cast` do not introduce new `HEq` obligations that the current proof avoids.

**A3 — "`List.get` on the closure list reduces definitionally, so `toDeriv`/`ofDeriv` still typecheck against concrete constructors."**
- *Evidence*: Current Bimodal `toDeriv` produces `.close Formula.box (by simp [bimodalSig]) …` and the conclusion `Formula.box φ` matches `necessitation` definitionally. Under R1, `toDeriv` must produce `.close ⟨0,_⟩ …` with conclusion `(bimodalSig fc).closures.get ⟨0,_⟩ φ`, which must be **defeq** to `Formula.box φ` for the round-trip proofs to close by `rfl`/`simp`.
- *Risk*: `List.get [box,allFuture,swapTemporal] ⟨0,_⟩` reduces for literal index+literal list, but the elaborator's willingness to reduce it *inside a dependent match against the named `necessitation` constructor* is unverified. If it needs `decide`/`Fin.cases` unfolding, the clean `rfl` round-trips (`ofDeriv_toDeriv`, currently `| ax _ _ _ => rfl`) may degrade.
- *Test*: Prototype `bimodalSig`-with-`Fin` `toDeriv`/`ofDeriv` and check `ofDeriv_toDeriv`'s closure cases still close without `decide`.

**A4 — "A generic deduction theorem on `Deriv σ` is a reusable Phase-3 payoff."**
- *Evidence against (strong)*: Already exists generically (`algebraic_has_deduction_theorem`) for the closure-free fragment, and the closure rule `close` only fires at `Γ = []` so it never interacts with context discharge — meaning a `Deriv σ` deduction theorem would be **provable but redundant**: it covers exactly the fragment `algebraicDerivationSystem` already covers, and adds nothing for the closure part. Consumers already route through `ListDeriv`/`HasHilbertTree`.
- *Test*: Name **one** concrete `deduction_theorem` call site in `Logics/` that would be *shorter* routed through a `Deriv σ` generic theorem + `bimodalEquiv` transport than through the existing per-logic proof. If none exists, Phase 3 candidate #1 is dead.

**A5 — "A generic soundness skeleton on `Deriv σ` transports to each logic."**
- *Evidence against*: Soundness is proven per-logic against *incompatible* semantic targets — Kripke frame classes (`Bimodal/.../Soundness/`, `Modal/.../Systems/*/Soundness.lean`), algebraic/Boolean models (`Propositional/Semantics/Algebra/Soundness.lean`), frame-class variants. A generic skeleton needs a generic "semantic algebra + per-closure soundness" input; instantiating that input **is** the per-logic soundness proof. Transport buys nothing.
- *Test*: Sketch the generic skeleton's hypothesis signature; check whether discharging it for Bimodal is smaller than `Soundness/Soundness.lean` today.

**A6 — "Generic height/subformula induction" is a coherent single candidate.**
- *Evidence against*: This conflates two unrelated inductions. Derivation-height induction is *already trivially available* (`Deriv.height` exists, `ProofSystemMorphism.lean:92`). Subformula induction is a property of the **formula algebra `F`**, not of `Deriv σ` — the heavy subformula machinery lives in `Bimodal/Syntax/Subformulas.lean`, `SubformulaClosure.lean`, `Decidability/FMP/*`, none of which `Deriv σ` abstracts. A `Deriv σ` substrate offers nothing here.

---

## Blind Spots & Missing Questions

1. **The plan never asks "is the forward-only layer already sufficient for every current roadmap need?"** Report 04's Vision A says it is, and there is **no identified downstream consumer** demanding a backward `Equiv` or a generic metatheorem. The entire Phase 1–2 investment is speculative infrastructure. The plan should be required to name the *first real consumer* before Phase 1, not after Phase 2 (its own §7.2 gate says "without [Phase 3], do not start Phase 1" — the plan as briefed inverts this by scheduling Phase 1 first).

2. **Maintenance cost of a parallel `Deriv σ` representation is unbudgeted.** CSLib would then carry **four** derivation abstractions (`DerivationTree` per-logic, `DerivationSystem`/`InferenceSystem`, `ListDeriv`/`algebraicDerivationSystem`, `Deriv σ`). Each `Equiv` is a standing proof obligation that must survive future edits to the concrete inductives. The plan quantifies neither the carrying cost nor who consumes `Deriv σ` enough to justify it.

3. **No interaction analysis with the *existing* generic abstractions.** `DerivationSystem`, `HasHilbertTree`, `MinimalHilbert`, `algebraicDerivationSystem` already occupy the "generic proof-system" niche. The plan treats `Deriv σ` as if the niche were empty. The unasked question: *why is `Deriv σ` the right generic substrate rather than extending `DerivationSystem`/`HasHilbertTree`, which already have consumers?* `Deriv σ`'s distinguishing feature is that it carries `close`; but `close`-metatheory (necessitation) is exactly where the deduction theorem and algebraic path already **stop** by design (`GenericMCS.lean:103–109`).

4. **"Zero-debt per-phase buildability" vs cross-phase dependency is untested.** Phase 2's `bimodalEquiv` depends on the R1 signature; Phase 1 must therefore land the R1 refactor *and* re-green `map_id`/`map_comp` *in the same phase* or the overlays break. The claim that each phase is independently buildable is plausible but unverified for the map-law re-proof — the single most likely place a phase lands `[BLOCKED]`.

5. **Report 04 already recommends AGAINST auto-pursuing Vision B** (§7.2: "do not auto-pursue"; "gate Vision B behind a concrete consumer"). Task 448's framing as a "study" is consistent with that, but any plan that schedules R1/Phase-1 work product (not just study) would be acting against the definitive report's own recommendation. The critic's position: **task 448 should terminate at a decision memo, not produce R1 code, unless a concrete consumer is first identified.**

---

## Highest-Risk Failure Modes (ranked)

1. **Land Phases 1–2, discover Phase 3 has no payoff (the "paid-for-plumbing" trap).** Report 04 §5.7 already names this as "the subtle mess to avoid." Evidence now makes it the *likely* outcome: the generic deduction theorem already exists (`algebraic_has_deduction_theorem`); soundness doesn't transport (A5); height/subformula induction is a non-candidate (A6). The realistic end-state is a `Fin`-refactored Foundations file + `bimodalEquiv` with **no generic theorem a concrete logic consumes more cheaply than today**. Probability: high.

2. **Phase 1 `map_comp`/`map_id` re-proof is harder under `Fin` than the plan assumes**, turning "surgical" Phase 1 into a multi-cycle HEq/cast fight (A2, A3). Probability: medium-high. This is where a `[BLOCKED]` would actually surface.

3. **Transport friction defeats any Phase-3 theorem that *is* generic-provable** (deduction theorem): the `HasHilbertTree` docstring evidence (`DeductionHelpers.lean:20`) shows the generic/concrete seam is precisely at concrete-constructor pattern-matching + concrete `termination_by`; the `Equiv` moves that friction, it does not remove it. Probability: high that transport is ≥ direct-proof cost.

4. **Opportunity cost / maintenance drag**: a fourth derivation abstraction with speculative reuse adds standing proof obligations against 204 `DerivationTree` sites' future evolution, for conceptual-unification value the codebase may not cash. Probability: certain if pursued; severity: moderate.

---

## The single question the plan most needs to answer before committing

**Name one concrete theorem, currently proved (or wanted) in `Logics/`, whose proof would be *strictly shorter or newly-possible* when done once on `Deriv σ` and transported via the Equivs — that is NOT already served by `algebraicDerivationSystem` / `HasHilbertTree` / `DerivationSystem`.** If that consumer cannot be named up front, Phases 1–2 are speculative plumbing and task 448 should conclude at "Vision A is the delivered result; Vision B deferred until a consumer exists" — which is exactly report 04's own recommendation.

---

## Confidence Level

**High** on Findings 1–4 and Assumptions A1, A4, A5, A6 (all grounded in read source: the 4-file consumer set, the HEq origin, the pre-existing `algebraic_has_deduction_theorem`/`list_deduction_theorem`, and the `HasHilbertTree` generic/concrete-boundary docstring).
**Medium-high** on A2/A3 and Failure Mode 2 (the map-law re-proof difficulty under `Fin` is a reasoned prediction from reading `map_id`/`map_comp`, not from a compiled prototype — a spike would settle it definitively).
