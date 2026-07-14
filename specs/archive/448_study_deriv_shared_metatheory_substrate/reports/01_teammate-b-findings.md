# Teammate B Findings — Alternatives & Prior Art (Task 448)

**Task type**: cslib (research — read-only; no Lean edits)
**Role**: Teammate B — alternatives / prior-art researcher
**Date**: 2026-07-01
**Ground truth**: `specs/419_.../reports/04_abstract-picture-and-result-inventory.md`;
`Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean`

## Key Findings

1. **CSLib already has a shared-metatheory substrate — at the `Prop` level, and it is load-bearing.**
   The pair `DerivationSystem F` (`Cslib/Foundations/Logic/Metalogic/Consistency.lean:56`) +
   the `InferenceSystem`/`MinimalHilbert…BimodalTMHilbert` typeclass hierarchy
   (`Cslib/Foundations/Logic/InferenceSystem.lean`, `.../ProofSystem.lean`) is exactly a
   "proof system as an abstract consequence relation." On it, the generic **deduction theorem**
   (`GenericMCS.algebraic_has_deduction_theorem`, proved once), **Lindenbaum** (`Consistency.set_lindenbaum`),
   and **MCS closure/implication/negation-completeness** (`SetMaximalConsistent.*`) are already
   established generically. This is Vision B's "Layer 3 prize," *already delivered* for the
   consequence-relation class of metatheorems.

2. **That substrate is consumed by ~30 files across all four logics** (Modal, Temporal, Bimodal,
   Propositional — completeness, MCS, Lindenbaum, deduction theorems), whereas `Deriv σ` /
   `ProofSigHom` / `Deriv.map` is consumed by **exactly 3 files** (the overlays) and **never runs
   backward**. `Deriv σ` is an isolated forward-only lifting device; `DerivationSystem` is the real
   shared substrate.

3. **The proven bridge pattern is `Nonempty`-wrapping, not backward maps.** Every logic joins the
   generic seam via `HilbertOf Axioms` — an empty tag `inductive` whose `InferenceSystem` maps
   closed derivability to `Nonempty (DerivationTree Axioms [] φ)` (`GenericMCS.lean:27-30`). This
   turns a Type-valued derivation tree into the Prop typeclass layer **forward only**, and
   immediately inherits deduction theorem + MCS. No `Equiv`, no backward recursion, no large
   elimination — because everything downstream lives at `Nonempty`/`Prop`.

4. **Mathlib confirms membership-as-data has no generic backward extractor.** The forward direction
   (data → Prop) is free (`List.get_mem`, `List.getElem_mem`, `List.Vector.get_mem`); the backward
   direction (recover an index from `a ∈ l`) exists in Mathlib *only under `[BEq α] [LawfulBEq α]`*
   (`List.idxOf_get`, `List.getElem?_idxOf`). CSLib's generic formula type `F` has no such instance,
   so a generic `List.Mem → Fin` recovery is genuinely unavailable — which is precisely why R1
   must **carry** the index as data rather than recover it. R1 is Mathlib-idiomatic, not ad hoc.

## Alternative Representations (R2, R3, others) — encoding, cost, trade-off

Report 04 §3 gives R1/R2/R3. Extracted and extended:

| Option | Encoding | Lean-level cost | Trade-off vs R1 |
|---|---|---|---|
| **R1** (baseline) | keep `closures : List`; `close` carries `i : Fin σ.closures.length`; `clMap` becomes an index map with naturality | touches Foundations file + 3 overlays; `close`/`clMap`/`Deriv.map` change; Modal/PL proofs get *simpler* | — (the reference) |
| **R2** | `closures : Fin n → (F → F)` (indexed family) as the `ProofSig` field | more invasive: every signature literal restated as a `Fin`-family; no power gain | Strictly worse than R1: same expressiveness, larger blast radius. Mathlib's `List.Vector (F→F) n` (= list + `get : Fin n → α` + `mem_iff_get`) is the packaged version, but still restates each signature. Reject in favor of R1. |
| **R3** | per-signature `ClosureTag` inductive + `op : Tag → (F → F)`; `close` carries a `Tag` | adds a `Type` field to `ProofSig` + a bespoke inductive per logic | Best *ergonomics* (named tags, exhaustiveness on `necessitation`/`temporal_*`), but overkill for ≤3 closures; a `Type` field complicates the functor. Only wins if a logic grows many named closures. |
| **R-store** (new) | `close` stores the chosen operator directly as data with a *Type-valued* membership witness `{ m // m ∈ closures }` promoted to a custom `inductive MemData m closures : Type` (head/tail as data) | one new small inductive; `Deriv.map`/backward case on it | Equivalent to R1 in power (a `Fin`-index and a data-membership witness are isomorphic). More boilerplate than `Fin`; no Mathlib API. R1's `Fin` reuses `List.get`/`getElem`/`Vector` lemmas, so prefer R1. |
| **R-classical** | keep `Prop` membership; backward map via `Classical.choice` | trivial to write | **Trap** (report 04 §2): noncomputable, round-trip `ofDeriv ∘ toDeriv = id` unprovable ⇒ never yields an `Equiv`. Reject. |
| **R-bridge** (the real alternative — see recommendation) | leave `Deriv σ` untouched; add a *forward* `Nonempty`-wrap into the existing `DerivationSystem`/`InferenceSystem` seam | ~1 tag + 1 `InferenceSystem` instance + 1 `MinimalHilbert` instance, mirroring `HilbertOf` | Delivers the shared-metatheory ROI (deduction theorem, MCS) for `Deriv σ` **without R1**, because it never runs backward. Only covers consequence-relation-level metatheorems (not data-structural ones). |

Design-space note: R1/R2/R3/R-store are four spellings of the same fix — **make the closure choice
`Type`-valued data.** They differ only in ergonomics and Mathlib-API leverage; R1 maximizes both.
R-classical and R-bridge are categorically different: R-classical fakes the backward map (reject),
R-bridge *avoids needing it* (the genuine contender).

## Prior Art (Mathlib lemmas + CSLib/existing formalizations, with names)

**Mathlib — membership-as-data (verified via loogle/leansearch):**
- `List.mem_iff_get` — `a ∈ l ↔ ∃ n, l.get n = a` (Init.Data.List.Lemmas). **Prop existential** — the
  `∃ n` cannot be eliminated into `Type`; documents the wall, does not cross it.
- `List.mem_iff_getElem` — `a ∈ l ↔ ∃ i, ∃ (h : i < l.length), l[i] = a`. Same: Prop bridge only.
- `List.get_mem` / `List.getElem_mem` / `List.Vector.get_mem` (`v.get i ∈ v.toList`) — **forward
  data → Prop, free.** These are what R1 uses to discharge the membership side-condition after
  carrying the `Fin` index.
- `List.idxOf_get` — `l.get ⟨idxOf a l, h⟩ = a` **requires `[BEq α] [LawfulBEq α]`.**
- `List.getElem?_idxOf` — `a ∈ l → l[idxOf a l]? = some a`, **requires `[LawfulBEq α]`.**
- `List.Vector α n` (`= list + get : Fin n → α`, with `List.Vector.mem_iff_get`) — Mathlib's packaged
  "container indexed by `Fin`," i.e. the R2 encoding with library support.

  **Conclusion from Mathlib**: there is *no* generic lemma eliminating `x ∈ l` into `Type`; the
  sanctioned idiom is to represent the choice as `Fin l.length` data and relate it to membership via
  the `*_mem`/`mem_iff_getElem` bridges. Index recovery from membership exists only with decidable
  equality. This exactly matches, and vindicates, R1.

**CSLib — existing generic-deduction / proof-system-as-algebra formalizations (the decisive prior art):**
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` — `DerivationSystem F` structure (abstract
  consequence relation `Deriv : List F → F → Prop` + weakening/assumption/mp); generic `Consistent`,
  `SetMaximalConsistent`, `set_lindenbaum`, `HasDeductionTheorem`, `SetMaximalConsistent.{closed_under_derivation, implication_property, negation_complete}`.
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` — `algebraicDerivationSystem` built once from
  `ListDeriv` for **any** `MinimalHilbert S`; `algebraic_has_deduction_theorem` (generic deduction
  theorem); the `predicate → type → seam` bridge via `HilbertOf Axioms` + `Nonempty (DerivationTree …)`.
- `Cslib/Foundations/Logic/Metalogic/{ListDeduction,SetDeduction}.lean` — generic list/set deduction
  theorem, cut, monotonicity over `[InferenceSystem S F] [MinimalHilbert S]`.
- `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` — full loop
  `MinimalHilbert ⟺ HasDeductionTheorem` (`dt_minimal_hilbert`, `minimal_hilbert_has_deduction_theorem`).
- `Cslib/Foundations/Logic/{InferenceSystem,ProofSystem}.lean` — `InferenceSystem S α` derivation
  functor + `ModusPonens`/`Necessitation` + `MinimalHilbert…BimodalTMHilbert` bundled Hilbert classes.
- Reach: `DerivationSystem` is consumed by ~30 files across Modal/Temporal/Bimodal/Propositional
  (completeness, MCS, Lindenbaum, deduction). Bimodal already plugs in at any frame class via
  `HilbertTMFc fc` (`Bimodal/Metalogic/Core/GenericMCSBridge.lean`).
- Isabelle antecedent cited in-repo: `Propositional_Logic_Class.thy` (`list_deduction_logic`),
  referenced by `GenericMCS.lean:81`.

**Mathlib — proof-system-morphism analogues** (already noted in `ProofSystemMorphism.lean:39-41`):
`FirstOrder.Language.LHom` (signature-morphism half); `CategoryTheory` free constructions. No
free-multicategory / generic-derivation-functor library exists in Mathlib — CSLib's `DerivationSystem`
seam is the closest working analogue and it is home-grown.

## Recommended Approach (ranked: does anything beat R1?)

**Ranking depends entirely on which Layer-3 metatheorems Vision B intends to consume — and prior art
splits them into two classes:**

1. **RANK 1 — R-bridge beats R1 for consequence-relation-level metatheorems** (deduction theorem,
   MCS/Lindenbaum, cut, weakening, "soundness as a Prop"). These **already exist generically** on
   `DerivationSystem`/`InferenceSystem`. If the goal is to let `Deriv σ` share them, the minimal,
   sorry-free, computable move is a **forward `Nonempty`-wrap of `Deriv σ` into the existing seam**
   (clone the `HilbertOf` pattern), *not* R1's backward-map refactor. It touches ~1 tag + 2 instances,
   never runs backward, and inherits the whole MCS machinery. **For this class, R1 is unnecessary
   plumbing** — precisely report 04 §5's "subtle mess" (R1 + Equivs with no data-structural consumer).

2. **RANK 2 — R1 is correctly chosen, but only for data-structural metatheorems.** If (and only if)
   a concrete goal needs Type-valued structural recursion *out of* a derivation and transported
   *bidirectionally* between native trees and `Deriv σ` (height/subformula induction producing a new
   tree, computable proof transformation, cut-elimination, a genuine `Equiv`), then the `Prop` seam
   cannot express it and R1 is required. Among the data encodings (R1/R2/R3/R-store) **R1 wins**:
   `Fin`-index reuses Mathlib's `List.get`/`getElem`/`Vector` + `getElem_mem` API, is least invasive
   (`ProofSig` field unchanged), and makes Modal/PL uniform. R2/R3/R-store are strictly dominated;
   R-classical is a trap.

3. **RANK 3 — reject** R-classical, A2 inductive-replacement, and `Prop`-axiom Bimodal (report 04 §5).

**Net recommendation.** *Nothing beats R1 within the data-encoding family — R1 is the right choice
there.* But the strongest **alternative to needing R1 at all** is the R-bridge: CSLib's own,
in-use, ~30-consumer `DerivationSystem` seam already realizes the shared-metatheory substrate for
every consequence-relation metatheorem, via forward `Nonempty`-wrapping and never a backward map.
So Vision B should be split: **(a)** for deduction/MCS-style results, bridge `Deriv σ` forward into
the existing seam (no R1); **(b)** reserve R1 strictly for a *named* data-structural consumer, and do
not spend it speculatively. This is the prior art that most reduces risk: it shows the "prize" is
largely already banked, and pinpoints the narrow residue where R1 actually earns its cost.

## Confidence Level

**High** for the prior-art claims (all CSLib declarations read in source; Mathlib lemma
signatures verified via loogle/leansearch). **High** that R1 dominates R2/R3/R-store within the
data-encoding family. **Medium-high** that R-bridge beats R1 for the metatheorems Vision B is likely
to want — contingent on the (still-unnamed) Layer-3 consumer: if that consumer turns out to be
data-structural, R1 is back on top. Recommend the team's primary-approach teammate confirm whether
any intended Layer-3 metatheorem is data-structural before committing to R1.
