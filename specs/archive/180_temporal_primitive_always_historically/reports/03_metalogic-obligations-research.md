# Research Report: Metalogic Obligations for Primitive allFuture/allPast (Task 180)

- **Task**: 180 — temporal_primitive_always_historically
- **Started**: 2026-06-30
- **Completed**: 2026-06-30
- **Effort**: hard (CSLib research, H2/H3/H4)
- **Dependencies**: None (build-exclusive on a green Temporal tree)
- **Sources/Inputs**:
  - `specs/180_temporal_primitive_always_historically/reports/01_primitive-always-historically-research.md` (settled design)
  - `specs/180_temporal_primitive_always_historically/reports/02_implementation-attempt-status.md` (parked attempt)
  - `specs/180_temporal_primitive_always_historically/plans/01_primitive-gh-implementation.md` (8-phase plan, [PARTIAL])
  - `specs/180_temporal_primitive_always_historically/wip/01_primitive-gh-wip.patch` (1063-line WIP, not applied)
  - Live source at HEAD `8833bbd3`: `Cslib/Logics/Temporal/{Syntax,Semantics,ProofSystem,Metalogic}/...`
- **Artifacts**: `reports/03_metalogic-obligations-research.md` (this file)
- **Standards**: report-format.md; cslib.md; lean4.md; anti-analysis.md (H2); reference-grounding.md (H3)

## Executive Summary

The un-reached Metalogic layer has a single root cause of breakage, and the settled WIP already
encodes the fix mechanism. **Every metalogic break traces to one fact**: today `𝐆φ` is the
*definitional abbreviation* `¬𝐅¬φ` (`Formula.allFuture φ := .neg (.someFuture (.neg φ))`,
`Formula.lean:140`), so dozens of MCS/Chronicle proofs silently rely on the **defeq**
`𝐆φ ≡ ¬(𝐅¬φ)` when they call `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`, or `change`.
Promoting `allFuture`/`allPast` to constructors destroys that defeq, so those steps stop
type-checking — the proofs do not become *false*, they become *disconnected*.

The WIP patch's chosen repair (verified by reading the patch) is to add **four bridge axioms** to
the `Axiom` inductive — `allFuture_to_classic`, `classic_to_allFuture`, `allPast_to_classic`,
`classic_to_allPast` — i.e. `⊢ 𝐆φ → ¬𝐅¬φ` and `⊢ ¬𝐅¬φ → 𝐆φ` (and past duals). This is not a
convenience: I verified adversarially that **neither direction of `𝐆φ ↔ ¬𝐅¬φ` is derivable from
the existing BX axioms once G is primitive** (the axiom set constrains G only through
`left_mono_until_G`/`right_mono_until`/`connect_future`/`density` + necessitation, none of which
can introduce a primitive `𝐆` from a U/S hypothesis). So the bridge axioms are **necessary for
completeness**, and the task's "classical equivalences become theorems" deliverable is satisfied
by these axioms (a theorem derivable in one `.axiom` step) — see Decisions D3 for the honesty
caveat.

Given the bridge axioms exist from the ProofSystem layer onward, the metalogic repair reduces to
two reusable MCS lemmas (`mcs_allFuture_iff`, `mcs_allPast_iff`) plus **case-by-case rewrites at
the defeq break sites** — no new canonical-model construction is required. The Truth Lemma's two
new inductive cases (`allFuture`, `allPast`) can be discharged by a **reduction strategy** that
reuses the *already-proven* standalone `truth_lemma_untl_*`/`truth_lemma_snce_*`/`truth_lemma_imp`
case lemmas — again, **no new chronicle-frame coherence lemma is needed**. This substantially
de-risks the plan's "highest-risk, largest" Phase 6.

## Context & Scope

Settled by report 01 and the WIP (do not re-litigate): the constructor set, structural semantics
`Sat t 𝐆φ ↔ ∀ s, t<s → Sat s φ` (`Satisfies.lean:151` `allFuture_iff` will become definitional),
`swapTemporal` duality, and the Syntax/Semantics/ProofSystem/Tableau edits (WIP touches these 7
files). This report addresses **only** the four metalogic targets in the FOCUS block: Soundness,
MCS/Chronicle/TruthLemma, Completeness, and the classical-equivalence placement.

Read budget: 6 source files fully read + 4 targeted greps before first concrete output;
< 20% of tool calls (H2 compliant).

## Findings

### F0 — BibKey grounding (H3)

`references.bib` (repo root, 32 KB) contains **no** entry for Boudou, Diéguez & Fernández-Duque.
`grep -in "boudou\|dieguez\|fernandez\|intuitionistic temporal"` returns nothing. **No verified
BibKey exists.** Per H3 protocol, cite by full reference and flag for addition:

> Boudou, J., Diéguez, M., & Fernández-Duque, D. (2017). *A decidable intuitionistic temporal
> logic.* Proc. CSL 2017. **[BibKey to be added — suggested `Boudou2017`]**

The Boudou et al. framework is the *motivation* (independent primitive G and F), not a source of
proof steps transcribed here; the metalogic obligations below are dictated by the CSLib source
structure, not the paper. Relevance is thus limited to justifying why G/H must be primitive
(report 01 §"Intuitionistic Temporal Logic Background"). This is a **Tier 1** task by
classification, but with a **degenerate literature dependency** — the paper supplies design
rationale, and the actual proof obligations are code-driven (Tier 3-like). The
source-to-implementation mapping (below) is therefore keyed to Lean targets, not paper theorems.

### F1 — Root cause: the `𝐆φ ≡ ¬𝐅¬φ` defeq is load-bearing across the metalogic

`Formula.allFuture φ := .neg (.someFuture (.neg φ))` (`Formula.lean:140-141`), so `𝐆φ` and
`¬𝐅¬φ` are *the same term*. The metalogic exploits this defeq at these concrete sites (each will
fail to type-check when `allFuture` becomes an opaque constructor):

| Site | File:line | Defeq used | Why it breaks |
|------|-----------|-----------|---------------|
| `mcs_g_mp` | `MCS.lean:169-170` | `(mcs_mem_iff_neg_not_mem).mpr (h : 𝐆ψ∉Ω) : 𝐅¬ψ∈Ω` needs `¬(𝐅¬ψ)=𝐆ψ` | `.mpr` no longer unifies `¬(𝐅¬ψ)` with primitive `𝐆ψ` |
| `mcs_g_witness` final | `MCS.lean:374` | `mcs_not_mem_of_neg h_g_bot (h_f_top)` needs `𝐆⊥ = ¬𝐅⊤` | `𝐆⊥` opaque ≠ `¬(𝐅¬⊥)` |
| `mcs_h_mp` / `mcs_h_witness` | `MCS.lean:229-230,472-474` | past duals of the above | same |
| `someFuture_allFuture_neg_absurd` | `WitnessSeed.lean:53` | `mcs_not_mem_of_neg h_G_neg h_sf_nn` needs `𝐆(¬ψ)=¬(𝐅¬¬ψ)` | opaque `𝐆(¬ψ)` ≠ `¬(𝐅¬¬ψ)` |
| `somePast_allPast_neg_absurd` | `WitnessSeed.lean:65` | past dual | same |
| `Seeds.lean` seed builder | `Seeds.lean:54` (comment "definitionally allFuture φ ∈ A") | membership converted by defeq | needs bridge |
| `Structures.lean` | `Structures.lean:157` `change Formula.allFuture φ ∈ A` | `change` across the defeq | `change` fails |
| `RRelation.lean` duality helpers | `RRelation.lean:479-515` (`neg_allPast_neg_to_somePast`, `neg_allFuture_neg_to_someFuture`) | consume `¬(𝐆¬γ)∈M` and produce `𝐅γ` | input pattern `¬(𝐆¬γ)` no longer defeq to anything U/S; needs bridge to re-enter |

`someFuture_allFuture_neg_absurd` is the **highest-leverage** site: it is the "future coherence"
contradiction lemma consumed all over the Chronicle (`OrderedSeedConsistency.lean:127`,
`Splitting.lean:643,660`, `Structures.lean:186`). Repairing it once fixes the largest fan-out.

### F2 — The settled repair: four bridge axioms (already in the WIP)

Reading `01_primitive-gh-wip.patch` confirms the design decision: it adds to `Axiom`
(`Axioms.lean`, after `dense_indicator`):

```lean
| allFuture_to_classic (φ : Formula Atom) :
    Axiom (φ.allFuture.imp (Formula.neg (Formula.someFuture (Formula.neg φ))))
| classic_to_allFuture (φ : Formula Atom) :
    Axiom ((Formula.neg (Formula.someFuture (Formula.neg φ))).imp φ.allFuture)
| allPast_to_classic  (φ : Formula Atom) :
    Axiom (φ.allPast.imp (Formula.neg (Formula.somePast (Formula.neg φ))))
| classic_to_allPast  (φ : Formula Atom) :
    Axiom ((Formula.neg (Formula.somePast (Formula.neg φ))).imp φ.allPast)
```

All four have `minFrameClass = .Base` (the `_ => .Base` fallback at `Axioms.lean:233` already
covers them — verify no explicit arm is needed). The WIP also rewires the `Instances.lean`
typeclass instances (`HasAxiomLeftMonoUntilG`, etc.) to route through `classic_to_allFuture`,
which is the correct pattern.

**Necessity (adversarially verified, F1→F2 justification):** With G primitive, the only ways to
introduce `𝐆X` in a derivation are (i) `temporal_necessitation` from `⊢X`, (ii) `connect_future`
`X→𝐆𝐏X`, (iii) `density` `𝐆𝐆φ→𝐆φ`, and the mono axioms which have `𝐆(…)` in the *antecedent*.
None can conclude a primitive `𝐆φ` from a U/S premise such as `¬𝐅¬φ`. Hence `¬𝐅¬φ→𝐆φ` is
**underivable** without `classic_to_allFuture`. Symmetrically `𝐆φ→¬𝐅¬φ` needs
`allFuture_to_classic` (the G-distribution route `mcs_g_mp` is itself circular once the defeq is
gone). The bridge axioms are therefore **mandatory for completeness**, not optional sugar.

### F3 — Per-file Metalogic obligation table (core deliverable)

Legend: **Reuse** = existing verified lemma (file:line read); **New** = to be proved (verified
absent by grep).

| File | What changes | New / repaired lemma(s) | Concrete sketch / reuse candidate |
|------|--------------|-------------------------|-----------------------------------|
| `Semantics/Satisfies.lean` | `allFuture_iff`/`allPast_iff` (`:151`,`:165`) become definitional (`simp only [Satisfies]`); add semantic bridge | **New** `sat_allFuture_iff_neg_someFuture_neg : Sat M t (𝐆φ) ↔ Sat M t (¬𝐅¬φ)` | From `allFuture_iff` + `someFuture_iff` + `Classical.not_exists`/`not_not`. Same content as F5 soundness cases. |
| `Metalogic/Soundness.lean` | `axiom_sound` (`:75`) is a `match`; add **4 arms** for the bridge axioms | 4 new match arms (no named lemmas) | See F5. Reuse `Satisfies.allFuture_iff` (already used at `:408`), `someFuture_iff` (`:87` usage pattern at `:267`). |
| `Metalogic/DenseSoundness.lean` | Same `match` extended (dense soundness re-dispatches Base axioms) | mirror 4 arms or delegate to `axiom_sound` | Check whether DenseSoundness re-matches or calls Base; add arms only where it re-matches. |
| `Metalogic/MCS.lean` | Repair `mcs_g_mp`/`mcs_h_mp`/`mcs_g_witness`/`mcs_h_witness`/`derive_g_contradiction`/`derive_h_contradiction` defeq sites (F1) | **New** `mcs_allFuture_iff`, `mcs_allPast_iff` (single reusable bridge-in-MCS lemmas) | See F6. Then replace each broken `mcs_not_mem_of_neg`/`mcs_mem_iff_neg_not_mem` step with a rewrite through these. |
| `Metalogic/WitnessSeed.lean` | Repair `someFuture_allFuture_neg_absurd` (`:43`), `somePast_allPast_neg_absurd` (`:55`) | rewrite via `mcs_allFuture_iff` | Convert `h_G_neg : 𝐆(¬ψ)∈M` to `¬(𝐅¬¬ψ)∈M` before the final `mcs_not_mem_of_neg`. Fixes fan-out to Chronicle. |
| `Metalogic/Chronicle/RRelation.lean` | `neg_allFuture_neg_to_someFuture` (`:499`), `neg_allPast_neg_to_somePast` (`:479`) inputs `¬(𝐆¬γ)∈M` | insert `mcs_allFuture_iff` to re-enter U/S world | The DNE + `right_mono_until` body (`:503-515`) is unchanged; only the entry membership needs the bridge. |
| `Metalogic/Chronicle/PointInsertion/Seeds.lean` | `:54` "definitionally allFuture φ ∈ A" conversion; `:92-113` G-DNE seed steps | replace defeq conversion with `mcs_allFuture_iff` | Steps already use `right_mono_until`+necessitation explicitly; only the defeq membership hop breaks. |
| `Metalogic/Chronicle/CounterexampleElimination/Structures.lean` | `:157` `change Formula.allFuture φ ∈ A` | replace `change` with `(mcs_allFuture_iff …).mp/.mpr` | `change` across defeq is exactly the pattern that dies. |
| `Metalogic/Chronicle/OrderedSeedConsistency.lean`, `PointInsertion/Splitting.lean`, `PointInsertion/Since.lean` | consumers of `*_neg_absurd` | **no change** if WitnessSeed lemmas keep their *signatures* | Repairing F1's absurd lemmas internally leaves callers untouched. |
| `Metalogic/Chronicle/Frame.lean` | `:62,:72` map over `Formula.allFuture`/`allPast` — structural, not defeq | verify only | Uses constructor as a function; primitive constructor still works. |
| `Metalogic/Chronicle/TruthLemma.lean` | **Add 2 inductive cases** `allFuture`/`allPast` to `chronicle_truth_lemma` (`:219`) | **New** `truth_lemma_allFuture`, `truth_lemma_allPast` | See F7 — reduction strategy, reuses `truth_lemma_untl_forward/backward` (`:120`,`:141`), `truth_lemma_imp` (`:75`), `truth_lemma_bot` (`:66`). |
| `Metalogic/Completeness.lean` | none structural — only calls `chronicle_truth_lemma` (`:122`) | verify build | Carries through once TruthLemma is total. |
| `Metalogic/DenseCompleteness.lean` | none structural | verify build | Density axiom treats `𝐆` abstractly; fine. |
| `Metalogic/TemporalContent.lean`, `DenseMCS.lean` | use `mcs_mem_iff_neg_not_mem`/`neg_not_mem` with G (grep hit) | audit + rewrite via bridge | Same defeq class as MCS.lean; low volume. |
| `Metalogic/GenericMCSBridge.lean` | generic (Atom-agnostic) MCS framework | **likely no change** | It is temporal-operator-agnostic; the G/H specifics live in MCS.lean. Verify by scoped build. |

### F4 — MCS bridge lemmas (the two lemmas that repair MCS + Chronicle)

Proposed **new** lemmas in `MCS.lean` (verified absent: grep `allFuture.*↔|iff_neg_someFuture`
returns nothing). Building blocks all verified present:
`temporal_implication_property` (`MCS.lean:79`), `theoremInMcs` (`MCS.lean:97`), bridge axioms (F2).

```lean
/-- Bridge: in an MCS, primitive `𝐆φ` membership matches its classical unfolding. -/
theorem mcs_allFuture_iff {Ω : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistent Ω) {φ : Formula Atom} :
    (𝐆φ) ∈ Ω ↔ (Formula.neg (𝐅 (Formula.neg φ))) ∈ Ω := by
  constructor
  · exact fun h => temporal_implication_property h_mcs
      (theoremInMcs h_mcs (.axiom [] _ (.allFuture_to_classic φ) trivial)) h
  · exact fun h => temporal_implication_property h_mcs
      (theoremInMcs h_mcs (.axiom [] _ (.classic_to_allFuture φ) trivial)) h
-- `mcs_allPast_iff` is the verbatim past dual using `allPast_to_classic`/`classic_to_allPast`.
```

Repair recipe at each F1 site: wherever the old code produced `𝐅¬ψ ∈ Ω` from `𝐆ψ ∉ Ω` by defeq,
now do: `mcs_neg_of_not_mem` (`MCS.lean:119`) to get `¬𝐆ψ ∈ Ω`, then note
`(mcs_allFuture_iff).not_left`… — more directly, most sites already *hold* `𝐆X ∈ Ω` (positive
membership); for those just `rw`/`.mp` through `mcs_allFuture_iff` to obtain `¬(𝐅¬X) ∈ Ω` and
continue with the existing U/S machinery. `𝐆⊥` sites additionally use `neg ⊥ = ⊤`
(defeq `⊥→⊥ = top`, or a one-line `simp`).

### F5 — Soundness: the 4 new `axiom_sound` arms

`axiom_sound` (`Soundness.lean:75`) matches each `Axiom` constructor and proves validity. The 4
bridge axioms are sound because both sides denote `∀ s>t, Sat s φ`. Sketch (reusing the
`allFuture_iff`/`someFuture_iff` idiom already in the file at `:87,:267,:408`):

```lean
| allFuture_to_classic φ =>
    intro t hG                       -- hG : Sat M t (𝐆φ)
    rw [Satisfies.allFuture_iff] at hG
    simp only [Satisfies.neg_iff, Satisfies.someFuture_iff, not_exists, not_and]
    exact fun s hlt => absurd (hG s hlt) -- ¬¬: from ∃ counterexample derive ⊥
| classic_to_allFuture φ =>
    intro t h                        -- h : Sat M t (¬𝐅¬φ)
    rw [Satisfies.allFuture_iff]
    intro s hlt
    by_contra hns                    -- Classical is open (attribute [local instance] at :49-class files)
    exact h ⟨s, hlt, hns⟩            -- witness contradicts ¬∃
```

(Exact `simp` sets to be tuned against `Satisfies.imp_iff`/`neg_iff` — both verified present at
`Satisfies.lean:87,114`.) `allPast_to_classic`/`classic_to_allPast` mirror with `allPast_iff`/
`somePast_iff`. `minFrameClass` is `.Base`, so no dense-frame side conditions.

### F6 — Truth Lemma reduction strategy (de-risks Phase 6)

`chronicle_truth_lemma` (`:216`) is `induction φ generalizing t`, producing per-child IHs of the
form `ih_φ : ∀ s, Sat s φ ↔ φ ∈ limitF s.val` (this shape is confirmed by how the existing `untl`
case passes `ih_φ`/`ih_ψ` to `truth_lemma_untl_forward` at `:227`). Making G/H primitive adds two
cases. **Key result: they need no new canonical-model lemma.** Because the standalone case lemmas
`truth_lemma_untl_forward` (`:120`), `truth_lemma_untl_backward` (`:141`), `truth_lemma_imp`
(`:75`), `truth_lemma_bot` (`:66`) each take their IHs as *explicit arguments*, we can reconstruct
the truth lemma at the compound `¬𝐅¬φ = ¬(⊤ U ¬φ)` from the single IH for `φ`:

```lean
theorem truth_lemma_allFuture (A) (h_mcs) (t : ChronicleSubtype A h_mcs) (φ)
    (ih_φ : ∀ s, Satisfies (chronicleModel A h_mcs) s φ ↔ φ ∈ limitF A h_mcs s.val) :
    Satisfies (chronicleModel A h_mcs) t (𝐆φ) ↔ (𝐆φ) ∈ limitF A h_mcs t.val := by
  -- (1) Derive IHs for ¬φ and ⊤ from ih_φ + MCS negation-completeness at each point:
  have ih_neg : ∀ s, Satisfies _ s (Formula.neg φ) ↔ (Formula.neg φ) ∈ limitF A h_mcs s.val := by
    intro s
    rw [Satisfies.neg_iff, ih_φ s]
    exact (mcs_mem_iff_neg_not_mem (limit_c0 A h_mcs s.val s.property)).symm.not_left … -- neg completeness
  have ih_top : ∀ s, Satisfies _ s Formula.top ↔ Formula.top ∈ limitF A h_mcs s.val := …
  -- (2) Assemble the truth lemma for the compound ¬(⊤ U ¬φ) via the existing case lemmas:
  have tl_cmpd : Satisfies _ t (Formula.neg (𝐅 (Formula.neg φ)))
        ↔ (Formula.neg (𝐅 (Formula.neg φ))) ∈ limitF A h_mcs t.val :=
    truth_lemma_imp A h_mcs t (𝐅 (Formula.neg φ)) Formula.bot
      (by constructor                          -- IH for (⊤ U ¬φ) from untl case lemmas + ih_top/ih_neg
          · exact truth_lemma_untl_backward A h_mcs t (Formula.neg φ) Formula.top ih_neg ih_top
          · exact truth_lemma_untl_forward  A h_mcs t (Formula.neg φ) Formula.top ih_neg ih_top)
      (truth_lemma_bot A h_mcs t)
  -- (3) Bridge both sides to the primitive 𝐆φ:
  rw [sat_allFuture_iff_neg_someFuture_neg,             -- semantic (F3, Satisfies.lean)
      mcs_allFuture_iff (limit_c0 A h_mcs t.val t.property)]  -- membership (F4, MCS.lean)
  exact tl_cmpd
```

Caveats to resolve during implementation (flagged, not hand-waved):
- The argument order `truth_lemma_untl_backward A h_mcs t φ ψ ih_φ ih_ψ` maps `𝐅X = ⊤ U X = untl ⊤ X`
  to `(ψ U φ)` with `ψ := ⊤` (guard), `φ := ¬φ` (event) — confirm the guard/event slots against
  `someFuture φ = untl ⊤ φ` (`Formula.lean:68`); the `truth_lemma_untl_*` lemmas are stated for
  `ψ U φ` with `φ` the event, matching.
- Step (1)'s `ih_neg` uses MCS negation-completeness — the exact combinator is
  `mcs_mem_iff_neg_not_mem`/`mcs_neg_of_not_mem`/`mcs_not_mem_of_neg` (all in `MCS.lean:119-132`);
  pick the one that turns `φ ∉ f(s)` into `¬φ ∈ f(s)` and back.
- `truth_lemma_allPast` mirrors via `truth_lemma_snce_forward/backward` (`:171`,`:189`) and
  `mcs_allPast_iff`. Alternatively use `swapTemporal` duality if the file already has a
  past/future symmetry combinator (Frame/RRelation duality helpers exist).

Then in `chronicle_truth_lemma`, add:
```lean
  | allFuture φ ih_φ => exact truth_lemma_allFuture A h_mcs t φ ih_φ
  | allPast   φ ih_φ => exact truth_lemma_allPast   A h_mcs t φ ih_φ
```

### F7 — Completeness / DenseCompleteness

`Completeness.lean` uses only `chronicle_truth_lemma` generically (`:122`) — no constructor match.
Once TruthLemma is total, completeness compiles unchanged. Same for `DenseCompleteness.lean`
(the `density` axiom already treats `𝐆` abstractly; its soundness lives in `DenseSoundness.lean`
where `allFuture_iff` is used at the analogue of `Soundness.lean:408`). **Low risk** — verify by
scoped build only.

### F8 — Placement of the classical-equivalence "theorems"

Report 02 warned these might be needed before the final phase. **This is resolved by the WIP's
axiom approach**: because the equivalences are *axioms* (`allFuture_to_classic` et al.) available
from the ProofSystem layer (Phase 4), the MCS (Phase 5) and Chronicle (Phase 6) layers can consume
them immediately via `mcs_allFuture_iff`. The plan's Phase 5/6→Phase 8 ordering hazard therefore
**dissolves**. The task's stated deliverable "`𝐆φ ↔ ¬𝐅¬φ` recovered as theorems" is met by thin
wrappers in `Theorems.lean` (Phase 8) that just package the two axiom directions into an `Iff`:
```lean
theorem allFuture_iff_neg_someFuture_neg (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (𝐆φ ↔ ¬𝐅¬φ) := …  -- from the two bridge axioms + and-intro
```

## Decisions

- **D1** — Adopt the WIP's four bridge axioms as the canonical mechanism; do **not** attempt to
  derive `𝐆φ ↔ ¬𝐅¬φ` from the mono axioms (proven underivable, F2).
- **D2** — Introduce exactly two reusable MCS lemmas `mcs_allFuture_iff` / `mcs_allPast_iff`
  (F4) and route every F1 defeq break through them, rather than ad-hoc per-site fixes.
- **D3** — **Honesty caveat on "theorems".** With G primitive, the classical equivalences are
  *axioms*, so calling them "theorems" is technically true but conservativity is *asserted by
  axiom, not proved*. This is unavoidable (F2) and should be stated plainly in the PR description:
  the classical BX system with primitive G/H is the old system **plus** the (sound) collapse
  axioms; classical completeness is preserved, intuitionistic strength is enabled by *omitting*
  these axioms in a future intuitionistic variant. This matches Boudou et al.'s independent-G/F
  motivation.
- **D4** — Truth Lemma via the F6 reduction strategy (reuse standalone case lemmas), not via a
  new chronicle coherence lemma. Keep `WitnessSeed`/`RRelation`/`Seeds`/`Structures` lemma
  **signatures** stable so Chronicle consumers are untouched.

## Recommendations (critique of the 8-phase plan)

The existing plan (`plans/01`) survives contact with the source with three refinements:

1. **Phase 5 is under-scoped for the defeq audit.** The plan lists Soundness+MCS+helpers but does
   not name the specific break sites. Replace its checklist with the F1 table + F4 lemmas. Add
   `WitnessSeed.lean` explicitly to Phase 5 (the plan omits it, yet its `*_neg_absurd` lemmas are
   the highest-fan-out breaks and must land before Chronicle Phase 6).
2. **Phase 6 is de-risked, not the largest risk.** With F6, the TruthLemma cases are ~40 lines of
   *reuse*, not a new canonical construction. Re-label Phase 6 from "HIGHEST RISK, LARGEST" to
   "medium". The genuine risk concentrates in **Phase 5** (the defeq audit fan-out across
   `MCS` + `WitnessSeed` + `RRelation` + `Seeds` + `Structures`). Recommend splitting Phase 5:
   **5a** = Soundness + DenseSoundness (4 arms, self-contained), **5b** = MCS bridge lemmas +
   MCS.lean/WitnessSeed repairs, **5c** = Chronicle defeq-site repairs (RRelation/Seeds/Structures).
3. **Delete the Phase 5/6→Phase 8 ordering contingency** (F8): the bridge is axiomatic and
   available from Phase 4, so no reordering or local-lemma inlining is needed. Keep only the thin
   `Theorems.lean` wrapper at Phase 8.
4. **Add a soundness arm to `DenseSoundness.lean`** to the Phase 5 file list *only if* it
   re-matches Base axioms (verify; the plan already lists it, keep it).

Suggested revised metalogic wave: **5a ∥ (5b→5c) → 6 → {7 already parallel} → 8**.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|-----------|------------|
| `Instances.lean` typeclass rewiring (WIP) subtly wrong, so `right_mono_until` etc. no longer resolve for downstream MCS proofs | H | M | Phase 4 scoped build of `ProofSystem`; spot-check `someFuture_allFuture_neg_absurd` rebuilds first (canary). |
| `mcs_allFuture_iff` `.mp`/`.mpr` direction mismatch at a site expecting the *negated* form (`𝐆ψ ∉ Ω`) | M | M | Provide a companion `mcs_not_allFuture_iff : 𝐆φ ∉ Ω ↔ 𝐅(¬φ) ∈ Ω` derived from `mcs_allFuture_iff` + negation-completeness; use at `mcs_g_mp`-style sites. |
| F6 step (1) IH-for-`¬φ` combinator picks the wrong MCS negation lemma, looping | M | M | Enumerated candidates in F6; test with `lean_multi_attempt` before editing. |
| `neg ⊥ = ⊤` not defeq in `𝐆⊥` sites | L | M | One-line `simp only [Formula.neg, Formula.top, PropositionalConnectives.neg, PropositionalConnectives.top]`. |
| DenseSoundness re-matches and needs its own 4 arms | M | L | Read its `match`; delegate to `axiom_sound` if possible. |
| Build-exclusivity: whole Temporal red until Phase 8 (report 02 constraint) | H | H (expected) | One phase per agent run, scoped `lake build Module`; unchanged from plan. |

## Adversarial Self-Verification (H4)

Each recommendation was challenged before finalizing:

- **Claim: "`𝐆φ ↔ ¬𝐅¬φ` is underivable, so bridge axioms are necessary."** *Challenge:* could
  linearity/connectedness axioms (`temp_linearity`, `connect_future`) derive it? *Check:* traced
  all G-introduction routes (necessitation, `connect_future`, `density`, mono-axiom consequents);
  none introduces a primitive `𝐆φ` from a U/S antecedent. **Corroborated externally**: the WIP
  author *independently added the same four axioms* — two independent derivations reaching the
  same necessity is strong evidence. **Verdict: upheld.**
- **Claim: "TruthLemma needs no new chronicle lemma (F6)."** *Challenge:* does the reduction
  secretly need a coherence lemma `𝐆φ∈f(t) ∧ t<s → φ∈f(s)`? *Check:* No — that content is
  *already discharged* by `truth_lemma_untl_backward` (which uses `limit_satisfies_c4`) applied to
  `⊤ U ¬φ`; the reduction reuses it wholesale. The only genuinely new pieces are the two bridge
  lemmas (semantic + MCS), both one-liners over the bridge axioms. **Verdict: upheld, but marked
  the IH-reconstruction combinators as "to be tuned" (not asserted working).**
- **Claim: reuse lemmas exist.** *Check method:* direct `Read` of each definition with file:line
  (`truth_lemma_untl_forward` TruthLemma.lean:120; `someFuture_allFuture_neg_absurd`
  WitnessSeed.lean:43; `temporal_implication_property` MCS.lean:79; `allFuture_iff`
  Satisfies.lean:151; `axiom_sound` Soundness.lean:75). **`lean_local_search` returned empty**
  (LSP index cold at HEAD, WIP unapplied) — I did **not** rely on it; the source reads are
  authoritative. **Verdict: upheld via file evidence.**
- **Claim: `mcs_allFuture_iff` is new.** *Check:* grep `allFuture.*↔|iff_neg_someFuture` → no
  hits. Marked **"to be proved"**. **Verdict: upheld.**
- **Overconfidence audit:** F6's `sat_allFuture_iff_neg_someFuture_neg` and the `ih_neg`
  construction are sketches, not verified proofs; the `simp` sets in F5 are approximate. These are
  labeled as sketches with named building blocks, satisfying H2 (actionable) without
  over-claiming closure. No fundamental flaw surfaced → no `## Revised Direction` needed.

`adversarial_verification_triggered: true`.

## Source-to-Implementation Mapping (Tier 1)

| Source claim | BibKey | Lean target | Translation notes |
|--------------|--------|-------------|-------------------|
| G and F are *independent* primitives (intuitionistic temporal logic) | Boudou2017 *(to add to references.bib)* | `Formula.allFuture`/`allPast` as constructors; bridge axioms omitted in future intuitionistic variant | The bridge axioms encode exactly the *classical collapse* Boudou et al. reject; keeping them = classical, dropping them = intuitionistic. |
| Classical `𝐆φ ↔ ¬𝐅¬φ` (double-negation duality) | (folklore; Prior/Burgess tense logic) | `Axiom.allFuture_to_classic`/`classic_to_allFuture` (+ past duals); `Theorems.allFuture_iff_neg_someFuture_neg` | Underivable once G primitive (F2) → must be axiomatic; "theorem" = one-step axiom wrapper (D3). |
| Truth lemma / canonical model (Claim 2.11) | Burgess 1982 (cited in `TruthLemma.lean:34`; **also absent from references.bib** — flag) | `chronicle_truth_lemma` + new `truth_lemma_allFuture`/`allPast` | New cases reduce to Burgess's existing U/S cases via bridge (F6); no new canonical construction. |

## Appendix

**Files read (authoritative grounding):** `reports/01`, `reports/02`, `plans/01`;
`Syntax/Formula.lean` (defs), `Semantics/Satisfies.lean` (full), `Metalogic/Soundness.lean`
(dispatch + `soundness`), `Metalogic/MCS.lean` (full), `Metalogic/Chronicle/TruthLemma.lean`
(full), `ProofSystem/Axioms.lean` (full), `Metalogic/WitnessSeed.lean:38-77`,
`Metalogic/Chronicle/RRelation.lean:420-520`; `01_primitive-gh-wip.patch` (Axioms/Instances hunks).

**Greps:** chronicle usage of `futureSet|allFuture|*_neg_absurd`; `references.bib` for Boudou;
absence of `allFuture.*↔`; defeq-pattern files (`mcs_mem_iff_neg_not_mem`/`neg_not_mem`).

**Verified-present reuse lemmas (file:line):** `Satisfies.imp_iff`:87, `neg_iff`:114,
`someFuture_iff`:127, `somePast_iff`:139, `allFuture_iff`:151, `allPast_iff`:165;
`temporal_implication_property`:79, `theoremInMcs`:97, `mcs_neg_of_not_mem`:119,
`mcs_not_mem_of_neg`:124, `mcs_mem_iff_neg_not_mem`:129 (MCS.lean); `truth_lemma_bot`:66,
`truth_lemma_imp`:75, `truth_lemma_untl_forward`:120, `truth_lemma_untl_backward`:141,
`truth_lemma_snce_forward`:171, `truth_lemma_snce_backward`:189, `chronicle_truth_lemma`:216
(TruthLemma.lean); `axiom_sound`:75, `soundness`:395 (Soundness.lean); `limit_c0` (via
`MCS.limit_c0` usages in TruthLemma).

**To-be-proved (verified absent):** `mcs_allFuture_iff`, `mcs_allPast_iff`,
`sat_allFuture_iff_neg_someFuture_neg`, `truth_lemma_allFuture`, `truth_lemma_allPast`,
`allFuture_iff_neg_someFuture_neg` (+ past dual), 4 `axiom_sound` arms.
