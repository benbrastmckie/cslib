# Research Report: Task 454 — Consolidate Chronicle PointInsertion Since helpers (Bimodal ↔ Temporal)

- **Task**: 454
- **Type**: cslib (Lean 4 / CSLib)
- **Date**: 2026-07-01
- **Session**: sess_1782924983_6bcecb_454
- **Scope**: Factor the duplicated, `fc`-diverged Chronicle point-insertion *Since* seed-consistency
  helpers shared by `Logics/Bimodal/.../PointInsertion/Since.lean` (1019 L) and
  `Logics/Temporal/.../PointInsertion/Since.lean` (704 L) into a common, interface-parameterized
  Chronicle-support module; reduce both logics to thin instantiations. Zero new sorries/axioms.
- **Grounding**: Every diff/overlap claim below was produced from the actual source files with
  `diff`/`grep`/`sed`, not from memory. The task-452 precedent claims are read from the landed
  Foundations module and task-452 report.

---

## 0. Executive summary (the load-bearing conclusions)

1. **The named *Since* seed-consistency helpers diverge along ONE axis: the explicit
   `fc : FrameClass` parameter.** Bimodal threads `fc` through every helper call; Temporal is the
   monomorphic `FrameClass.Base` specialization written with Temporal-native notation
   (`(xi S eta)`, `𝐏event`) and a few renamed aliases (`temporal_negation_complete` ↔
   `SetMaximalConsistent.negation_complete`). The proof *skeletons* are line-for-line the same
   (verified by full-body `diff`). This is exactly the "base ↔ Fc" pattern task 452 collapsed —
   **but across two distinct `Formula`/`FrameClass`/`DerivationTree` type universes**, so it is a
   genuine cross-logic abstraction, not a within-file collapse.
2. **The small helpers (`lemma27SinceSeed`, `l27sC5EventList`, `l27sB5GuardList`,
   `l27s_c5_event_list_mem`, `l27s_b5_guard_list_mem`, and the sibling `l27s_c5_γ_mem`,
   `l27s_b5_β_mem`) are essentially byte-identical** — the only diffs are docstring verbosity and
   ONE `simp only` lemma set (`[Formula.and, Formula.neg]` vs `[Formula.and]`). They depend only on
   `Formula` operators, so they are the cheapest, lowest-risk factoring win.
3. **The two big private theorems `lemma_2_7_since_seed_consistent` and
   `lemma_2_8_since_seed_consistent` are the real target.** They are `private` and have **zero
   external consumers** (grep-verified), so they can be relocated freely. In contrast the four
   *public* names — `lemma_2_7_since`, `lemma_2_8_since`, `lemma24SinceWithGuard`, `lemma24WithGuard`
   — are consumed by `CounterexampleElimination/*` in **both** logics and MUST be preserved verbatim
   as thin per-logic wrappers.
4. **The frame/relation interface is LARGE (~25–35 fields).** The seed-consistency proofs sit atop
   the entire Burgess/RRelation/Seeds apparatus (`BurgessR3Maximal`, `burgessRSet`,
   `burgessRSetSince`, `deductiveClosure`, `dc_delta_B_controlled`, `untl_left_mono_thm`,
   `snce_left_mono_thm`, `self_accum_since_mcs`, `list_conj_mem_*`, `listConjImpliesElem`,
   `BurgessR3Maximal_extension_fails`, `burgessRSince_implies_burgessR`, negation-completeness, …),
   which is itself duplicated per-logic. The common module must take that apparatus as **interface
   fields** (statements only — each logic supplies its own proof), NOT re-derive it. This is why
   this is the most structurally complex task in the batch.
5. **Burgess.lean and Seeds.lean diverge MORE than mechanically** (different proof strategies —
   Temporal uses `mcs_allFuture_iff` bridge lemmas and is shorter — plus different module
   organization). Their *proof bodies* therefore cannot be shared. **But this does not block the
   Since task**: the interface only needs the Burgess lemma *signatures* to align (they do, modulo
   `fc`), so each logic supplies its existing proof as an instance field. Full unification of
   Burgess/Seeds is explicitly out of scope and should stay a separate future task.
6. **Home**: `Cslib/Foundations/Logic/Metalogic/Chronicle/` (new subdir), namespace
   `Cslib.Logic.Metalogic.Chronicle`, mirroring the task-452 GenericMCS home. Foundations already
   ships `HasSince`/`HasUntil` notation classes (`Foundations/Logic/Connectives.lean:117,122`) to
   reuse for the formula-operator part of the interface. No shared Chronicle foundation exists yet.

---

## 1. Precise diff / overlap analysis (Goal 1)

### 1.1 Declaration map of the two `Since.lean` files

Both files share the same ordered block structure. Line ranges from `grep -nE`:

| Decl (in order) | Bimodal lines | Temporal lines | Divergence |
|---|---|---|---|
| `lemma24WithGuard` (public) | 832–880 (49 L) | **45–66 (22 L)** | present in both; Bimodal fc-param + longer; **relocated** (top in Temporal, bottom in Bimodal) |
| `lemma27SinceSeed` (priv def) | 66–70 | 67–71 | identical (has `@[nolint unusedArguments]`) |
| `l27sC5EventList` (priv def) | 71–79 | 72–80 | identical |
| `l27s_c5_event_list_mem` | 80–90 | 81–91 | identical |
| `l27sB5GuardList` (priv def) | 91–99 | 92–100 | identical |
| `l27s_b5_guard_list_mem` | 100–110 | 101–111 | identical |
| `l27s_c5_γ_mem` | 111–125 | 112–126 | identical |
| `l27s_b5_β_mem` | 126–147 | 127–144 | identical modulo one `simp only` set |
| `lemma_2_7_since_seed_consistent` (priv) | 148–344 (197 L) | 145–333 (189 L) | fc-threading only (see §1.3) |
| `lemma_2_7_since` (public) | 345–434 (90 L) | 334–417 (84 L) | fc-threading only |
| `lemma_2_8_since_seed_consistent` (priv) | 435–624 (190 L) | 418–600 (183 L) | fc-threading only |
| `lemma_2_8_since` (public) | 625–724 (100 L) | 601–680 (80 L) | fc-threading only |
| `until_witness_enriched_seed_consistent` (priv) | 725–831 (107 L) | **absent inline** | Bimodal-only in this file |
| `since_witness_enriched_seed_consistent` (priv) | 881–991 (111 L) | **absent inline** | Bimodal-only in this file |
| `lemma24SinceWithGuard` (public) | 992–1016 | 682–702 | present in both; signatures differ (`fc`, and Bimodal `{A}` vs Temporal `{C}`) |

**Why Bimodal is ~45% larger**: (a) `fc`-threading inflates every line slightly; (b) the two extra
`*_witness_enriched_seed_consistent` helper theorems (~218 L) that the Temporal file does not carry
inline; (c) more inline `--` comments (Temporal stripped many).

### 1.2 The small shared helpers — near byte-identical

`diff` of Bimodal L66–147 vs Temporal L67–144 returns only:
- 6 docstring rewordings (Bimodal spells out `untl(γ, β∧xi)`; Temporal is terse), and
- **one** proof-line difference at the `l27s_b5_β_mem` tail:
  `simp only [Formula.and, Formula.neg] at h_inj` (Bimodal) vs `simp only [Formula.and] at h_inj`
  (Temporal).

These helpers reference only `Formula.snce`/`Formula.untl`/`Formula.and`/`Formula.neg` and pure list
plumbing — **no `fc`, no Burgess apparatus**. They factor trivially over a `HasSince`/`HasUntil`
+ `HasAnd`/`HasNeg` formula interface.

### 1.3 The big seed-consistency theorems — divergence is 100% mechanical

Full-body `diff` of `lemma_2_7_since_seed_consistent` (Bimodal 148–344 vs Temporal 145–333):
79 `<` lines / 71 `>` lines changed out of ~190, and **every** change is one of:

| Kind | Bimodal | Temporal |
|---|---|---|
| consistency predicate | `SetMaximalConsistent fc A` / `SetConsistent fc …` | `Temporal.SetMaximalConsistent A` / `Temporal.SetConsistent …` |
| deductive closure | `deductiveClosure fc ({xi} ∪ B)` | `deductiveClosure ({xi} ∪ B)` |
| derivation family | `DerivationTree fc [] …` | `DerivationTree FrameClass.Base [] …` |
| Burgess lemmas | `BurgessR3Maximal_extension_fails fc …`, `dc_delta_B_controlled fc …`, `untl_left_mono_thm fc …`, `snce_left_mono_thm fc …`, `burgessRSince_implies_burgessR fc …`, `self_accum_since_mcs fc …` | same names **without** `fc` |
| list helpers | `listConj fc`, `list_conj_mem_dcs fc`, `list_conj_mem_mcs fc`, `listConjImpliesElem fc` | same **without** `fc` |
| negation-completeness | `SetMaximalConsistent.negation_complete h_mcs_C` | `temporal_negation_complete h_mcs_C` |
| notation | `Formula.snce xi eta`, `Formula.somePast event` | `(xi S eta)`, `𝐏event` |
| comments | present | mostly stripped |

`lemma_2_8_since_seed_consistent` follows the identical pattern. **Conclusion**: the two proof
skeletons are the same proof; Temporal is the `fc := .Base` reading. An interface that (i) fixes an
abstract derivation family `Deriv` and (ii) provides the Burgess apparatus as fields makes both
bodies collapse to one generic proof.

### 1.4 Burgess.lean / Seeds.lean overlap (context — NOT this task's proof target)

Delegated sub-analysis (read-only) found:
- **Burgess**: 26/40 declarations share names; **all diverged**, primarily by the same `fc` axis
  (`theoremInMcsFc`→`theoremInMcs`, `SetMaximalConsistent.implication_property`→
  `temporal_implication_property`), PLUS secondary proof-strategy divergence (Temporal uses
  `mcs_allFuture_iff` bridges; shorter) and module reorg (`BurgessR3Maximal_extension_fails`,
  `dc_delta_B_controlled`, `dc_delta_B_burgessR3` live in Temporal **Seeds.lean** but Bimodal
  **Burgess.lean**).
- **Seeds**: 20/25 share names; all diverged; even larger proof-style gap (`F_neg_of_G_not` is 23 L
  Bimodal vs 9 L Temporal).

**Implication for scope**: because Burgess/Seeds proof *bodies* genuinely differ, do **not** try to
share them in this task. The Since seed-consistency module consumes their lemma *statements* as
interface fields; each logic keeps its own Burgess/Seeds proofs and wires them into its instance.
This keeps task 454 tractable and honest about the "consolidation-with-care" framing.

---

## 2. The frame/relation interface abstraction (Goal 2) — task-452 as precedent

### 2.1 What task 452 did (landed pattern to imitate)

`Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` (namespace `Cslib.Logic.Metalogic.GenericMCS`)
defines a small `class HilbertTree (D : List F → F → Type*)` over an abstract formula `F` with
`[HasImp F]`, capturing the 5 things the backward MCS-bridge direction needs
(`assumption`/`mp`/`weakening`/`axiomK`/`axiomS`). Generic combinators (`unfoldListImp`,
`listDerivToTree`, `setConsistent_iff_congr`, `setMaxConsistent_iff_congr`) are written once over the
class; each logic supplies a ~10-line `instance` and keeps its public names as thin delegations. Base
↔ Fc collapse: base is *definitionally* the `fc := .Base` case, so base bodies became one-line
delegations to the `_fc` versions. Report: `specs/452_generalize_genericmcsbridge_foundations/reports/01_generalize-genericmcsbridge.md`.

**Key difference for 454**: task 452's interface was tiny (5 fields, one clean `InferenceSystem`
bottom). Task 454's interface must abstract the *entire tense-logic Burgess apparatus* the Since
proofs invoke — an order of magnitude more fields — because the seed-consistency proofs are deep.

### 2.2 The required interface (structure, ~25–35 fields)

Recommended: a `structure` (not a `class` — there is one instance per logic, and Bimodal needs an
instance *family* indexed by `fc`, so explicit passing is clearer than instance resolution) living in
Foundations, parameterized over an abstract formula type and derivation family. Sketch:

```lean
namespace Cslib.Logic.Metalogic.Chronicle

variable {F : Type*}

/-- Everything the Since point-insertion seed-consistency proofs consume from the
frame/derivation/Burgess layer of a tense logic. One instance per (logic, frame index). -/
structure SinceSeedInterface (F : Type*) where
  -- formula operators (or: require [HasImp F] [HasSince F] [HasUntil F] [HasAnd F] [HasNeg F]
  -- and drop these fields — see §2.3 reuse note)
  snce   : F → F → F
  untl   : F → F → F
  somePast : F → F
  and    : F → F → F
  neg    : F → F
  -- derivation family + consistency predicates
  Deriv          : List F → F → Type*        -- Bimodal: DerivationTree fc ; Temporal: DerivationTree .Base
  SetConsistent          : Set F → Prop
  SetMaximalConsistent   : Set F → Prop
  ClosedUnderDerivation  : Set F → Prop
  deductiveClosure       : Set F → Set F
  listConj               : List F → F
  -- Burgess relation
  BurgessR3Maximal   : Set F → Set F → Set F → Prop
  burgessRSet        : Set F → Set F → Set F → Prop
  burgessRSetSince   : Set F → Set F → Set F → Prop
  -- the lemma fields (statements only; each logic supplies its proof)
  negation_complete  : ∀ {A}, SetMaximalConsistent A → ∀ φ, φ ∈ A ∨ neg φ ∈ A
  extension_fails    : {- BurgessR3Maximal_extension_fails signature -}
  rsince_implies_r   : {- burgessRSince_implies_burgessR signature -}
  dc_delta_B_controlled : {- … -}
  untl_left_mono     : {- untl_left_mono_thm signature -}
  snce_left_mono     : {- snce_left_mono_thm signature -}
  self_accum_since   : {- self_accum_since_mcs signature -}
  list_conj_mem_dcs  : {- … -}
  list_conj_mem_mcs  : {- … -}
  listConjImpliesElem : {- … -}
  subset_deductiveClosure : {- … -}
  deductiveClosure_closed : {- deductiveClosure_closed_under_derivation -}
  -- (complete list = the §1.3 "Burgess lemmas / list helpers" rows; ~15 lemma fields)
```

The generic theorems:

```lean
theorem lemma_2_7_since_seed_consistent (I : SinceSeedInterface F)
    {A B C : Set F} {xi eta : F} (…hyps in I's vocabulary…) :
    I.SetConsistent (lemma27SinceSeed A B C xi eta) := by
  -- the Temporal proof body verbatim, with every `f …` replaced by `I.f …`
  …
theorem lemma_2_8_since_seed_consistent (I : SinceSeedInterface F) … := by …
```

Per-logic wiring (public names preserved):

```lean
-- Temporal/.../PointInsertion/Since.lean  (thin)
private def temporalSinceInterface : SinceSeedInterface (Formula Atom) := { … existing lemmas … }
theorem lemma_2_7_since {A B C} … := (lemma_2_7_since_of_seed temporalSinceInterface …)   -- wrapper

-- Bimodal/.../PointInsertion/Since.lean  (instance family)
private def bimodalSinceInterface (fc : FrameClass) : SinceSeedInterface (Formula Atom) := { … }
theorem lemma_2_7_since (fc : FrameClass) {A B C} … := (… (bimodalSinceInterface fc) …)
```

### 2.3 Reuse-first findings (mandatory check)

- **`Foundations/Logic/Connectives.lean:117,122`** already define `class HasUntil (F)` and
  `class HasSince (F)`. **Reuse them** for the `snce`/`untl` operator part of the interface rather
  than re-declaring operator fields; likewise check for `HasAnd`/`HasNeg`/`HasImp` there. This is the
  CSLib reuse-first requirement and shrinks the interface.
- **`Foundations/Logic/Metalogic/MCSProperties.lean`** already has generic `SetConsistent`,
  `SetMaximalConsistent`, `closed_under_derivation`. Investigate whether the per-logic
  `Temporal.SetMaximalConsistent` / `SetMaximalConsistent fc` are *definitional specializations* of
  the Foundations ones (task 452 §2.1 says these Foundations predicates exist and are logic-agnostic
  over a `DerivationSystem`). If so, the interface can take a `DerivationSystem F` and reuse the
  Foundations consistency predicates directly, dropping 4 fields. **Verify with `lean_hover_info` on
  `Temporal.SetMaximalConsistent` and the Foundations `SetMaximalConsistent` during Phase 0.**
- **No shared Chronicle/Burgess foundation exists** (`find Cslib/Foundations -ipath '*hronicle*'`
  empty). This module is genuinely new Foundations content — consistent with reuse-first (it is the
  first shared home for this apparatus, not a duplicate of one).

### 2.4 Why a `structure` beats a `class` here

Bimodal needs the interface **indexed by `fc : FrameClass`** (an instance *per frame class*). A
`class` would need `instance (fc) : SinceSeedInterface …`, which is resolvable but fragile when
several `fc` are in scope. An explicit `structure` argument passed positionally matches task 452's
observation that Temporal/Bimodal keep their tag types explicit and makes the `fc`-family obvious.
(Task 452 used a `class` because its interface had exactly one instance per logic; here Bimodal's
`fc`-family argues for explicit passing.)

---

## 3. Exact module location, name, and instantiation shape (Goal 3)

### 3.1 Home and name

- **Directory (new)**: `Cslib/Foundations/Logic/Metalogic/Chronicle/`
- **File**: `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean`
- **Namespace**: `Cslib.Logic.Metalogic.Chronicle` (matches GenericMCS's `Cslib.Logic.Metalogic.*`)
- **Imports**: only Foundations — `Connectives` (for `HasSince`/`HasUntil`), `MCSProperties`,
  `ListImplication`/`ListDeduction` as needed. **No `Cslib/Logics/*` import** ⇒ no cycle (the two
  Since.lean files will `public import` this new module, exactly as the bridges import GenericMCS).
- Rationale for Foundations (not a shared `Logics/` parent): Temporal and Bimodal are siblings with
  **no** common `Logics/` ancestor (Bimodal carries its own `Theorems.TemporalDerived`, it does not
  import Temporal). Foundations is the only shared ancestor and is the reuse-first home. A new
  subdirectory leaves room to later hoist Burgess/Seeds support beside it.
- Barrel: add to the module index (`lake exe mk_all --module`) and ensure `Cslib.Init` /
  `checkInitImports` stays green.

### 3.2 Instantiation shape (what each Since.lean becomes)

1. Keep `lemma27SinceSeed` + the small `l27s*` helpers **in the common module** (they need only
   formula operators; move both copies there, delete both local copies). Resolve the one
   `simp only [Formula.and, Formula.neg]` vs `[Formula.and]` diff by using the superset
   `[..., Formula.neg]` form (it is a no-op when `neg` is absent from the goal) — verify it still
   closes both.
2. Move `lemma_2_7_since_seed_consistent` / `lemma_2_8_since_seed_consistent` bodies into the common
   module as `SinceSeedInterface`-consuming theorems (they are `private`, zero external refs — safe).
3. In each logic's `Since.lean`: define the `SinceSeedInterface` (Temporal: one; Bimodal: an
   `fc`-indexed family), then keep the four **public** names `lemma_2_7_since`, `lemma_2_8_since`,
   `lemma24SinceWithGuard`, `lemma24WithGuard` at their current signatures as thin wrappers that call
   the generic theorems through the interface. External consumers
   (`CounterexampleElimination/Interface.lean`, `RecursiveWalks.lean`, `MainElimination.lean`) then
   compile unchanged.
4. The Bimodal-only `until_witness_enriched_seed_consistent` /
   `since_witness_enriched_seed_consistent` stay in Bimodal (not shared) — they are not part of the
   named duplicate family and have no Temporal counterpart in this file.

### 3.3 Public-API preservation table (grep-verified consumers)

| Name | Visibility | External consumers | Action |
|---|---|---|---|
| `lemma_2_7_since` | public | Bimodal `CEE/Interface`, Temporal `CEE/RecursiveWalks`,`MainElimination` | keep name+sig, wrap |
| `lemma_2_8_since` | public | same 3 | keep name+sig, wrap |
| `lemma24SinceWithGuard` | public | same 3 | keep name+sig, wrap |
| `lemma24WithGuard` | public | same 3 | keep name+sig, wrap |
| `lemma_2_7_since_seed_consistent` | private | **none** | move to common module |
| `lemma_2_8_since_seed_consistent` | private | **none** | move to common module |
| `lemma27SinceSeed`, `l27s*` | private | **none** | move to common module |

---

## 4. Coordination risk with tasks 449–451 (flagged per instructions)

- **Current status (state.json)**: 449 `not_started`, 450 `not_started`, 451 `not_started`, 415
  `completed`, 452 `completed`. **None of 449–451 is in flight for this run**, so there is no
  immediate `TemporalConservativity`/Chronicle churn to serialize against right now.
- **Latent risk**: 449 extends the `FrameClass` inductive (adds `.Metric`) and its
  `LE`/`PartialOrder`/`minFrameClass`; 450/451 build TM-conservativity and BX+ completeness on top,
  and per task 452's collision analysis "may edit files near the Bimodal bridge" and the Chronicle
  layer. If 449–451 later rewrite `TemporalConservativity` or adjacent Chronicle files, the
  `bimodalSinceInterface (fc)` family must cover any new `fc` case — but because the interface is
  `fc`-polymorphic and Bimodal already threads `fc` everywhere, a new `.Metric` case is absorbed
  automatically (same reasoning task 452 used for its `HilbertTree (DerivationTree fc)` instance).
- **Recommendation**: land 454 **before** 449–451 (454 is a pure refactor preserving all public
  names; 449–451 then build on the deduplicated base). If 449 lands first, 454 rebases mechanically
  (the interface gains no fields; only the `fc` domain grows). Record this ordering in the plan.

---

## 5. Zero-debt / risks / Phase-0 gate

1. **Zero new sorries/axioms is achievable**: this refactor *moves* existing sorry-free proofs; it
   introduces no new proof obligations. The generic seed-consistency theorem is the Temporal proof
   body re-expressed over `I.*`. Verify with `lean_verify` on the generic theorems (axiom check) and
   `grep -rn "sorry" ` on touched files.
2. **Phase-0 defeq/signature gate (blocking)**: before deleting any local copy, (a) build the new
   Foundations module in isolation; (b) prove the *Temporal* instance + one wrapper
   (`lemma_2_7_since`) compiles; (c) prove the *Bimodal* `fc`-family instance + wrapper compiles.
   Only then delete the local private bodies. Interface-field signatures must match both logics'
   existing lemma types modulo `fc` — confirm each field type with `lean_hover_info` on the concrete
   lemmas (`untl_left_mono_thm`, `snce_left_mono_thm`, `self_accum_since_mcs`,
   `BurgessR3Maximal_extension_fails`, `burgessRSince_implies_burgessR`, `dc_delta_B_controlled`,
   `list_conj_mem_dcs`, `list_conj_mem_mcs`, `listConjImpliesElem`) in **both** trees.
3. **Interface size is the main risk.** ~15 lemma fields must be transcribed exactly. Mitigate by
   reusing Foundations `HasSince`/`HasUntil`/`MCSProperties` (§2.3) to drop operator/consistency
   fields, and by generating field signatures directly from `lean_hover_info` output rather than by
   hand.
4. **`simp only` set reconciliation** (§3.2 step 1) — the one non-`fc` proof-line diff. Use the
   superset lemma list; verify both goals still close via `lean_multi_attempt`.
5. **Do NOT attempt to unify Burgess.lean / Seeds.lean proof bodies** (§1.4): they diverge
   non-mechanically. Only their lemma *signatures* enter the interface. Any attempt to share their
   bodies risks sorries and is out of scope.
6. **Lint**: new Foundations declarations need docstrings (docBlame); Prop-valued fields are fine in
   a `structure`; keep names lowerCamelCase; the module needs the standard license header + module
   docstring. `nolint dupNamespace` may be needed given the `Chronicle` namespace segment (the
   existing `ChronicleTypes.lean` uses `@[nolint dupNamespace]` liberally).

---

## 6. Suggested phase decomposition (for the planner)

- **Phase 0** — Create `Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean`; verify
  reuse of `HasSince`/`HasUntil`/`MCSProperties`; transcribe interface-field signatures from
  `lean_hover_info` on both logics' concrete lemmas; `lake build` the module in isolation (no
  per-logic edits, no generic proof yet — just types compile).
- **Phase 1** — Move `lemma27SinceSeed` + small `l27s*` helpers into the module (formula-operator
  interface only); retarget both Since.lean files to the shared copies; build both logics.
- **Phase 2** — Port `lemma_2_7_since_seed_consistent` body as the generic interface-consuming
  theorem; wire the **Temporal** instance + `lemma_2_7_since` wrapper; delete Temporal's local
  private body; build Temporal + its `CounterexampleElimination`.
- **Phase 3** — Wire the **Bimodal** `fc`-family instance + `lemma_2_7_since` wrapper; delete
  Bimodal's local body; build Bimodal.
- **Phase 4** — Repeat Phases 2–3 for `lemma_2_8_since_seed_consistent` / `lemma_2_8_since`.
- **Phase 5** — Full CI: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake …`, `lake lint`; `lean_verify` generic theorems for zero
  axioms/sorries; `mk_all --module` barrel update.

**Estimated net reduction**: the two ~190 L seed-consistency proofs collapse to one ~190 L generic
proof + two ~40 L instances; the small helpers dedup ~80 L × 1. Gross ~450 L duplicated → ~270 L
shared + ~90 L wiring ⇒ net ~200–300 L eliminated, consistent with the "consolidation-with-care"
framing. Both logics reduced to thin instantiations, DoD-compliant.

---

## 7. Files referenced (absolute paths)

- Bimodal Since: `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean`
- Temporal Since: `/home/benjamin/Projects/cslib/Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean`
- Bimodal Burgess/Seeds: `…/BXCanonical/Chronicle/PointInsertion/Burgess.lean`, `…/Seeds.lean`
- Temporal Burgess/Seeds: `…/Temporal/Metalogic/Chronicle/PointInsertion/Burgess.lean`, `…/Seeds.lean`
- Burgess relation defs: `…/{Bimodal…,Temporal…}/Chronicle/ChronicleTypes.lean`,
  `…/Chronicle/RRelation.lean`
- Precedent (landed): `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`;
  report `/home/benjamin/Projects/cslib/specs/452_generalize_genericmcsbridge_foundations/reports/01_generalize-genericmcsbridge.md`
- Reuse targets: `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean` (HasSince/HasUntil:117,122);
  `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Metalogic/MCSProperties.lean`
- External consumers to keep compiling: `…/Chronicle/CounterexampleElimination/Interface.lean`
  (Bimodal), `…/CounterexampleElimination/{RecursiveWalks,MainElimination}.lean` (Temporal)
