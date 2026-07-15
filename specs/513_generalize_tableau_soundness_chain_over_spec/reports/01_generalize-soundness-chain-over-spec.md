# Research Report: Task 513 — Generalize the Tableau SOUNDNESS Chain over the Rule-Application Interface

- **Task**: 513 — `generalize_tableau_soundness_chain_over_spec`
- **Status**: [RESEARCHED]
- **Scope**: generalize `modalStepBranch_preserves_sat` (`SoundnessStep.lean`, ~500 lines) and its
  fuel-induction wrapper `modalExpandBranches_closed_unsat` (`Soundness.lean`) over an abstract
  `apply : RuleApply Atom`; re-instantiate K byte-identically; instantiate at
  `modalApplyOneT` to expose `modalTableauT_sound`; complete `tValid_decides` /
  `instDecidableTValid` (task 503 Phase 6).
- **Precedent mirrored**: task 510 (completeness/Hintikka chain), task 507 (termination measure).

## Bottom Line

**Feasible, structurally low-risk, and materially cheaper than task 510's crux — but it is
NOT a mechanical mirror of 510, because of one decisive asymmetry.**

The completeness chain (510) abstracted cleanly because **it never reads a propagating rule's
payload** — F9/F10 could hide the payload behind `∃ out, … = .persistent out`. **The soundness
proof does the opposite: it reads the propagating payload directly** (`SoundnessStep.lean:566-598`
reads `boxPropagation`; `:948-977` reads the diamond-negative successor propagation). Therefore:

1. **The existing 11 `RuleApplicationSpec` fields are INSUFFICIENT for soundness**, and — the key
   architectural finding — **the new soundness obligations cannot be `RuleApplicationSpec` fields
   at all**: they are **frame-relativized** (T's box-positive self-conjunct is sound only in
   reflexive models), while `RuleApplicationSpec` is deliberately **frame-agnostic**
   (`GenericDriver.lean`, no `FrameCondition` parameter). The generalization is threaded through a
   **new, separate frame-relativized soundness interface**, not through `RuleApplicationSpec`.

2. **The favourable structural fact (verified by task 503 Phase 6) is real and load-bearing**: the
   ambient Kripke model `(W, m)` is never replaced — only the world-assignment `f` is redefined at
   fresh worlds. Because every frame condition `FC` is a predicate on `m.r` alone, the `FC m.r`
   witness threads through the entire proof **unchanged**. This is what makes the port low-risk.

3. **A second favourable fact makes the port small**: `modalApplyOneT` differs from `modalApplyOne`
   on **exactly two shapes** (`.pos,.box` and `.neg,.diamond`, proved by
   `modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean:113`). The **minting** shapes
   (`boxNeg = .neg,.box`, `diamondPos = .pos,.diamond`) are **byte-identical to K**. So the ~200
   lines of minting-arm proof (fresh-world construction, `f'` extension) are reused verbatim via an
   agreement hypothesis; only the two propagating arms (~60 lines total) are replaced by
   frame-relativized semantic hypotheses.

4. **The hardest semantic content is ALREADY PROVEN.** `FrameSoundness.lean:159-229` already
   contains `branchSatisfiableIn_reflFC_boxPos_mem`, `branchSatisfiableIn_reflFC_diaNeg_mem`,
   `modalTBoxSelf_sound`, `modalTDiaNegSelf_sound` — the T-specific reflexivity soundness. Task 513
   consumes these; it does not reprove them.

**Main risk**: one phase is a ~400-450-line port of `modalStepBranch_preserves_sat` with `FC`
threaded through every `refine ⟨W, m, f, …⟩` tuple. It is mechanical (the model is never rebuilt),
but it is the bulk of the task. This is the only plausible `[BLOCKED]` site, and it is low
probability on the evidence.

**The interface grows by frame-relativized *semantic-soundness* facts on the two propagating
shapes plus one *agreement* fact — living in a new `RuleSoundnessSpec FC apply` bundle (or as raw
hypotheses), NOT in `RuleApplicationSpec`.**

---

## 0. The Decisive Asymmetry with Task 510 (read this first)

510's own report (§1, §9) turns on: *"the chain never reads a Propagating payload — it only ever
uses the class membership to derive a contradiction."* That is why F9/F10 are
`∃ out, (apply sf b acc).1 = .persistent out`, and why T/B/S5 discharge them despite different
payloads.

**Soundness inverts this exactly.** The box-positive arm
(`SoundnessStep.lean:566-598`) does nothing *but* read the payload:

```lean
refine ⟨boxPropagation b acc φ lbl ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
...
simp only [boxPropagation, Accessibility.successorsOf, List.mem_filterMap] at hmem_new
obtain ⟨w', hw'mem, hsf'⟩ := hmem_new        -- reads each propagated ⟨.pos, φ, tgt⟩
...
exact hpos (f tgt) (hacc lbl tgt hedge)       -- justifies it from □φ + the edge
```

For T, `modalApplyOneT`'s box-positive payload is `boxPropagation ++ (self-conjunct filtered)`
(`FrameRules.lean:96-101`). The extra `⟨.pos, φ, lbl⟩` is justified by **reflexivity**, not by any
recorded edge. There is **no** `∃ out` weakening that hides this: the soundness proof must produce
a semantic justification for **every** formula in the payload. Hence the soundness field is
irreducibly semantic and irreducibly frame-relativized. This is the single most important design
fact of the task and the direct explanation of why "completeness is generic, soundness is not."

---

## 1. Current State of the Soundness Chain (what exists, what is missing)

| Declaration | File:line | Generalized? |
|---|---|---|
| `branchSatisfiable` (frame-free, `Type*`) | `SoundnessStep.lean:63` | K-only |
| `sfSat`, `sfSat_pos/_neg` | `SoundnessStep.lean:158-173` | **generic already** (rule-agnostic) |
| `RuleResultSat` | `SoundnessStep.lean:177` | **generic already** (the right abstraction) |
| `applyPropRule_sat` | `SoundnessStep.lean:196` | **generic already** (K/T/B/S5 share prop rules) |
| `tryAllPropRules_sat` | `SoundnessStep.lean:369` | **generic already** |
| `accFreshInv`, `accFreshInv_empty` | `SoundnessStep.lean:392-404` | generic (data-only) |
| `negImp_alpha_preserved` | `SoundnessStep.lean:414` | **`private`** — needs de-priv/FC-lift |
| `modalStepBranch_preserves_sat` (~500 lines) | `SoundnessStep.lean:443` | **K-only — THE CRUX** |
| `modalClosed_unsat` | `SoundnessStep.lean:92` | K-only (frame-free) |
| `modalStepBranch_preserves_accFreshInv_gen` | `Soundness.lean:117` | **generic already (task 510)** — raw `freshLocal` |
| `modalExpandBranches_closed_unsat` (fuel ind.) | `Soundness.lean:197` | **K-only** |
| `kValid`, `modalTableau_sound` | `Soundness.lean:352-361` | K-only (byte-identical, keep) |
| `FrameCondition`, `frameValid`, `trivialFC` | `FrameSoundness.lean:69-80` | **frame vocab exists (task 509)** |
| `branchSatisfiableIn FC` (`W : Type`) | `FrameSoundness.lean:106` | **frame vocab exists** |
| `branchSatisfiableIn_trivial_imp` | `FrameSoundness.lean:121` | exists |
| `modalTableau_sound_frame` (K via frameValid) | `FrameSoundness.lean:135` | exists |
| `tValid := frameValid reflFC` | `FrameSoundness.lean:149` | exists |
| `branchSatisfiableIn_reflFC_boxPos_mem` | `FrameSoundness.lean:162` | **T semantic core — PROVEN** |
| `branchSatisfiableIn_reflFC_diaNeg_mem` | `FrameSoundness.lean:180` | **T semantic core — PROVEN** |
| `modalTBoxSelf_sound`, `modalTDiaNegSelf_sound` | `FrameSoundness.lean:199-229` | **T rule soundness — PROVEN** |
| `modalTableauT_sound` | — | **MISSING (task 513 deliverable)** |
| `tValid_decides`, `instDecidableTValid` | — | **MISSING (task 503 Phase 6 target)** |
| `modalTableauT_complete` | `FrameCompleteness.lean:882` | exists (task 503 Phase 5) |

The single crux is `modalStepBranch_preserves_sat`. Everything above it (`RuleResultSat`,
`tryAllPropRules_sat`) is already generic; everything for T's frame-specific soundness
(`branchSatisfiableIn_reflFC_*`) is already proven. The task is the ~500-line bridge in between,
plus wiring.

---

## 2. Import-Edge Topology (the layout constraint — differs from 510)

Verified edges:

```
Rules ─→ Saturation ─┬─→ SoundnessStep ─→ Soundness ─┐
                     │        (LoopInduction ─────────┤)
                     │                                └─→ FrameSoundness ←── FrameRules
                     │                                          │
                     └─→ Completeness ─→ FmpMeasure ─→ GenericDriver ─→ TDriver ─┐
                                                       (RuleApplicationSpec)      │
                                                                    FrameCompleteness  (imports
                                                                    FrameSoundness + TDriver)
```

**The decisive finding: `SoundnessStep` / `Soundness` / `FrameSoundness` and `GenericDriver` are on
PARALLEL branches** — both descend from `Saturation`, **neither imports the other**. They merge
only at `FrameCompleteness` (which imports both `FrameSoundness` and `TDriver → GenericDriver`).

Consequences (three regimes, cf. 510's two):

1. **`SoundnessStep.lean` and `FrameSoundness.lean` CANNOT reference `RuleApplicationSpec`**
   (`GenericDriver` not imported; importing it would pull the entire `FmpMeasure`/`Completeness`/
   `GenericDriver` chain in and violate the minimal, shake-clean import surface these files keep —
   exactly the constraint 510 recorded when it added `modalStepBranch_preserves_accFreshInv_gen`
   with a **raw** `freshLocal` parameter). So the generic soundness `_gen` lemmas take **raw,
   unbundled hypotheses**, precisely as 507/510 did for the parallel-branch files.

2. **`FrameSoundness.lean` is the natural home for the generic FC-relativized soundness lemmas**:
   it already defines `branchSatisfiableIn FC`, imports `Saturation` (→ `modalStepBranchGen`,
   `modalExpandBranchesGen`), `SoundnessStep` (→ `sfSat`, `RuleResultSat`, `tryAllPropRules_sat`),
   and `Soundness` (→ `modalStepBranch_preserves_accFreshInv_gen`, `modalClosed_unsat`). It may
   reference `modalApplyOne` (via `Rules`) for the agreement hypothesis discharge.

3. **`FrameCompleteness.lean` is the natural home for the K/T instantiations**
   (`modalTableauT_sound`, `tValid_decides`, `instDecidableTValid`): it is the unique merge point
   that sees both `modalApplyOneT` / `modalApplyOneT_spec` / `modalTableauT` (from `TDriver`) and
   the generic soundness lemmas + `tValid` / `reflFC` (from `FrameSoundness`). It already hosts
   `modalTableauT_complete`, so decidability lands beside it as a one-liner.

**Recommendation: extend `FrameSoundness.lean` (generic lemmas + K/T semantic discharges) and
`FrameCompleteness.lean` (T instantiation + decidability); do NOT create new files.** No barrel
churn, K corollaries stay beside their generic sources.

---

## 3. The Interface: which `RuleApplicationSpec` fields suffice, and the new soundness obligations

### 3.1 Verdict on the existing 11 fields

Derived from what the proof actually consumes (not assumed):

| `RuleApplicationSpec` field | Used by generic **soundness**? | Why |
|---|---|---|
| F1 `freshLocal` | **Yes (indirectly)** | needed by the fuel-induction wrapper via `modalStepBranch_preserves_accFreshInv_gen` (freshness maintenance), NOT by the sat-preservation step itself |
| F2 `outputsSubsetUniverse` | No | termination/universe, irrelevant to soundness |
| F3 `persistentFresh` | No | counting measure |
| F4 `rankStep` | No | termination |
| F5 `outDegStep` | No | termination |
| F6 `knownWorldsStep` | No | termination |
| F7 `branchingLength` | No | termination |
| F8 `localShapeInvariance` | No | gives only `.fst` branch-independence; soundness needs the *value*, not independence |
| F9 `boxPosNotExpanding` | No | `∃ out` hides exactly the payload soundness needs |
| F10 `diaNegNotExpanding` | No | ditto |
| F11 `boxNegWitness` | No | gives only the witness head + `∃ rest`; soundness reads the full minting payload |
| F12 `diaPosWitness` | No | ditto |

**Only `freshLocal` (F1) is reused, and only for freshness maintenance in the fuel wrapper.** The
sat-preservation content is orthogonal to all 12 fields. This is the precise, evidence-based
answer to the task's field-analysis question: **no existing field carries semantic soundness, and
none can — they are all either termination facts or payload-hiding shape facts.**

### 3.2 The new soundness obligations (three facts, frame-relativized)

The generic soundness step needs, for `apply` and a frame condition `FC`:

**(S-agree) — agreement off the two propagating shapes.** Rewrites `apply → modalApplyOne` on the
structural (propositional) and minting shapes, so the K arm proofs port verbatim:

```lean
hAgree : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
    ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) →
    ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) →
    apply sf b acc = modalApplyOne sf b acc
```
- **K discharge**: `fun _ _ _ _ _ => rfl` (`apply = modalApplyOne`).
- **T discharge**: `modalApplyOneT_eq_of_not_boxPos_diaNeg` verbatim — its statement is **exactly**
  this (`FrameRules.lean:113`). Zero new proof content.
- Covers all 10 propositional arms **and** both minting arms (`boxNeg = .neg,.box`,
  `diamondPos = .pos,.diamond` are outside the excluded `.pos,.box`/`.neg,.diamond` set).

**(S-boxPos) — frame-relativized box-positive semantic soundness.** The propagating box arm, where
the payload is read:

```lean
hBoxPosSound : ∀ {W : Type} (m : Model W Atom) (f : WorldIndex → W)
    (φ : Proposition Atom) (lbl : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
    FC m.r →
    (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) →
    (∀ sf ∈ b, sfSat m f sf) →
    (apply ⟨.pos, .box φ, lbl⟩ b acc).snd = acc ∧
    RuleResultSat m f (apply ⟨.pos, .box φ, lbl⟩ b acc).fst
```
- `RuleResultSat` (`SoundnessStep.lean:177`) is the pre-existing correct abstraction:
  `.persistent nf ↦ ∀ sf ∈ nf, sfSat m f sf`. The `.snd = acc` conjunct records non-minting.
- **K discharge**: extract the box-positive arm of the current monolith (`SoundnessStep.lean:555-598`)
  into a standalone lemma `modalApplyOne_boxPos_sound`; `FC` is unused (drop it), `acc = acc` by
  `modalApplyOne`'s propositional-then-persistent structure.
- **T discharge**: `modalApplyOneT`'s box-positive payload is `kForms ++ selfNew.filter …`
  (`modalApplyOneT_boxPos_fst`, `TDriver.lean:176`). Split `RuleResultSat` over the `++`: the
  `kForms` half is K's `modalApplyOne_boxPos_sound`; the `selfNew` half is
  `branchSatisfiableIn_reflFC_boxPos_mem` / `modalTBoxSelf_sound` (`FrameSoundness.lean:162,199`),
  which need `FC = reflFC`. **This is the only place `FC` is consumed, and its witness already
  exists.** New T content: ~15-25 lines combining two proven results over a filtered append.

**(S-diaNeg) — frame-relativized diamond-negative semantic soundness.** Dual of S-boxPos on the
`.neg,.diamond` shape; K discharge extracts `SoundnessStep.lean:948-977`, T discharge uses
`branchSatisfiableIn_reflFC_diaNeg_mem` / `modalTDiaNegSelf_sound`.

### 3.3 Where the new obligations live: a NEW bundle, NOT `RuleApplicationSpec`

Because `hBoxPosSound`/`hDiaNegSound` carry an `FC m.r` hypothesis and `RuleApplicationSpec` has
no `FrameCondition` parameter (and lives in `GenericDriver`, off the soundness import branch),
**the three facts cannot be `RuleApplicationSpec` fields.** Two equivalent packagings:

- **(Recommended) raw hypotheses** on the generic lemmas (mirrors 510's
  `modalStepBranch_preserves_accFreshInv_gen`, which takes raw `freshLocal`). Simplest; no new
  structure; the K/T instantiations supply the three facts directly. `freshLocal` for the fuel
  wrapper is also passed raw (K: `modalApplyOne_fresh`; T: `modalApplyOneT_spec.freshLocal` at the
  `FrameCompleteness` call site, which *can* see `RuleApplicationSpec`).
- **(Optional ergonomic) a `RuleSoundnessSpec (FC) (apply)` structure** in `FrameSoundness.lean`
  bundling `agree`, `boxPosSound`, `diaNegSound` (+ optionally `freshLocal`). Nicer for future
  B/S5 reuse, but adds a declaration. Recommend deferring to whenever B/S5 (tasks 505/504) actually
  land their soundness — until then, raw hypotheses match the proven 507/510 pattern and keep the
  diff minimal.

**Net interface growth: 3 frame-relativized soundness facts (raw), 0 new `RuleApplicationSpec`
fields.** This is the honest answer to "determine which fields suffice and whether a new
soundness-side field is needed": the soundness side needs a *separate frame-relativized interface*,
disjoint from `RuleApplicationSpec`.

---

## 4. Generic lemma signatures (to add in `FrameSoundness.lean`, raw-hypothesis form)

```lean
-- Frame-relativized closed-branch unsatisfiability (trivial generalization of modalClosed_unsat).
lemma modalClosed_unsatIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hclosed : isModalClosed b = true) (acc : Accessibility) :
    ¬ branchSatisfiableIn FC b acc
-- proof: fun ⟨W,m,f,_,he,hb⟩ => modalClosed_unsat b hclosed acc ⟨W,m,f,he,hb⟩

-- THE CRUX: generic frame-relativized single-step sat preservation (~400-450 line port).
theorem modalStepBranchGen_preserves_satIn (FC : FrameCondition) (apply : RuleApply Atom)
    (hAgree  : <S-agree, §3.2>)
    (hBoxPos : <S-boxPos, §3.2>)
    (hDiaNeg : <S-diaNeg, §3.2>)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiableIn FC b acc)
    (hInv : accFreshInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiableIn FC b' newAcc

-- Generic frame-relativized fuel induction (port of modalExpandBranches_closed_unsat, ~150 lines).
theorem modalExpandBranchesGen_closed_unsatIn (FC : FrameCondition) (apply : RuleApply Atom)
    (hFreshLocal : <F1-shape raw, as in modalStepBranch_preserves_accFreshInv_gen>)
    (hAgree hBoxPos hDiaNeg : …) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility),
      expandedSets.length = branches.length → accs.length = branches.length →
      List.Forall₂ (fun b acc => accFreshInv b acc) branches accs →
      modalExpandBranchesGen apply branches expandedSets accs fuel = .closed →
      List.Forall₂ (fun b acc => ¬ branchSatisfiableIn FC b acc) branches accs
```

### K re-instantiation (byte-identical statements — zero regression)

**Keep `modalStepBranch_preserves_sat`, `modalExpandBranches_closed_unsat`, `modalTableau_sound`,
`kValid` byte-identical and untouched** (the 510 "keep both" precedent — 510 kept
`modalHintikkaSet` concrete alongside `modalHintikkaSetGen`). Reason: the K path is stated at
`branchSatisfiable.{v,u}` (`Type*`, `SoundnessStep.lean:451`), whereas `branchSatisfiableIn FC` is
fixed at `W : Type` (universe 0) because `FrameCondition := ∀ {World : Type}, …` binds `Type`. A
`Type*` K statement therefore **cannot** be a corollary of the `Type`-fixed FC lemma. This is a
genuine universe boundary — do not attempt to collapse K's `.{v,u}` binder (that would break
byte-identity).

**Zero-regression demonstration** (the "re-instantiate K trivially" deliverable): re-derive
`modalTableau_sound_frame` (`FrameSoundness.lean:135`, K soundness through `frameValid`, universe
0) via `modalExpandBranchesGen_closed_unsatIn trivialFC modalApplyOne` — discharging `hAgree` by
`rfl`, `hBoxPos`/`hDiaNeg` by the extracted K arm lemmas, `hFreshLocal` by `modalApplyOne_fresh`.
This exhibits K as a trivial instance at universe 0 **without** touching K's canonical `Type*` API.
(If a reviewer insists K's monolith itself be re-derived, that requires widening
`branchSatisfiableIn`/`FrameCondition` to `Type*`, which is out of scope and unnecessary — T/B/S5
all live at universe 0.)

### T instantiation (in `FrameCompleteness.lean`)

```lean
-- Discharge the three soundness facts for T (near FrameSoundness's modalTBoxSelf_sound):
lemma modalApplyOneT_boxPos_soundIn  : <S-boxPos with apply := modalApplyOneT, FC := reflFC>
lemma modalApplyOneT_diaNeg_soundIn  : <S-diaNeg …>
--   via modalApplyOneT_boxPos_fst (TDriver) + K's modalApplyOne_boxPos_sound
--       + branchSatisfiableIn_reflFC_boxPos_mem / modalTBoxSelf_sound

theorem modalTableauT_sound (φ : Proposition Atom) (h : modalTableauT φ = .closed) : tValid φ := by
  -- contrapositive over reflFC, mirroring modalTableau_sound (Soundness.lean:361):
  -- feed modalExpandBranchesGen_closed_unsatIn reflFC modalApplyOneT
  --   (modalApplyOneT_spec.freshLocal) hAgreeT hBoxPosT hDiaNegT (modalFuel φ)
  --   at [[⟨.neg,φ,0⟩]] [[]] [Accessibility.empty];
  -- initial branchSatisfiableIn reflFC witness uses the reflexive closure of the counter-world.
  --   NOTE: the initial model must satisfy reflFC — use m with reflexive r (e.g. the given
  --   reflexive model from ¬tValid), which is available since tValid quantifies reflexive models.

theorem tValid_decides (φ0 : Proposition Atom) : modalTableauT φ0 = .closed ↔ tValid φ0 := by
  constructor
  · exact modalTableauT_sound φ0
  · intro htv; cases htab : modalTableauT φ0 with
    | closed => rfl
    | openBranch b a => exact absurd htv (modalTableauT_complete φ0 htab)

instance instDecidableTValid (φ0 : Proposition Atom) : Decidable (tValid φ0) :=
  match h : modalTableauT φ0 with
  | .closed => .isTrue ((tValid_decides φ0).mp h)
  | .openBranch _ _ => .isFalse (modalTableauT_complete φ0 h)
```

These mirror K's `modalTableau_decides` / `instDecidableKValid` (`CompletenessLoop.lean:1574,1586`)
line-for-line; both become one-liners once `modalTableauT_sound` lands. `modalTableauT_complete`
already exists (`FrameCompleteness.lean:882`).

**One point to verify during implementation** (flagged, not a blocker): in `modalTableau_sound`,
K builds the initial `branchSatisfiable` witness from an *arbitrary* falsifying model. For T, the
initial `branchSatisfiableIn reflFC` witness must supply an `FC m.r = Std.Refl m.r` proof. Since
`tValid = frameValid reflFC` quantifies over **reflexive** models, the falsifying model obtained by
`by_contra` on `tValid` is reflexive by hypothesis — so the `reflFC` witness is in hand. This
threads cleanly; confirm the `Std.Refl` instance/field is passed into the initial-branch tuple.

---

## 5. How the ~500-line crux port decomposes (arm-by-arm)

`modalStepBranch_preserves_sat` (`SoundnessStep.lean:443-977`) after `cases sign <;> cases formula`
splits into 14 arms. Port each to `modalStepBranchGen apply` / `branchSatisfiableIn FC`:

| Arm(s) | Lines | Port strategy | New content |
|---|---|---|---|
| `atom`, `bot` (both signs) | 470-476, 733-739 | via `hAgree` → `modalApplyOne` → `notApplicable`/absurd; `simp` closes | none |
| `and`/`or`/`imp` (both signs, incl. `negPos/negNeg/impNeg`) — 10 propositional arms | 477-554, 740-802 | via `hAgree` → `modalApplyOne`; port `refine ⟨…,W,m,f,hacc,…⟩` adding the `FC m.r` witness (unchanged `m`). Optionally route through `tryAllPropRules_sat` (already generic) instead of re-inlining `simp` | thread `FC` witness only |
| `imp`→`negImp_alpha_preserved` (`impNeg`) | 802 | de-privatize + FC-lift `negImp_alpha_preserved` (`SoundnessStep.lean:414`, currently `private`) | ~5-line FC variant |
| **`box` pos (boxPos)** | 555-598 | **replace by `hBoxPos`**; K extraction = `modalApplyOne_boxPos_sound` | extract standalone K lemma |
| **`diamond` neg (diaNeg)** | 948-977 | **replace by `hDiaNeg`**; K extraction = `modalApplyOne_diaNeg_sound` | extract standalone K lemma |
| `diamond` pos (diamondPos, minting) | 599-727 | via `hAgree` → `modalApplyOne`; port verbatim — builds `f'`, threads `FC m.r` (m unchanged), uses `hInv`/`modalNextWorld_gt` as-is | thread `FC` witness only |
| `box` neg (boxNeg, minting) | 803-947 | via `hAgree` → `modalApplyOne`; port verbatim (dual of diamondPos) | thread `FC` witness only |

The two minting arms (~260 lines total) are where the "model never replaced" fact pays off: the
`refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, …, W, m, f', ?_, ?_⟩` tuples change only by
inserting the `FC m.r` component (identical `m`, so `FC m.r` is literally the incoming witness).
`f'` extension, freshness (`hInv`), and edge bookkeeping are unchanged.

---

## 6. Recommended Phase Decomposition

Every phase ends at a green scoped `lake build` + commit. Mirrors 510's proven shape.

| P | Scope | Files | Est. lines | Risk |
|---|---|---|---|---|
| **1** | Extract K arm lemmas `modalApplyOne_boxPos_sound` (from `:555-598`) and `modalApplyOne_diaNeg_sound` (from `:948-977`) as standalone `RuleResultSat`-valued lemmas; de-privatize + FC-lift `negImp_alpha_preserved`; add `modalClosed_unsatIn`. Pure extraction, zero proof-content change. | `SoundnessStep.lean`, `FrameSoundness.lean` | ~120 | Low |
| **2** | **CRUX**: `modalStepBranchGen_preserves_satIn` (port of the monolith, §5). Two propagating arms → `hBoxPos`/`hDiaNeg`; propositional + minting arms ported with `FC` threaded via `hAgree`. | `FrameSoundness.lean` | ~420 | **High** |
| **3** | `modalExpandBranchesGen_closed_unsatIn` (port of `modalExpandBranches_closed_unsat`, swapping in the generic step + `modalStepBranch_preserves_accFreshInv_gen` + `modalClosed_unsatIn`). | `FrameSoundness.lean` | ~160 | Med |
| **4** | K zero-regression: re-derive `modalTableau_sound_frame` via `…_closed_unsatIn trivialFC modalApplyOne` (discharge `hAgree` by `rfl`, arms by P1 lemmas). Confirm K public API (`modalTableau_sound`, `modalTableau_decides`, `instDecidableKValid`) byte-identical & untouched (diff). | `FrameSoundness.lean` | ~40 | Low |
| **5** | T soundness discharges `modalApplyOneT_boxPos_soundIn`/`_diaNeg_soundIn` (combine K arm lemmas + `branchSatisfiableIn_reflFC_*`); `modalTableauT_sound` (feed generic fuel lemma at `reflFC`/`modalApplyOneT`, initial reflexive witness per §4 note). | `FrameSoundness.lean` and/or `FrameCompleteness.lean` | ~120 | Med |
| **6** | `tValid_decides` + `instDecidableTValid` (one-liners, mirror K). Full CI + `#print axioms` sweep (axiom-trio only). | `FrameCompleteness.lean` | ~30 | Low |

If P2 overruns, split: **P2a** = propositional + `atom`/`bot` arms; **P2b** = two minting arms;
the two propagating arms are already externalized as hypotheses, so the split is clean.

**Downstream (tasks 504 S5, 505 B)**: they get the entire generic soundness chain
(`modalStepBranchGen_preserves_satIn`, `…_closed_unsatIn`) for free. Each must supply only its own
three facts: `hAgree` (its own `…_eq_of_not_boxPos_diaNeg`), and `hBoxPos`/`hDiaNeg` discharged via
its own frame condition's semantic soundness (`Std.Symm` for B, `Relation.RightEuclidean`/`Eqv`
for S5) — plus a `freshLocal` (both never mint, so trivial). Their `branchSatisfiableIn_*FC_*_mem`
analogues are the only genuinely new per-system content, mirroring FrameSoundness's existing
`reflFC`/`s4FC` semantic lemmas.

---

## 7. Zero-Debt / Fidelity Assessment

- **No `sorry`, no axiom, no vacuous placeholder** is anticipated or acceptable. The two
  semantically-loaded arms are externalized as hypotheses that are **already proven for T**
  (`FrameSoundness.lean:162-229`); the rest is a mechanical FC-threaded port over an **unchanged
  model**.
- **Only plausible `[BLOCKED]` site**: P2 (the ~420-line crux) — if a minting-arm port hits an
  unexpected elaboration snag threading the `FC` witness. Low probability (the model is never
  rebuilt; `FC m.r` is a passenger). Correct response if it occurs: `[BLOCKED]` with the exact goal
  state recorded on the specific arm — never a `sorry`.
- **Counter-finding sought and NOT found**: a soundness arm that rebuilds `(W, m)` (not just `f`),
  or a propagating-shape payload whose soundness needs a frame condition **other** than the target
  logic's own `FC`. Neither exists — every minting arm keeps `m` fixed (`:631,:841`), and the two
  propagating payloads' extra formulas are justified by exactly `reflFC` (T), which is in hand.
- **Fidelity**: this is a transcription/generalization task, not a novel proof; follow the K
  monolith arm-for-arm (Fitting Ch. 2 semantics is already encoded in `Satisfies`). Do not replace
  ported arms with `aesop`/`simp`-bulldozing — keep the K structure so byte-identity of the K
  corollary is auditable.

## References

- Task 510 report/summary: `specs/510_generalize_completeness_loop_hintikka_chain_over_spec/`
- Task 503 Phase 6 blocker: `specs/503_…/.orchestrator-handoff.json` (the model-never-replaced fact)
- [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
