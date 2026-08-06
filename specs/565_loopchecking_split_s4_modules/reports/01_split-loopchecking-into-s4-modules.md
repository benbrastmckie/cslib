# Research: Splitting `LoopChecking.lean` into an `S4/` Module Cluster

**Task**: 565 — `[Task G of the modal-tableau refactor programme; P3]`
**Session**: `sess_1786030020_688c25_565`
**Date**: 2026-08-06
**Tree state**: `11607e0f` (post tasks 564, 586, 566)

---

## 0. Executive Summary

1. **Re-measured**: `LoopChecking.lean` is now **11,393 lines / 241 top-level declarations**
   (58 of them `private`) — not 10,540 / 230. The stated baseline is stale; tasks 564/566
   grew the file net-positive.

2. **The discontiguity claim is confirmed and is stronger than stated.** Under the family
   partition derived below, `Universe` occupies **6 disjoint source runs spanning L229–L9499**,
   `Driver` occupies **15 disjoint runs**, and the invariant material occupies **9 disjoint
   runs**. No contiguous line-range cut can produce any of the six named families.

3. **A seventh module is structurally forced.** The task's six-family list
   (Universe/BirthKey/Guard/Invariant/Hintikka/Redirect) cannot be extracted while the
   drivers stay in `LoopChecking.lean`: the invariant material alone makes **248 references**
   into the driver definitions. `S4/Driver.lean` (or an equivalently-named module) must exist
   *below* Invariant/Hintikka/Redirect. This is the single most important finding for planning.

4. **An 11-module layering with zero cycles has been verified empirically** (0 forward edges
   over 241 declarations and their full reference graph). See §3.

5. **26 `private` declarations cross a proposed seam** and must be de-privatized. Three
   `private` declarations have **no consumer at all** (§5.3) — Boneyard candidates.

6. **Zero downstream import churn is achievable** by retaining `LoopChecking.lean` as a
   `public import` barrel. `-- shake: keep` is the established, ratchet-free idiom for the
   re-exports the barrel does not itself consume (§6).

7. **`ORGANISATION.md` needs two edits**: expand the single undifferentiated `Tableau/` line
   into a subtree, and add the currently-absent module-size guidance (§4.3).

---

## 1. Re-Measurement (Q1)

### 1.1 Current figures

| Metric | Task description | Measured at `11607e0f` |
|---|---|---|
| `LoopChecking.lean` lines | 10,540 | **11,393** |
| Top-level declarations | 230 | **241** |
| `private` declarations | — | **58** |
| `@[simp]` lemmas | — | 2 (`modalMintShape_boxNeg`, `modalMintShape_diaPos`) |
| Other attributes | — | 1 (`@[nolint unusedArguments]` on `Reds`) |
| `instance` / `notation` / `macro` / `mutual` | — | **none** |

Reproduction (declaration count uses a corrected pattern — the one embedded in the file's own
header at L89–L98 misses `@[attr]`-prefixed and `public`-prefixed declarations):

```bash
wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean
grep -cE '^(@\[[^]]*\][[:space:]]*)?(private |protected |public )?(noncomputable |partial |unsafe )*(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom) ' \
  Cslib/Logics/Modal/Tableau/LoopChecking.lean
```

**Note for the implementer**: the file's own `## Measured Baseline` prose block (L60–L215)
contains stale self-referential figures ("10,540 lines", "230 top-level items") *and* a large
body of subsystem-wide census documentation. It must be updated and re-homed as part of this
task — see §4.4.

### 1.2 Family mapping to declaration names

The full 241-declaration assignment is in **Appendix A**. Summary:

| Family | Decls | ~Lines | Disjoint source runs |
|---|---:|---:|---|
| `Universe` | 32 | 499 | **6**: 229–529, 1815–1857, 2323–2367, 6067–6084, 8124–8195, 9480–9499 |
| `BirthKey` | 17 | 441 | **7**: 530–554, 900–981, 1030–1053, 1593–1672, 2147–2226, 2368–2499, 3079–3096 |
| `Guard` | 12 | 261 | **2**: 555–774, 1143–1183 |
| `Driver` (new) | 88 | 2,820 | **15**: 775–899, 982–1029, 1054–1142, 1184–1592, 1673–1814, 1858–2146, 2227–2322, 2705–2854, 3257–4059, 4513–4552, 7738–7959, 8006–8066, 8680–8812, 9625–9799, 10863–10900 |
| `Hintikka` | 15 | 601 | **2**: 6574–7138, 8088–8123 |
| `Redirect` | 16 | 639 | **2**: 8966–9479, 9500–9624 |
| Invariant material | 41 | 4,445 | **9**: 2500–2704, 2855–3078, 3097–3256, 4060–4512, 4553–6066, 6085–6573, 7139–7737, 8813–8965, 9800–10447 |
| Retained in `LoopChecking` | 20 | 1,460 | **5**: 7960–8005, 8067–8087, 8196–8679, 10448–10862, 10901–11394 |

**This table is the evidence the task asked for.** `Universe` — the *lowest* layer, the one a
naive line-count split would put in the first 500 lines — has material at L8124 and L9499. A
mechanical cut is not merely suboptimal; it is impossible.

---

## 2. Why a Seventh Module Is Forced (Q2, part 1)

The task's framing — six `S4/` modules, drivers and entry points retained in
`LoopChecking.lean` — does not close. Measured cross-family reference counts:

```
Invariant  -> Driver   248 references
Redirect   -> Driver    11 references
Hintikka   -> Driver    18 references
```

Every `modalStepBranchS4*_preserves_*` lemma names `modalStepBranchS4Keyed` or
`modalStepBranchS4KeyedOrdered` in its own statement. If those definitions live in
`LoopChecking.lean`, then `Invariant.lean` must import `LoopChecking.lean`, and
`LoopChecking.lean` must import `Invariant.lean` to state its entry-point theorems — a cycle.

**Two resolutions, both viable:**

- **(A) Recommended — add `S4/Driver.lean`.** Holds `modalApplyOneS4`, `modalApplyOneS4Keyed`,
  `modalApplyOneS4KeyedMint`, `modalStepBranchS4`, `modalStepBranchS4Keyed{,Body}`,
  `modalStepBranchS4KeyedOrdered`, `modalExpandBranchesS4{,Keyed,KeyedOrdered}`,
  `modalApplyOneS4KeyedSt` + the `RuleApplySt` bridge theorems, and the shape/equation lemmas
  that are immediate consequences of those definitions. `LoopChecking.lean` retains only
  `modalTableauS4Keyed{,Ordered}`, the termination-measure block, and the two capstone
  theorems.

- **(B) Alternative — `Guard.lean` absorbs the drivers.** Defensible on the reading that
  `modalApplyOneS4Keyed` *is* "the rule application that consults the guard". Keeps the module
  count at six but produces a ~3,100-line `Guard.lean` whose name describes ~8% of its content.

Recommend (A). Flag (B) explicitly in the plan so the deviation from the task's six-module
list is a recorded decision rather than drift.

---

## 3. The Verified Acyclic Layering (Q2, part 2)

### 3.1 Method

A reference graph over all 241 declarations was built by (a) line-wise stripping of block and
line comments, (b) tokenising each declaration's statement-plus-proof span, (c) intersecting
against the local declaration-name set. Docstrings are excluded, so mentions in prose do not
create false edges; `simp [foo]` / `unfold foo` / `exact foo` mentions *are* captured, so
definitional-unfolding dependencies are covered.

A candidate partition was then checked for forward edges (a module referencing a module later
in the intended import order). Three iterations were required; the final partition has
**zero forward edges**.

### 3.2 The layering

```
                       Universe
                          │
                      BirthKey
                          │
                        Guard
                          │
                        Driver
                     ╱    │    ╲
              Hintikka  InvKeys  InvAcc
                 │         ╲      ╱
              Redirect     Invariant
                 │             │
                 │        InvHintikka
                 ╲            ╱
                  LoopChecking  (barrel + entry points)
```

| Module | Decls | ~Lines | Imports (S4-internal) |
|---|---:|---:|---|
| `S4/Universe.lean` | 32 | 499 | — |
| `S4/BirthKey.lean` | 17 | 441 | `Universe` |
| `S4/Guard.lean` | 12 | 261 | `Universe`, `BirthKey` |
| `S4/Driver.lean` | 88 | 2,820 | `Universe`, `BirthKey`, `Guard` |
| `S4/Hintikka.lean` | 15 | 601 | `Driver` |
| `S4/Redirect.lean` | 16 | 639 | `Universe`, `BirthKey`, `Guard`, `Driver`, `Hintikka` |
| `S4/InvariantKeys.lean` | 14 | 1,725 | `Universe`, `BirthKey`, `Guard`, `Driver` |
| `S4/InvariantAcc.lean` | 12 | 1,320 | `Universe`, `BirthKey`, `Guard`, `Driver` |
| `S4/Invariant.lean` | 7 | 599 | + `InvariantKeys`, `InvariantAcc` |
| `S4/HintikkaInvariant.lean` | 8 | 801 | + `Hintikka`, `InvariantAcc`, `Invariant` |
| `LoopChecking.lean` | 20 | 1,460 | all of the above |

`Universe`, `InvariantKeys`, and `InvariantAcc` sit on independent branches below `Driver`
and can be built in parallel — a real compile-time win over the current serial 11k-line file.

### 3.3 On splitting the invariant material into three

`Invariant` as a single module is **4,445 lines / 41 decls** — larger than every file in
`Modal/Tableau/` except `LoopChecking`, `FrameCompleteness`, and `FrameSoundness`. Splitting
it three ways was tested and is acyclic:

- **`InvariantKeys`** — the six keys-facing fields
  (`keyLowerBd`, `keysInUniverse`, `keysTotal`, `keysDistinct`, `keysWorldsKnown`,
  `keysOriginS4`), plus the two `successorBirthContent_*_subset_relevantSetFinset` lemmas that
  `keyLowerBd` consumes.
- **`InvariantAcc`** — the accessibility/expansion fields (`eNodup`, `accFresh`, `accKnown`),
  `worldsContiguousS4` and its preservation, and the pigeonhole world bound
  (`modalKnownWorlds_length_le_worldBoundS4`, `modalStepBranchS4_worldBound`).
- **`Invariant`** — the `S4LoopInv` structure itself, `bClosure`/`eClosure` preservation, and
  the two capstone `_preserves_S4LoopInv` theorems that assemble all ten fields.
- **`HintikkaInvariant`** — `S4KeyedHintikkaInv`, `S4OrderedFuelInv`, their preservation
  theorems, and `modalS4Saturated_of_ordered_settled`.

If the plan prefers to hold at seven modules, collapse these four into one `S4/Invariant.lean`
— still acyclic, just large. Recommend the four-way split; it is the difference between a
4.4k-line file and four files none of which exceeds 1.8k.

### 3.4 What stays in `LoopChecking.lean`

20 declarations, ~1,460 lines:

- **Entry points**: `modalTableauS4Keyed`, `modalTableauS4KeyedOrdered`,
  `modalTableauS4Keyed_eq_modalExpandBranchesGenSt`.
- **Termination measure** (L8196–8679, L10448–10862): the `persistentFresh` /
  `branchingLength` / `outputsSubsetUniverse` per-call obligations, `modalExpMeasure_*`
  bridges, and the `stepBranch` projection lemmas. These sit above `InvariantAcc`
  (`modalApplyOneS4Keyed_outputsSubsetUniverse_S4` consumes `modalStepBranchS4_worldBound` and
  `worldsContiguousS4`).
- **Capstones**: `modalExpandBranchesS4Keyed_hintikka`,
  `modalExpandBranchesS4Keyed_openBranch_initial_mem`.

This is a coherent residue — "the S4 driver's entry points, its termination argument, and its
two end-to-end theorems" — not a leftover bucket.

### 3.5 Four assignments that are non-obvious and must not be guessed

These were the three iterations' worth of corrections. Getting any of them wrong reintroduces
a cycle:

| Declaration | Naive home | Correct home | Why |
|---|---|---|---|
| `keysUpdate_preserves_keysDistinct` (L720) | BirthKey (name says "keys") | **Guard** | references `blockingWorldS4Keyed`, `blockingWorldS4Keyed_none_fresh` |
| `modalNonMintCandidates{,_*}` (L1184–1264) | Guard (mint-readiness) | **Driver** | `modalNonMintCandidates` is defined in terms of `modalApplyOneS4Keyed` |
| `successorBirthContent_{boxNeg,diamondPos}_subset_relevantSetFinset` (L2500, L2601) | BirthKey (name) | **InvariantKeys** | reference `modalApplyOneS4KeyedMint` and its equation lemmas |
| `modalS4Saturated_addEdge_of_blocked` (L9500) | Hintikka (name prefix) | **Redirect** | consumes 8 Redirect declarations (`blockedRedirect_boxed_*`, `successorsOf_addEdge_*`, `modalApplyOneS4_*_fst_eq`) |

Also non-obvious: `modalMintShape` **does** belong in Guard (it depends on nothing below), but
`modalNonMintCandidates` does not, even though the two are adjacent and share a doc section
heading (`## Mint-Readiness`, L1114). The seam runs *through* that doc section.

---

## 4. Standards Conformance (Q3)

### 4.1 What `ORGANISATION.md` and `NOTATION.md` actually require

**`NOTATION.md` imposes no obligation on this task.** It covers operational-semantics arrow
notation (Options A/B/C) and the `S`-token collision. `LoopChecking.lean` declares **no
notation, no `scoped` declarations, and no macros** — verified by grep. Nothing to conform to,
nothing to preserve. State this explicitly in the plan so it is not re-investigated.

**`ORGANISATION.md` imposes**: the `Cslib.Logic.Modal` namespace for `Logics/Modal/`, and the
`Cslib.Logic` prefix shared across `Foundations/Logic/` and `Logics/`. It says nothing about
file headers, module size, or docstring structure.

### 4.2 The actual module template (from convention, not documentation)

The binding conventions are enforced by CI (`pre-pr-check.sh` step 3: copyright headers;
step 5: `--wfail`) and by the two modules that landed most recently — `Support/Accessibility.lean`
and `Support/KnownWorlds.lean`. Every new `S4/*.lean` must reproduce:

```lean
/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.<upstream>
public import Cslib.Logics.Modal.Tableau.S4.<lower S4 modules>

/-! # <Title>

<Prose: what this module holds and *why it is a separate module*.>

## Main Definitions   -- or ## Main Results
- `foo`: ...
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

...

end Cslib.Logic.Modal.Tableau

end
```

Note the trailing bare `end` closing the `@[expose] public section` — `LoopChecking.lean`
L11393 and `Support/KnownWorlds.lean` both have it.

`Support/Accessibility.lean`'s header sets the standard for the prose: it carries an explicit
**"Why a separate module"** section arguing against a future reader re-merging it. Each `S4/`
module should carry the equivalent — for `Universe.lean` in particular, since its six-run
provenance makes it look arbitrary to anyone who does not know the dependency structure.

### 4.3 Required `ORGANISATION.md` updates

**Edit 1 — replace the undifferentiated `Tableau/` line.** Currently, in the `Modal/` tree:

```
└── Tableau/                   -- Tableau decision procedures (K/T/B/S4/S5 drivers, saturation, soundness/completeness)
```

Replace with a subtree naming `Support/` (which already exists and is undocumented) and the
new `S4/` cluster with its layering. The `Foundations/Logic/Tableau/` block in the same file
is the formatting precedent.

**Edit 2 — add module-size guidance.** `ORGANISATION.md` currently gives none, which is
precisely how an 11,393-line file came to exist. Recommended wording, stated as guidance with
an explicit escape hatch rather than a hard gate:

> **Module size.** Prefer modules under ~1,500 lines. A module past ~3,000 lines should carry
> a docstring note justifying its size or a tracked plan to split it. Size alone is never a
> reason to split: split along the *dependency* structure, never by line count — the families
> inside a large module are typically discontiguous in the source, and a contiguous cut will
> not find them. Confirm any proposed seam is import-acyclic before writing files.

Placing this near the "Namespace Convention" section keeps the cross-cutting conventions
together.

**Edit 3 (optional)** — `Boneyard/` is already documented (task 566). If
`foldl_max_le_of_forall_le` is moved there (§5.3), no `ORGANISATION.md` change is needed.

### 4.4 Re-homing the header's `## Measured Baseline` block

`LoopChecking.lean` L60–L215 is ~155 lines of subsystem-wide census documentation (sorry
counts, axiom counts, "inventory figures that drifted", re-derivation-site tallies) that is
**not about loop-checking at all** — it documents the whole `Modal/Tableau/` subsystem. It
also contains the stale `10,540` / `230` figures.

Recommend: move it to `Cslib/Logics/Modal/Tableau/README.md` (or a `docs/` note), leaving
`LoopChecking.lean`'s header to describe the S4 driver. If a README is out of scope, it stays
in `LoopChecking.lean` but the two stale numbers must be corrected and the split noted.
Either way this is a required edit, not an optional tidy — the numbers are wrong today.

---

## 5. Mechanical Hazards (Q4)

### 5.1 `@[expose] public section` — the highest-severity hazard

The **entire** body of `LoopChecking.lean` sits inside one `@[expose] public section` opened at
L218. This is load-bearing: `@[expose]` makes definition bodies visible to downstream
elaboration, which every `unfold`, `simp [modalApplyOneS4Keyed]`, `rfl`, and `decide` proof
across the file depends on.

**Every new `S4/*.lean` must open its own `@[expose] public section`.** Omitting it on even
one module will produce a diffuse cascade of "failed to unfold" / motive-not-type-correct
errors in *downstream* modules, far from the omission. This is the single most likely way to
lose a day on this task.

Corollary: use `public import` (not bare `import`) for every S4-internal import, matching the
existing convention throughout `Modal/Tableau/`.

### 5.2 26 `private` declarations cross a proposed seam

Each must have `private` removed (they become part of the `Cslib.Logic.Modal.Tableau`
namespace's public surface). Grouped by their new home:

**From `Universe`** (11): `mem_modalUniverseS4_of`, `mem_modalUniverseS4_of'`,
`modalUniverseS4_mem_label`, `mem_of_any_beq_S4`, `any_beq_of_mem_S4`,
`mem_signedSubfmls_of_formula_S4`, `modalNextWorld_fresh_beq_S4`, `modalTBoxSelf_fresh`,
`modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`, `modalFourDiaNegProp_fresh`

**From `BirthKey`** (4): `boxPlusExtraS4_outputs_subset_S4`, `boxPlus_pos_disjunct_elim`,
`boxPlus_neg_disjunct_elim`, `successorBirthContent_subset_signedSubfmls`

**From `Driver`** (11): `modalStepBranchS4Keyed_result_keys_eq`,
`modalStepBranchS4Keyed_result_acc_eq`, `modalApplyOneS4Keyed_nonMint_known_S4`,
`modalApplyOneS4Keyed_nonMint_universe_S4`, `modalApplyOneS4Keyed_nonMint_snd_eq_acc`,
`modalStepBranchS4Keyed_keys_subset`, `modalStepBranchS4KeyedOrdered_keys_subset`,
`modalHintikkaClauseGen_S4Keyed_keys_indep`,
`modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding`,
`modalApplyOneS4Keyed_boxNeg_ne_notApplicable`, `modalApplyOneS4Keyed_diaPos_ne_notApplicable`

**Consequences of de-privatization:**
- **docBlame lint**: every de-privatized declaration needs a docstring. Spot-checks show most
  already have one (the file is unusually well-documented), but this must be verified per
  declaration — a missing docstring on a now-public lemma fails the `--wfail` gate.
- **Name-collision risk**: these names enter the shared `Cslib.Logic.Modal.Tableau` namespace
  alongside `FrameRules`, `TDriver`, `Saturation` etc. Names like `modalTBoxSelf_fresh` and
  `boxProps_outputs_subset_S4` are generic enough to warrant a `lean_local_search` check
  before landing.
- The remaining 32 `private` declarations stay private within their own module — no change.

### 5.3 Three `private` declarations have zero consumers

Verified by repo-wide grep (occurrence count includes the declaration itself):

| Declaration | Line | Occurrences in `Cslib/` |
|---|---:|---|
| `foldl_max_le_of_forall_le` | 6067 | **1** — declaration only. Genuinely dead. |
| `modalApplyOneS4Rules_boxPos_not_notApplicable_of_fourBoxProp_ne_nil` | 1719 | 2 — the second is a **docstring cross-reference** at L1760, not a use. |
| `modalApplyOneS4Rules_diaNeg_not_notApplicable_of_fourDiaNegProp_ne_nil` | 1762 | 1 — declaration only. |

All three are additionally referenced from `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean`,
which is excluded from the build by import-reachability, so those references impose no
constraint.

Per `Boneyard/README.md`'s zero-consumer archival criterion these qualify for the Boneyard.
**Recommend handling this as an explicit, separately-committed decision** rather than folding
it into the split — mixing a move-only refactor with deletions makes the "no proof content
changed" property unverifiable by diff inspection. If deferred, note it and carry them into
`Universe.lean` / `Driver.lean` unchanged.

### 5.4 Section variables and `unusedSectionVars`

One `variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]` line governs the whole file.
Because `unusedSectionVars` fires per *declaration*, and each declaration keeps the identical
variable context after the move, the split should be neutral. **But verify**: this is the
lint most likely to surface newly, and `pre-pr-check.sh` step 5 (`--wfail`) turns it into a
failure. If it fires, narrow the `variable` line per module (e.g. `Universe.lean` may not need
`[Hashable Atom]`) rather than adding a blanket `set_option linter.unusedSectionVars false` —
step 6's blanket-suppression ratchet is a ceiling that may only decrease.

### 5.5 Attributes and instances

Low risk, but must travel with their declarations:
- `@[simp]` on `modalMintShape_boxNeg` (L1152) and `modalMintShape_diaPos` (L1159) → both go
  to `Guard.lean`. Both LHSs are already simpNF-clean (they are in the tree today); moving
  does not change the simp set's *content*, only the module that contributes it.
- `@[nolint unusedArguments]` on `Reds` (L8965) → `Redirect.lean`.
- **No `instance`, no `notation`, no `scoped`, no `macro`, no `mutual`, no `termination_by`**
  anywhere in the file. Confirmed by grep. There are no ambient-instance hazards.

### 5.6 `open` scope

`open Cslib.Logic.Tableau Cslib.Logic.Modal` (L222) must be replicated verbatim in every new
module. It is what makes the unqualified `Sign`, `SignedFormula`, `RuleResult`, `Proposition`,
`Accessibility` references resolve.

### 5.7 Per-module upstream imports must be pruned, not copied

Naively giving every `S4/*.lean` the full current import set of `LoopChecking.lean`
(`FmpMeasure`, `FrameRules`, `Support.Accessibility`, `Support.KnownWorlds`, plus five Mathlib
`Finset` modules and `Mathlib.Tactic.Ring`) will produce **new `lake shake` findings inside
`Modal/Tableau/`** — which is exactly what the verification gate forbids ("no Modal/Tableau
findings AND count stays 9"). Import pruning is therefore mandatory, not cosmetic.

Attempting to predict the minimal import set statically is unreliable: name-based attribution
gives false positives because several declaration names are declared in more than one upstream
module. The dependable procedure is:

1. Give each module the full inherited set initially.
2. Build.
3. Run `bash scripts/check-shake-residue.sh` and remove exactly what it flags.
4. Re-build; repeat until the Modal/Tableau finding count is zero and the global count is 9.

For orientation, the authoritative upper bound (transitive import closure of
`LoopChecking.lean` today) is: `Foundations/Logic/Tableau/{Branch,Closure,ClosureCondition,`
`Measure,PropositionalRules,RuleResult,Sign,SignedFormula}` and
`Modal/Tableau/{Branch,Closure,Completeness,Defs,FmpMeasure,FrameRules,Rules,Saturation,`
`SoundnessStep,Support.Accessibility,Support.KnownWorlds}`. Note that `TDriver`,
`GenericDriver`, and `CompletenessLoop` are **not** in the closure despite prose references to
them in docstrings — do not add them.

---

## 6. Downstream Impact (Q5)

### 6.1 Who imports `LoopChecking.lean`

**Direct importers (5):**

| File | Nature |
|---|---|
| `Cslib.lean` (L504) | root barrel — `public import` |
| `Cslib/Logics/Modal/Tableau/S5Simplification.lean` (L11) | uses 2 symbols |
| `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (L10) | uses **72 symbols** — the heavy consumer |
| `CslibTests/S4LoopGuardRegression.lean` (L9–10) | uses 10 symbols |
| `Boneyard/ModalTableauS4Keyed/{KeysRootEmpty,RedirectOriginTransfer}.lean` | outside the build |

**Transitive consumers (2)**: `FrameSoundness.lean` (3 symbols, via `FiveSimplification` →
`S5Simplification`) and `FiveSimplification.lean` (2 symbols, via `S5Simplification`).

`specs/*/artifacts/*.lean` scratch files also import it but are not built.

### 6.2 Recommended strategy: `LoopChecking.lean` stays a barrel — zero downstream churn

`LoopChecking.lean` retains 20 declarations *and* `public import`s all ten `S4/` modules. Every
downstream `public import Cslib.Logics.Modal.Tableau.LoopChecking` keeps resolving exactly as
today. **No edits to `S5Simplification.lean`, `FrameCompleteness.lean`, `FrameSoundness.lean`,
`FiveSimplification.lean`, or `CslibTests/S4LoopGuardRegression.lean` are required.**

There is repo precedent for a pure re-export barrel: `Cslib/Foundations/Logic/Tableau.lean`.

**Shake interaction.** `LoopChecking.lean`'s own body consumes `Universe`, `Guard`, `Driver`,
`Hintikka`, `InvariantAcc`, `Invariant`, and `HintikkaInvariant`. It does *not* consume
`BirthKey`, `Redirect`, or `InvariantKeys` — so shake will flag those three re-exports. The
established, ratchet-free fix is the per-import comment used in 14 places across `Cslib/`:

```lean
public import Cslib.Logics.Modal.Tableau.S4.Redirect -- shake: keep
```

Verified: `check-lint-suppressions.sh` counts only blanket `set_option linter.X false` lines
(regex at L48). `-- shake: keep` is **not** counted and does not move the suppression ratchet.

### 6.3 Required: `Cslib.lean` registration

`scripts/CheckInitImports.lean` requires every `Cslib.*` module to transitively import
`Cslib.Init`, and `Cslib.lean` enumerates every module explicitly. **All ten new
`Cslib.Logics.Modal.Tableau.S4.*` modules must be added to `Cslib.lean`**, in the existing
alphabetical position (between `...Tableau.Rules` and `...Tableau.S5Simplification`).

`Cslib.Init` reachability is satisfied transitively via `FmpMeasure`/`FrameRules`/`Branch` —
`Support/Accessibility.lean` relies on exactly this and passes today, so an explicit
`import Cslib.Init` per module is optional. Add it anyway for modules whose upstream import
set gets pruned down to other `S4/` modules only.

### 6.4 Optional follow-on (do not do in this task)

Once the barrel is in place, `FrameCompleteness.lean` could import the seven specific `S4/`
modules it uses instead of the barrel, cutting its rebuild surface. That is a separate
optimisation with its own verification cost; keeping it out of this task preserves the "no
downstream file changed" property that makes the split reviewable.

---

## 7. Zero-Debt Compliance

This is a **move-only refactor**. No new proof obligations arise; no declaration's statement or
proof changes. The zero-sorry outcome is achievable by construction, and no approach considered
here requires `sorry`, a new axiom, or deferral.

The one place proof text may need to change is `simp`/`unfold` calls that relied on a
now-private-elsewhere name — but §5.2 removes `private` from exactly those, so the references
remain valid.

**Verification gate (unchanged from the stated baseline):**

| Gate | Expected |
|---|---|
| `lake build Cslib` | green, ~3313 jobs (job count will rise — new modules) |
| `Modal/Tableau` sorry census | exactly **1** (`branchSatisfiableIn_s4FC_ancestor_redirect`, `FrameSoundness.lean`) |
| Axioms in subsystem | **0** |
| `lake shake` | exit 1, **9 findings, none in `Modal/Tableau/`** |
| `scripts/CheckInitImports.lean` | exit 0 |
| `lake exe lint-style` | exit 0 |
| `lake test` | green |
| `scripts/check-lint-suppressions.sh` | no increase |
| `scripts/check-boneyard-quarantine.sh` | exit 0 |

---

## 8. Suggested Phase Decomposition

Each phase ends green and is independently committable. The layering means each new module can
be extracted bottom-up while `LoopChecking.lean` shrinks, and the build is verifiable after
every single one.

| Phase | Work | Verify |
|---|---|---|
| 1 | `S4/Universe.lean` (32 decls, 6 runs); de-privatize 11; register in `Cslib.lean` | build + shake |
| 2 | `S4/BirthKey.lean` (17 decls, 7 runs); de-privatize 4 | build + shake |
| 3 | `S4/Guard.lean` (12 decls, 2 runs) | build + shake |
| 4 | `S4/Driver.lean` (88 decls, 15 runs); de-privatize 11 — **largest and riskiest phase** | build + shake |
| 5 | `S4/Hintikka.lean` (15 decls, 2 runs) | build + shake |
| 6 | `S4/Redirect.lean` (16 decls, 2 runs) | build + shake |
| 7 | `S4/InvariantKeys.lean` + `S4/InvariantAcc.lean` (26 decls) | build + shake |
| 8 | `S4/Invariant.lean` + `S4/HintikkaInvariant.lean` (15 decls) | build + shake |
| 9 | `LoopChecking.lean` header rewrite; re-home the `## Measured Baseline` block; barrel `public import`s + `-- shake: keep` | build + full CI |
| 10 | `ORGANISATION.md` edits 1 and 2 | doc review |
| 11 | Full gate sweep (`pre-pr-check.sh`, `lake test`, sorry/axiom census) | all green |

Phase 4 is oversized by any reasonable measure (88 declarations across 15 discontiguous runs).
Consider splitting it into 4a (the definitions plus their equation/shape lemmas, L775–L2322)
and 4b (the known-worlds/universe-membership composites, L3257–L4552, plus the trailing runs)
— acyclicity holds either way since 4b consumes only 4a and lower layers.

---

## Appendix A — Full Declaration Assignment

Two machine-readable artifacts were produced and are committed alongside this report:

- `specs/565_loopchecking_split_s4_modules/artifacts/module-assignment.md` — the complete
  241-declaration mapping, grouped by target module, with `private` flag, kind, and current line.
- `specs/565_loopchecking_split_s4_modules/artifacts/decl-graph.json` — the full reference
  graph: one record per declaration with `name`, `vis`, `kind`, `line`, `end`, `refs` (its
  local dependencies), and `sub` (its assigned target module).

**Line numbers in both artifacts are valid only against `11607e0f` and will shift as phases
land.** This is exactly why every reference in this report anchors on **declaration names**,
and why the phase plan must too. Regenerate both artifacts against the current tree at
implementation time using the procedure in §3.1; the assignment predicates are fully
determined by §1.2's run table plus §3.5's four corrections.

A useful invariant for the implementer: after regenerating, re-running the forward-edge check
from §3.1 against the `sub` assignment must report **zero violations**. If it does not, a
declaration has been added or moved since this research and the layering needs re-derivation
before writing any files.
