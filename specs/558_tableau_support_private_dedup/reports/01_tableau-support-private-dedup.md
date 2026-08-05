# Research Report: Extract Re-derived Private Tableau Facts into Public Support Modules

**Task**: 558 — Tableau Support private dedup
**Session**: sess_1785908335_1f3c58
**Date**: 2026-08-04
**Status**: Research complete

---

## Executive Summary

Six findings materially change the shape of this task versus its description.

1. **The "77 re-derivation sites" figure is closer to correct than the tree's own "corrected 55."**
   The tree's `LoopChecking.lean` module docstring retired 77 in favour of 55. But 55 counts
   `Local re-derivation` *comment strings*; the actual duplicate *declarations* number **72,
   across 41 families**. The comment-based census systematically undercounts because several
   duplicate families carry different comment phrasings (`S4-local restatement`,
   `Territory-local re-derivation`) or no comment at all.

2. **"50 private declarations in FmpMeasure.lean" is exactly correct**, but only **14** of them
   are actually re-derived elsewhere. The other 36 are genuinely file-local and must stay private.

3. **The three-module partition (Subfmls / KnownWorlds / Accessibility) covers only about half
   the inventory.** 33 of 72 duplicates are Branch.lean-level (fit the proposed modules cleanly);
   23 are FmpMeasure-level (need no new module at all — de-privatization in place suffices);
   16 originate *above* FmpMeasure and have no Support home.

4. **The task's premise — "mechanical and behaviour-preserving by construction, requires no
   abstraction decision" — is empirically FALSE as stated**, though less badly than first
   appeared. `modalKnownWorlds_fold_spec`'s private original is strictly **stronger** than its
   six copies (extra `Nodup` hypothesis, extra conjunct), and the `modalMaxWorld` family exists
   in four binder-incompatible variants. Neither is a drop-in substitution. **However**, after
   direct source inspection (§4.4) both hazards resolve without per-site proof work: the weak
   `fold_spec` copies become dead code, and 26 of 30 `modalMaxWorld` call sites use `apply`,
   which is binder-mode insensitive. **The reconciled count of genuinely different propositions
   is zero.** The plan must still split the safe bulk (~56 declarations) from the ~16 needing
   judgment — it may not assume uniformity.

5. **The do-not-edit constraint is satisfied on the deletion side** — zero duplicates live in
   Rules.lean, Saturation.lean, or Branch.lean. But Branch.lean is where the *definitions* live,
   and being unable to edit it is precisely *why* separate `Support/` modules are the right
   answer rather than adding the lemmas to Branch.lean directly.

6. **`file_scope` in state.json is wrong.** It lists the modules that *own the private originals*
   but omits all six modules where the 72 duplicates must be *deleted*.

---

## 1. Measured Inventory (re-measured against current tree)

### 1.1 Comment-site census — reconciled, no drift

| Command | Result |
|---|---|
| `grep -rho 'Local re-derivation' Cslib/ \| wc -l` | **57** |
| minus 2 self-referential prose lines in LoopChecking.lean's own docstring (`:142`, `:151`) | **55 real sites** |
| Sites outside `Cslib/Logics/Modal/Tableau/` | **0** |

Verified across commits: at `d9e4424d^` the count was 55 with zero prose lines; at `d9e4424d`
(which landed the docstring recording "55") it became 57 total / 55 real. **No drift since
2026-07-26** — the +2 is the measurement note counting itself.

Distribution of the 55 comment sites by file:

| File | Sites |
|---|---|
| LoopChecking.lean | 14 |
| S5Simplification.lean | 14 |
| FiveSimplification.lean | 10 |
| BDriver.lean | 6 |
| FrameSoundness.lean | 6 |
| FrameCompleteness.lean | 5 |

### 1.2 Declaration-level census — the authoritative number

Counting `private lemma <base>_<SUFFIX>` declarations whose `<base>` also exists as a
declaration elsewhere in the subsystem (suffixes `_B _C _S4 _S5 _S5w _Five _FS _anc _local
_origin _S4Keyed`):

> **41 families, 72 duplicate declarations.**

The comment census misses 17 declarations. Concrete examples of duplicates carrying **no**
`Local re-derivation` comment:

- `modalSubfmls_trans_B` (BDriver.lean:209) and `modalSubfmls_trans_S4` (LoopChecking.lean:1695)
  — the task description asserts `modalSubfmls_trans` is re-derived in **three** files; it is
  actually **four** (BDriver, FiveSimplification, LoopChecking, S5Simplification).
- `modalKnownWorlds_fold_spec_C` (FrameCompleteness.lean:3749) — description says four copies;
  there are **six**.
- `hasEdge_addEdge_cases` — description says four copies; there are **seven** (plus the original).

**Recommendation**: the implementation plan must drive off the declaration-level census, not the
comment strings. Deleting only commented sites would leave 17 duplicates behind.

### 1.3 Top families by multiplicity

| Base fact | Origin | Copies |
|---|---|---|
| `hasEdge_addEdge_cases` | Soundness.lean:75 (private) | 7 |
| `modalKnownWorlds_fold_spec` | FmpMeasure.lean:1733 (private) | 6 |
| `mem_modalKnownWorlds` | FmpMeasure.lean:1781 (private) | 6 |
| `modalKnownWorlds_mono_append` | FmpMeasure.lean:1822 (private) | 5 |
| `modalSubfmls_trans` | FmpMeasure.lean:401 (private) | 4 |
| `modalUniverse_mem_formula` | FmpMeasure.lean:461 (private) | 3 |
| `mem_modalUniverse_of` | FmpMeasure.lean:440 (private) | 3 |
| 9 families | various | 2 each |
| 25 families | various | 1 each |

### 1.4 The 50 private declarations in FmpMeasure.lean

`grep -c "^private " Cslib/Logics/Modal/Tableau/FmpMeasure.lean` = **50**. Confirmed exactly.

Of these, **14 are re-derived elsewhere** and are the actual publicisation candidates:

```
modalSubfmls_trans          mem_modalUniverse_of        modalUniverse_mem_formula
mem_boxPositivesOf          mem_successorsOf_hasEdge    modalKnownWorlds_fold_spec
modalKnownWorlds_nodup      mem_modalKnownWorlds        modalKnownWorlds_le_modalMaxWorld
modalKnownWorlds_mono_append  mintGroup_label_eq_freshWorld
modalExpMeasure_split       modalExpMeasure_append      modalExpMeasure_const_exp
```

(Plus `outDeg_addEdge_self`, `outDeg_addEdge_ne`, `boxProps_outputs_subset`,
`diaNegProps_outputs_subset`, `modalCount_notMem_*`, `modalWork_drop_*` which have `_S4` copies
found only by the declaration-level census.)

The remaining ~30 privates have no duplicates and **must stay private** — publicising them would
grow the public API surface for no benefit and would be flagged by `lake shake`/lint review.

---

## 2. Module Partition Analysis

### 2.1 The decisive fact: where the definitions live

| Definition | Home | Consequence |
|---|---|---|
| `Accessibility`, `empty`, `addEdge`, `successorsOf`, `allWorlds`, `hasEdge` | **Branch.lean:54-80** | Facts can sit at Branch level |
| `modalKnownWorlds`, `modalMaxWorld`, `modalNextWorld` | **Branch.lean:88-98** | Facts can sit at Branch level |
| `boxPositivesOf`, `boxPropagation` | **Branch.lean:182,196** | Facts can sit at Branch level |
| `modalSubfmls` | **FmpMeasure.lean:73** | Facts cannot go below FmpMeasure |
| `modalUniverse` | **FmpMeasure.lean:151** | Facts cannot go below FmpMeasure |
| `modalExpMeasure` | **FmpMeasure.lean:200** | Facts cannot go below FmpMeasure |
| `outDeg` | **FmpMeasure.lean:804** | One-liner over `successorsOf`; *could* be moved down |
| `accFreshInv` | **SoundnessStep.lean:392** | Facts cannot go below SoundnessStep |

`Branch.lean` imports only `Foundations.Logic.Tableau.SignedFormula` and `Modal.Tableau.Defs`. It
is the second-lowest module in the subsystem. **A `Support/` module importing Branch.lean sits
below every consumer — zero cycle risk.**

### 2.2 Three-tier classification of the 41 families

**Tier 1 — Branch.lean-level (9 families, 33 duplicate declarations).**
These fit the proposed `Support/` modules exactly.

| Target module | Families |
|---|---|
| `Support/Accessibility.lean` | `hasEdge_addEdge_cases` (7), `mem_successorsOf_hasEdge` (2), `hasEdge_mem_successorsOf` (1) |
| `Support/KnownWorlds.lean` | `modalKnownWorlds_fold_spec` (6), `mem_modalKnownWorlds` (6), `modalKnownWorlds_mono_append` (5), `modalKnownWorlds_nodup` (2), `modalMaxWorld_le_of_forall_label_le` (2), `mem_boxPositivesOf` (2) |

Both modules import **only** `Cslib.Logics.Modal.Tableau.Branch`.

**Tier 2 — FmpMeasure-level (16 families, 23 duplicate declarations).**
`modalSubfmls_trans`, `mem_modalUniverse_of`, `modalUniverse_mem_formula`, `modalSubfmls_self_mem`,
`boxProps_outputs_subset`, `diaNegProps_outputs_subset`, `mintGroup_label_eq_freshWorld`,
`outDeg_addEdge_self/_ne`, `modalCount_notMem_append_drop/_mono`, `modalWork_drop_linear/_persistent`,
`modalExpMeasure_split/_append/_const_exp`.

**Key finding: these need no new module.** All six consumer files already reach FmpMeasure
transitively through `public import` chains (verified below). Simply **removing the `private`
keyword in place** makes them visible everywhere. A `Support/Subfmls.lean` would have to sit
*above* FmpMeasure (it depends on `modalSubfmls`/`modalUniverse` defined there), which buys
nothing and adds a module.

> **Recommendation**: drop `Support/Subfmls.lean` from the plan. De-privatize the Subfmls/Universe
> facts in place in FmpMeasure.lean. Only `Support/Accessibility.lean` and `Support/KnownWorlds.lean`
> earn their existence — and they earn it because Branch.lean is do-not-edit.

**Tier 3 — above FmpMeasure (16 families, 16 duplicate declarations). Fits none of the three modules.**

| Origin | Families | Note |
|---|---|---|
| CompletenessLoop.lean | 3 | `modalStepBranchGen_newExps_const`, `hasEdge_addEdge_mono`, `modalStepHintikka_preserves_inv` |
| TDriver.lean | 3 | `modalApplyOne_boxPos_acc_eq`, `modalApplyOne_diamondNeg_acc_eq`, `not_shape_of_not_or` |
| FmpMeasure.lean (original already PUBLIC) | 3 | copy exists for reasons other than privacy |
| FiveSimplification.lean | 2 | `modalApplyOne_boxNeg_mint_fst`, `modalApplyOne_diamondPos_mint_fst` |
| Soundness / SoundnessStep | 2 | `accFreshInv_append`, `modalApplyOne_fresh` |
| Completeness.lean | 1 | `modalHintikkaClauseGen_lift` |
| S5Simplification.lean | 1 | `hintikka_congr` |
| FrameSoundness.lean | 1 | `modalApplyOneS5_fresh_local` |

**Flagged**: 8 of these families have an origin that is **already public**
(`modalApplyOne_fresh`, `modalSubfmls_self_mem`, `modalExpMeasure_step_lt`,
`modalApplyOne_diamondPos_outputs_subset`, `modalApplyOne_boxNeg_outputs_subset`,
`hintikka_congr`, `modalStepHintikka_preserves_inv`, `modalApplyOneS5_fresh_local`). Their copies
are **not** caused by privacy and are therefore **out of scope** for this task — they are either
genuine specialisations or gratuitous duplication requiring a separate judgement call. The plan
must not silently delete them.

**Flagged as structurally impossible**: `S5Simplification.lean:1179 modalApplyOneS5_fresh_local_local`
mirrors `FrameSoundness.lean:1824 modalApplyOneS5_fresh_local`, but FrameSoundness **imports**
S5Simplification. The dependency runs the wrong way; this can never be resolved by importing.

---

## 3. Import-Graph Constraints

### 3.1 Current subsystem DAG (Tableau-internal `public import` edges)

```
Defs
├── Branch ── Rules ── Saturation ─┬─ Closure
│                                  ├─ Completeness
│                                  └─ SoundnessStep ── Soundness (+ LoopInduction)
│
FmpMeasure  ← Completeness, SoundnessStep, Saturation
├── GenericDriver
└── LoopChecking ← FmpMeasure, FrameRules
     └── S5Simplification ← FmpMeasure, LoopChecking, GenericDriver
          ├── FiveSimplification ← GenericDriver, S5Simplification
          ├── CompletenessLoop ← FmpMeasure, Completeness, Soundness, GenericDriver, S5Simplification
          │    ├── TDriver, BDriver ← GenericDriver, FrameRules, CompletenessLoop
          └── FrameSoundness ← Soundness, FrameRules, S5Simplification, FiveSimplification
               └── FrameCompleteness ← Completeness, LoopChecking, FrameSoundness, TDriver, BDriver
```

### 3.2 Transitive reachability from each consumer (measured)

| Consumer | reaches Branch | reaches FmpMeasure | reaches Soundness | reaches CompletenessLoop | reaches TDriver |
|---|---|---|---|---|---|
| BDriver | YES | YES | YES | YES | NO |
| FiveSimplification | YES | YES | **NO** | NO | NO |
| FrameCompleteness | YES | YES | YES | YES | YES |
| FrameSoundness | YES | YES | YES | NO | NO |
| LoopChecking | YES | YES | **NO** | NO | NO |
| S5Simplification | YES | YES | **NO** | NO | NO |

**This table is the core justification for the refactor.**

- Every consumer reaches **Branch** and **FmpMeasure** → Tier-2 facts need only de-privatization.
- Three consumers (FiveSimplification, LoopChecking, S5Simplification) do **not** reach
  **Soundness.lean**. So `hasEdge_addEdge_cases` (7 copies, the single largest family)
  **cannot** be fixed by de-privatization — it must be *lowered* to Branch level. That is
  precisely what `Support/Accessibility.lean` accomplishes.
- Note `FmpMeasure.lean:1080 hasEdge_addEdge_cases_local` is itself a re-derivation of the
  Soundness.lean private, because FmpMeasure does not import Soundness either. Extracting to
  `Support/Accessibility.lean` lets **FmpMeasure.lean itself** drop a duplicate.

### 3.3 Cycle risk

**None**, provided the two new modules import only `Cslib.Logics.Modal.Tableau.Branch`:

```
Defs → Branch → Support/Accessibility
             → Support/KnownWorlds
```

`Support/*` would be imported by Soundness.lean, FmpMeasure.lean, and the six consumers. Since
`Support/*` imports nothing above Branch, no back-edge is possible.

### 3.4 Module registration

`Cslib.lean` lists all Tableau modules alphabetically at lines 492-511. The new
`Cslib.Logics.Modal.Tableau.Support.Accessibility` and `...Support.KnownWorlds` **must** be added
there or `lake exe checkInitImports` will fail. No `Support/` subdirectory convention exists
elsewhere in Cslib, but nested subdirectories are used (e.g.
`Cslib/Logics/Propositional/Tableau/Intuitionistic/`), so the layout is consistent.

---

## 4. "Behaviour-Preserving by Construction" — Verification and Audit Reconciliation

The task asserts the extraction is "mechanical and behaviour-preserving by construction."
**This is false for at least two families.** Verified by direct signature comparison.

### 4.1 IDENTICAL — safe to delete and import

**`hasEdge_addEdge_cases` (7 copies + original) — all byte-identical.**
```lean
private lemma hasEdge_addEdge_cases {acc : Accessibility} {w w' a a' : WorldIndex}
    (h : (acc.addEdge w w').hasEdge a a' = true) :
    (a = w ∧ a' = w') ∨ acc.hasEdge a a' = true
```
All seven copies match exactly. `hasEdge_addEdge_cases_anc` (FrameSoundness.lean:1206) renames
`a a'` to `u u'` — alpha-equivalent, harmless. **Verdict: fully mechanical.**

**`mem_modalKnownWorlds` (6 copies + original) — all byte-identical.**
```lean
private lemma mem_modalKnownWorlds
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (x : WorldIndex) :
    x ∈ modalKnownWorlds l ↔ ∃ sf ∈ l, sf.label = x
```
**Verdict: fully mechanical.**

### 4.2 HAZARD — original is STRICTLY STRONGER than its copies

**`modalKnownWorlds_fold_spec` (6 copies).** The private original in FmpMeasure.lean:1733:
```lean
private lemma modalKnownWorlds_fold_spec
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (ws0 : List WorldIndex)
    (hws0 : ws0.Nodup) :
    (l.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) ws0).Nodup ∧
    ∀ x, x ∈ l.foldl (...) ws0 ↔ x ∈ ws0 ∨ ∃ sf ∈ l, sf.label = x
```
All six copies (`_B`, `_C`, `_FS`, `_Five`, `_S4`, `_S5`) are **weaker**:
```lean
private lemma modalKnownWorlds_fold_spec_S5
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (ws0 : List WorldIndex) :
    ∀ x, x ∈ l.foldl (...) ws0 ↔ x ∈ ws0 ∨ ∃ sf ∈ l, sf.label = x
```
They **drop the `hws0 : ws0.Nodup` hypothesis and the `Nodup` conjunct**. This is *not* a
drop-in replacement:
- Every call site currently writes `modalKnownWorlds_fold_spec_S5 l ws0 x`.
- Using the strong original it becomes `(modalKnownWorlds_fold_spec l ws0 hNodup).2 x` — and the
  caller must **produce a `ws0.Nodup` proof it never previously needed**, which may not be
  available at all call sites.

> **Required plan action**: publish **two** lemmas in `Support/KnownWorlds.lean` — the weak
> membership form (matching what the six copies actually prove and what call sites consume) and
> the strong `Nodup`-carrying form. Do **not** try to route all consumers through the strong one.

### 4.3 HAZARD — differing binder form (call sites change)

**`modalKnownWorlds_mono_append` (5 copies).** Original uses `⊆`; all five copies use `∀ x ∈ …`:
```lean
-- FmpMeasure.lean:1822 (original)
private lemma modalKnownWorlds_mono_append (xs b : List (...)) :
    modalKnownWorlds b ⊆ modalKnownWorlds (xs ++ b)

-- all 5 copies
private lemma modalKnownWorlds_mono_append_S5 (xs b : List (...)) :
    ∀ x ∈ modalKnownWorlds b, x ∈ modalKnownWorlds (xs ++ b)
```
`List.Subset` unfolds to a **strict-implicit** binder `⦃a⦄`, whereas the copies bind `x`
explicitly. The propositions are definitionally equal, but the *application syntax differs*:
call sites written `h xs b x hx` must become `h xs b hx`. **Mechanical, but every call site must
be touched** — this is not a pure delete-and-import.

### 4.4 Reconciliation of contradictory audit verdicts

Two parallel audits returned conflicting verdicts. Both were resolved by reading the source
directly. **Neither auditor's `DIFFERENT` count survives inspection**; the reconciled inventory
of genuinely different propositions is **zero**.

#### CONFLICT 1 — `modalMaxWorld_foldl_le` / `modalMaxWorld_le_of_forall_le`

One auditor said **DIFFERENT** ("mechanical import-substitution would fail to unify"); the other
said content is **preserved end-to-end**. **Both are partly right, and both overstate the
consequence.** There are four variants:

| # | Declaration | Binders |
|---|---|---|
| 1 | `FmpMeasure.lean:1869 modalMaxWorld_foldl_le` | `(l) (c M : Nat) (hc) (h)` — all explicit, accumulator `c` |
| 2 | `S5Simplification.lean:1148 …_of_forall_S5w` | `{l} {M init : WorldIndex} (hinit) (h)` — implicit |
| 3 | `FiveSimplification.lean:3311 …_of_forall_Five` | byte-identical to #2 |
| 4 | `LoopChecking.lean:6182 foldl_max_le_of_forall_le` | explicit, `K`, distinct helper |

The first auditor is **factually correct**: these are *not* alpha-equivalent as written. Binder
mode (implicit `{}` vs explicit `()`) and accumulator naming/position genuinely differ.
`WorldIndex` is an `abbrev` for `Nat`, so the types are reducibly defeq and pose no obstacle —
the binder mode is the only real difference.

But the operative question is *what breaks at call sites*, and there the answer is: **almost
nothing.** Measured call-site census:

- **26 of 30 call sites use `apply`** (`modalMaxWorld_le_of_forall_label_le_Five` ×10,
  `modalMaxWorld_le_of_forall_label_le` ×10, `…_S5w` ×4, `modalMaxWorld_le_of_forall_le` ×2).
  `apply` unifies against the conclusion and turns remaining arguments into goals — it is
  **insensitive to binder mode**. Every one of these 26 sites typechecks unchanged after
  substituting any variant.
- **Only 4 call sites are term-mode**, and each is a single line *inside the wrapper lemma's own
  proof* — proofs that are deleted by the refactor anyway:
  - `FmpMeasure.lean:1884` `modalMaxWorld_foldl_le l 0 M (Nat.zero_le _) h`
  - `S5Simplification.lean:1167` `modalMaxWorld_foldl_le_of_forall_S5w (Nat.zero_le M) h`
  - `FiveSimplification.lean:3328` `modalMaxWorld_foldl_le_of_forall_Five (Nat.zero_le M) h`
  - `LoopChecking.lean:6201` `foldl_max_le_of_forall_le l K 0 (Nat.zero_le _) h`

> **Reconciled verdict: CONTENT-EQUIVALENT / BINDER-VARIANT.** Not "identical", not "different".
> Migration is safe under `apply` at 26/30 sites; the 4 term-mode sites are one-line touches
> inside proofs being removed. The plan should pick the **implicit-binder wrapper form**
> (`{l} {M} (h) : modalMaxWorld l ≤ M`) as canonical — it is the form 24 of the 26 `apply` sites
> already expect — and publish the `foldl` helper as internal scaffolding.

#### CONFLICT 2 — the `DIFFERENT` inventory

One auditor reported **3 declarations / 2 pairs** DIFFERENT; the other reported **exactly 1**, and
it was not even the same declaration. Resolved by reading both:

**`hasEdge_mem_successorsOf_origin` (LoopChecking.lean:1350) — auditor #2's sole `DIFFERENT`.**
It is true that this lemma is the **converse** of `mem_successorsOf_hasEdge`:
```lean
mem_successorsOf_hasEdge  : w' ∈ acc.successorsOf w → acc.hasEdge w w' = true   -- FmpMeasure:662
hasEdge_mem_successorsOf  : acc.hasEdge w w' = true → w' ∈ acc.successorsOf w   -- LoopChecking:6764
```
But that observation **misattributes the base**. `hasEdge_mem_successorsOf_origin` is not a
re-derivation of `mem_successorsOf_hasEdge` at all — it is a byte-identical duplicate of
`hasEdge_mem_successorsOf` at **LoopChecking.lean:6764, in the same file**, declared earlier
purely to work around a forward reference (its own docstring says so: *"defined later in this
file, past this section"*). **Verdict: IDENTICAL to its true base.** These are two distinct
facts (a converse pair), each with its own duplicate — not one family with a direction mismatch.

> This one needs **no Support module at all**: moving `hasEdge_mem_successorsOf` earlier within
> LoopChecking.lean removes the duplicate. It is the cheapest deletion in the whole inventory.

**`mem_modalUniverse_of` (3 copies) — flagged by comment prose, but IDENTICAL in fact.**
`FiveSimplification.lean:842` and `S5Simplification.lean:2097` both carry the comment *"swapped
to plain `modalUniverse`/`modalWorldBound`"*. Direct comparison shows all three declarations are
**byte-identical** to `FmpMeasure.lean:440` — same implicit binders `{φ0} {s} {φ} {w}`, same
hypotheses `(hw) (hφ)`, same conclusion, same three-line proof. The comment is **stale prose**
referring to an earlier `modalUniverseS5`/`modalWorldBoundS5` variant that no longer exists.
**Verdict: IDENTICAL.**

> **Warning for the plan**: the tree's comments are not a reliable hazard signal in either
> direction. Here they falsely suggest a deviation; elsewhere (§1.2) they are absent where real
> duplicates exist. Drive off signatures, not docstrings.

**Reconciled `DIFFERENT` inventory: none.** Every audited duplicate is IDENTICAL,
BINDER-VARIANT, or WEAKER (§4.2). No re-derivation proves a genuinely different proposition.

#### The WEAKER family — resolved, and it dissolves

Both auditors agreed `modalKnownWorlds_fold_spec` is WEAKER at 6 sites. Confirmed. The
orchestrator asked whether any consumer uses the dropped `Nodup` conjunct. **Measured answer: no,
and the hazard evaporates entirely.**

Every one of the 6 weak copies has **exactly one call site**, all of identical shape:
```
BDriver.lean:963            simpa using modalKnownWorlds_fold_spec_B l [] x
FrameCompleteness.lean:3792 simpa using modalKnownWorlds_fold_spec_C l [] x
FrameSoundness.lean:2108    simpa using modalKnownWorlds_fold_spec_FS l [] x
FiveSimplification.lean:820 simpa using modalKnownWorlds_fold_spec_Five l [] x
LoopChecking.lean:2952      simpa using modalKnownWorlds_fold_spec_S4 l [] x
S5Simplification.lean:1042  simpa using modalKnownWorlds_fold_spec_S5 l [] x
```
Each sits inside the proof of the corresponding `mem_modalKnownWorlds_X`. Two consequences:

1. `ws0` is **always `[]`**, so the dropped hypothesis is discharged for free by `List.nodup_nil`
   — exactly as FmpMeasure's own original does at line 1785:
   `(modalKnownWorlds_fold_spec l [] List.nodup_nil).2 x`.
2. More decisively: since `mem_modalKnownWorlds` is IDENTICAL across all 7 copies (§4.1),
   publishing it from `Support/KnownWorlds.lean` makes **all six `fold_spec` copies dead code**.
   They are deleted outright — no substitution, no call-site edit, no `Nodup` obligation.

> **The WEAKER family requires no per-site judgment after all.** Publish `mem_modalKnownWorlds`
> and the 6 weak `fold_spec` copies vanish with their sole consumer. Publish the strong
> `modalKnownWorlds_fold_spec` (with `Nodup`) only because `modalKnownWorlds_nodup` needs it.

**Related free deletions found.** `modalKnownWorlds_nodup_S5` (S5Simplification.lean:1079) has
**zero call sites** — dead code. Its helper `modalKnownWorlds_fold_nodup_S5` (:1061) is used only
to prove it. Both can be deleted without any replacement. By contrast
`modalKnownWorlds_nodup_S4` (LoopChecking.lean:6598, **public**, not private) is live with 2 uses
and does need the public `modalKnownWorlds_nodup`.

#### Minor binder note

`modalSubfmls_trans_B` (BDriver.lean:209) binds `{a c : Proposition Atom} {b : Proposition Atom}`
where the original binds `{a b c : Proposition Atom}` — reordered implicit binders, same content.
Harmless: all uses are term-mode with the hypotheses supplied positionally
(`modalSubfmls_trans_B hψ (…)`), which is unaffected by implicit-binder order.

### 4.5 Audit coverage gap (45 pairs audited vs 72 duplicates)

The three parallel audits covered **45 pairs**. The declaration-level census (§1.2) finds **72
duplicate declarations across 41 families**. The 27-declaration gap is accounted for as follows —
it is a coverage gap, **not** a discrepancy in the count:

- **~23 declarations** are the Tier-3 singletons (§2.2) — 16 families with one copy each,
  originating above FmpMeasure (TDriver, CompletenessLoop, Completeness, FiveSimplification,
  S5Simplification, FrameSoundness). These were never dispatched for audit because they are out
  of scope for the three proposed Support modules.
- **~4 declarations** are Tier-2 singletons found only by the suffix census and absent from the
  comment-based site list that seeded the audits (`modalCount_notMem_append_drop_S4`,
  `modalCount_notMem_mono_S4`, `modalWork_drop_linear_S4`, `modalWork_drop_persistent_S4`).

**Every family with 2+ copies was audited.** The unaudited residue is entirely single-copy
Tier-3 material that the plan should triage individually (§7 Phase D), not bulk-process.

### 4.6 The MEASURE group fits none of the three modules

The `modalExpMeasure_split` / `_append` / `_const_exp` family (3 copies, all in
LoopChecking.lean:9804-9836) depends on `modalExpMeasure`, defined at **FmpMeasure.lean:200**.
It is neither Subfmls, nor KnownWorlds, nor Accessibility. This is Tier-2 material: LoopChecking
already reaches FmpMeasure, so **de-privatization in place** resolves all three. It confirms the
three-module partition is incomplete as a taxonomy, but costs nothing to fix.

---

## 5. Do-Not-Edit Constraint Check (Rules.lean / Saturation.lean / Branch.lean)

**No scope conflict on the deletion side.** Verified at both comment level and declaration level:

- Zero of the 55 comment sites are in Rules.lean, Saturation.lean, or Branch.lean.
- Zero of the 72 duplicate declarations are in those three files.
- None of those three files declare any `private` lemma that is re-derived elsewhere.

**However — an important interaction.** Branch.lean at 205 lines owns `Accessibility`, `addEdge`,
`successorsOf`, `hasEdge`, `modalKnownWorlds`, `modalMaxWorld`, `modalNextWorld`, and
`boxPositivesOf`, and it *already* hosts four public lemmas about them (`modalNextWorld_gt`,
`label_le_modalMaxWorld`, `modalMaxWorld_le_append`, `modalNextWorld_le_append`). The
architecturally natural home for the 33 Tier-1 facts is Branch.lean itself. **The do-not-edit
constraint is exactly what makes a separate `Support/` directory the correct answer** rather than
an arbitrary one. This should be stated in the plan's rationale, and in the new modules'
docstrings, so a future reader does not "helpfully" fold them back into Branch.lean.

### 5.1 `file_scope` is incomplete — plan must widen it

state.json declares:
```
Support/, FmpMeasure.lean, Soundness.lean, TDriver.lean, CompletenessLoop.lean
```
This covers the modules that **own private originals** but omits every module where duplicates
must be **deleted**. The six files holding the 72 duplicates are:

```
BDriver.lean  FiveSimplification.lean  FrameCompleteness.lean
FrameSoundness.lean  LoopChecking.lean  S5Simplification.lean
```

Plus `Cslib.lean` (module registration). **Nine files are missing from `file_scope`.** The plan
must widen it or the implementation will be blocked. None of the additions collide with the
do-not-edit list.

---

## 6. Verification Baseline (measured this session, green-to-green reference)

### 6.1 Command set and current output

| Command | Exit | Output at baseline |
|---|---|---|
| `lake build Cslib` | **0** | `Build completed successfully (3311 jobs).` |
| `lake exe checkInitImports` | **0** | *(no output)* |
| `lake exe lint-style` | **0** | *(no output)* |
| `lake shake --add-public --keep-implied --keep-prefix` | **1** | 9 findings — **none in Modal/Tableau/** |

**`lake shake` is NOT clean at baseline.** It exits 1 with import suggestions in
`Cslib/Algorithms/Lean/TimeM.lean`, `Cslib/Computability/Machines/Turing/…`,
`Cslib/Foundations/…`, `Cslib/Languages/CCS/Basic.lean`,
`Cslib/Languages/CombinatoryLogic/Defs.lean`. Mostly `add #[public import
Mathlib.Tactic.Attr.Core]`.

> **The correct post-condition is not "shake exits 0" — it never has.** It is:
> **`lake shake … | grep 'Modal/Tableau'` stays empty, and the finding count stays at 9.**
> A plan that demands a clean shake exit will fail on pre-existing, out-of-scope noise.

### 6.2 Sorry and axiom census

```bash
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'
```

- **Modal/Tableau/ subsystem: exactly 1.**
  `FrameSoundness.lean:1276` (the `sorry` token), belonging to declaration
  `branchSatisfiableIn_s4FC_ancestor_redirect` at `FrameSoundness.lean:1252`.
  The build warning reports the *declaration* position (1252); the grep census reports the
  *token* position (1276). Both refer to the same single retained sorry.
  The task description's "line 1244" is stale — **re-locate by declaration name, never line number.**
- **Repo-wide: 29** code-position sorries (Bimodal 24, Modal/Tableau 1, Propositional 4).
  Note this differs from the orchestrator's "exactly 5" — that figure counts the `declaration
  uses 'sorry'` build warnings from an incremental build, which is an **undercount** (cached
  modules do not re-elaborate and never re-emit warnings). The grep census above is authoritative.
- **Axioms in Modal/Tableau/: 0** (`grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l`).

### 6.3 Must-stay-green declarations

| Declaration | Location |
|---|---|
| `modalTableauS4Keyed_complete` | FrameCompleteness.lean:4271 |
| `instDecidableKValid` | CompletenessLoop.lean:2295 |
| `instDecidableTValid` | FrameCompleteness.lean:1315 |
| `instDecidableBValid` | FrameCompleteness.lean:1931 |
| `instDecidableS5Valid` | FrameCompleteness.lean:2424 |
| `instDecidableFiveValid` | FrameCompleteness.lean:3214 |
| `instDecidableKb5Valid` | FrameCompleteness.lean:4160 |

Five of the seven live in FrameCompleteness.lean, which is also one of the six files losing
duplicates. Recommend a per-commit `lake build Cslib` gate rather than a final-only check.

---

## 7. Recommended Approach (zero-sorry, no deferral)

**Phase A — `Support/Accessibility.lean`** (imports only `…Tableau.Branch`).
Publish `hasEdge_addEdge_cases`, `mem_successorsOf_hasEdge` (+ its converse if genuinely
distinct). Delete 10 duplicates across BDriver, FrameCompleteness ×2, FrameSoundness ×2,
LoopChecking, S5Simplification, and `FmpMeasure.lean:1080`. Remove the now-unused
`private lemma hasEdge_addEdge_cases` from Soundness.lean, redirecting its 1 internal use.

**Phase B — `Support/KnownWorlds.lean`** (imports only `…Tableau.Branch`).
Publish `mem_modalKnownWorlds` (identical across all 7 — the highest-leverage single move in the
task), `modalKnownWorlds_mono_append` in the `∀ x ∈` form, `modalKnownWorlds_nodup`,
`modalKnownWorlds_fold_spec` (strong, `Nodup`-carrying — needed only to prove
`modalKnownWorlds_nodup`), `mem_boxPositivesOf`, and `modalMaxWorld_le_of_forall_label_le` in the
implicit-binder form with its `foldl` helper. Delete 23 duplicates.

> Order matters: publish `mem_modalKnownWorlds` **first**. Doing so strands all six weak
> `modalKnownWorlds_fold_spec_*` copies as dead code, which then delete cleanly with no `Nodup`
> obligation and no call-site edits (§4.4). Publishing the strong `fold_spec` first and trying to
> route the six copies through it is the harder path and is not necessary.
> Also delete `modalKnownWorlds_nodup_S5` and `modalKnownWorlds_fold_nodup_S5`
> (S5Simplification.lean:1079, :1061) — already dead, zero call sites, no replacement needed.

**Phase C — de-privatize Tier-2 facts in place in FmpMeasure.lean.**
No new module. Remove `private` from the ~14 re-derived declarations, add docstrings (docBlame
requires them once public). Delete 23 duplicates across the six consumers.

**Phase D — Tier-3 triage.** Do **not** attempt mechanically. Document the 16 families,
resolve the ones whose origin is genuinely private and reachable, and explicitly record the
8 public-origin families and the structurally-impossible `modalApplyOneS5_fresh_local_local`
as out of scope.

**Lint prevention** (all newly-public declarations): docstrings required (docBlame);
`lemma`/`theorem` not `def` for Prop-valued (defLemma); lowerCamelCase without underscores in
*definition* names (existing snake_case lemma names are conventional in this subsystem and match
Mathlib practice — preserve them); minimal section variables with `omit` where needed
(unusedSectionVars — note the existing `omit [DecidableEq Atom] [Hashable Atom] in` pattern at
BDriver.lean:208); explicit namespace wrapping (topNamespace).

**Zero-debt compliance**: every phase is a delete-and-redirect over already-proven facts. No
phase introduces a proof obligation that does not already have a proof in the tree. **No `sorry`
is needed at any point, and none should be accepted.** The one retained sorry
(`branchSatisfiableIn_s4FC_ancestor_redirect`) is untouched by all four phases.

---

## 8. Risk Stratification — safe bulk vs. per-site judgment

The plan **must not treat all 72 duplicates uniformly**. Reconciled split:

**Safe bulk — 56 declarations, pure delete-and-import, no judgment needed:**

| Family | Copies | Basis |
|---|---|---|
| `hasEdge_addEdge_cases` | 7 | byte-identical (§4.1) |
| `mem_modalKnownWorlds` | 6 | byte-identical (§4.1) |
| `modalKnownWorlds_fold_spec` | 6 | become dead code once `mem_modalKnownWorlds` is published (§4.4) |
| `modalSubfmls_trans` | 4 | identical modulo implicit-binder order |
| `mem_modalUniverse_of` | 3 | byte-identical — comment prose is stale (§4.4) |
| `modalUniverse_mem_formula` | 3 | identical |
| `mem_successorsOf_hasEdge` | 2 | identical |
| `mem_boxPositivesOf` | 2 | identical |
| `hasEdge_mem_successorsOf` | 1 | intra-file duplicate; fix by reordering LoopChecking.lean |
| `modalKnownWorlds_nodup_S5` + `_fold_nodup_S5` | 2 | **dead code, zero call sites** — free deletion |
| Tier-2 singletons | ~20 | de-privatize in place |

**Needs per-site judgment — 16 declarations:**

| Item | Why |
|---|---|
| `modalKnownWorlds_mono_append` (5) | `⊆` vs `∀ x ∈` — content-equal, but every call site changes arity (§4.3) |
| `modalMaxWorld` family (3) | binder-variant; 4 term-mode sites need a one-line touch (§4.4) |
| 8 public-origin families | duplication is **not** caused by privacy; may be genuine specialisation — out of scope |

## 9. Open Questions for the Plan

1. Should `outDeg` (FmpMeasure.lean:804, a one-line wrapper over `successorsOf`) move down to
   `Support/Accessibility.lean`? Doing so lets `outDeg_addEdge_self/_ne` join Tier 1. Cost: moving
   a `def`, which is a behaviour-relevant change (`shake`/`checkInitImports` must confirm).
2. Adopt the `∀ x ∈` form or the `⊆` form as the canonical public
   `modalKnownWorlds_mono_append`? The `∀ x ∈` form matches all five call-site populations and
   minimises churn; the `⊆` form is more idiomatic Lean/Mathlib. **Recommend `∀ x ∈`** —
   the FmpMeasure original is the *only* `⊆` user, and it has 2 internal call sites vs 5
   external populations.
3. For the `modalMaxWorld` wrapper, confirm the implicit-binder form `{l} {M} (h)` as canonical
   (§4.4 recommends it: 24 of 26 `apply` sites already expect it).
4. Should the 8 public-origin duplicate families be split into a follow-up task? They are not
   caused by privacy and do not belong to this task's stated scope.

---

## 10. Verification Command Set (for the implementation phase)

```bash
lake build Cslib                                        # must exit 0, 3311+ jobs
lake exe checkInitImports                               # must exit 0, no output
lake exe lint-style                                     # must exit 0, no output
lake shake --add-public --keep-implied --keep-prefix \
  2>&1 | grep 'Modal/Tableau'                           # must stay EMPTY (exit 1 overall is baseline)

# sorry census — must return exactly the FrameSoundness line
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'

grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l  # must stay 0
grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' Cslib/  # locate retained sorry by NAME
```

Progress metric (declaration-level, not comment-level):

```bash
# duplicate-declaration census — should fall from 72 toward the Tier-3 residue (~16)
# (regenerate with the suffix-family script recorded in this report, section 1.2)
grep -rho 'Local re-derivation' Cslib/ | wc -l   # secondary signal only; 57 at baseline
```
