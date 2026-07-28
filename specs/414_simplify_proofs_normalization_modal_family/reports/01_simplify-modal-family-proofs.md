# Research Report: Simplify Verbose Modal/Temporal/Bimodal Proofs

**Task**: 414
**Type**: cslib
**Session**: sess_1785258473_63f7b4_414
**Date**: 2026-07-28

## Scope Reconciliation

The original task premise cited "co-tags" from an abandoned task. This report is re-scoped to
the normalization and embedding lemmas that **actually exist today**, and to proof sites in
`Cslib/Logics/{Modal,Temporal,Bimodal}/` that fail to exploit them.

All simplifications below were **empirically verified** with `lean_multi_attempt` against the
live LSP (warm build, commit `aaa0e3cf`). No files were edited during research. Verification
notes distinguish confirmed wins from untested extrapolations and from confirmed dead ends.

## Reuse Check Protocol (completed)

Existing abstractions were enumerated before any recommendation was formed.

### Foundations — normalization lemmas that already exist

| Lemma | File | Attributes |
|---|---|---|
| `listImp_nil`, `listImp_cons` | `Cslib/Foundations/Logic/Metalogic/ListImplication.lean:51,54` | `@[simp, scoped grind =]` |
| `listImp_axiom_k`, `listImp_axiom_s` | `Cslib/Foundations/Logic/Metalogic/ListImplication.lean:61,77` | — |
| `list_flip_implication1/2` | `Cslib/Foundations/Logic/Metalogic/ListImplication.lean:111,146` | — |
| `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `negBigconj_def` | `Cslib/Foundations/Logic/Theorems/BigConj.lean:73,77,80,88` | `@[simp, scoped grind =]` |
| `bigconj_mem_derivable`, `bigconj_derivable_intro` | `Cslib/Foundations/Logic/Theorems/BigConj.lean:103,122` | — |
| `ListDeriv` (def), `list_deduction_theorem`, `list_deriv_reflection`, `list_deriv_mp`, `list_deriv_monotonic` | `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean:48,56,69,89,101` | — |

### Logics — embedding equation lemmas that already exist

| Family | File | Notes |
|---|---|---|
| `Modal.Proposition.toBimodal_{atom,bot,imp,and,or,box}` | `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean:47-76` | all `@[simp]`, all `rfl` |
| `Modal.Proposition.toBimodal_{neg,diamond}` | `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean:79,83` | **not** `@[simp]` (derived `abbrev`s) |
| `Temporal.Formula.toBimodal_{atom,bot,imp,untl,snce,neg,allFuture,allPast}` | `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean:50-89` | — |
| `PL.Proposition.toBimodal_{eq_embed,and,or,neg}`, `toTemporal_toBimodal` | `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean:68-100` | — |
| `PL.Proposition.toTemporal_{eq_embed,and,or,neg}` | `Cslib/Logics/Temporal/FromPropositional.lean:51-73` | — |

**Conclusion of reuse check**: the lemma inventory is adequate. No new abstraction is required
for any recommended change. One optional new Foundations lemma is discussed in F4 and is
**recommended against**.

## Findings

### F1 (HIGH VALUE, VERIFIED) — `unfold ListDeriv; simp only [listImp_nil]` is entirely redundant

`ListDeriv Γ φ` is *defined* as `InferenceSystem.DerivableIn S (listImp Γ φ)`
(`ListDeduction.lean:48`) and `listImp [] φ = φ` holds by `rfl` (`ListImplication.lean:51`).
Therefore `ListDeriv [] φ` is **definitionally** `InferenceSystem.DerivableIn S φ`, and `exact`
closes across this defeq with no normalization tactics at all.

The codebase nonetheless spells out the conversion by hand at 14 sites.

**Verified evidence** (`lean_multi_attempt`, all returning zero goals and zero diagnostics):

| Site | Current | Verified replacement |
|---|---|---|
| `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean:188` | `unfold ListDeriv at ih; simp only [listImp_nil] at ih; exact ih` | `exact ih` |
| `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean:169` | same | `exact ih` |
| `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean:189` | `unfold ListDeriv; simp only [listImp_nil]` (line before the `exact`) | **delete the line entirely** — verified that `exact ⟨Bimodal.DerivationTree.necessitation ψ h_thm.toDerivation⟩` closes the goal on its own (the following line then reports "No goals to be solved") |

**Important negative**: `simpa using ih` **fails** here with a type mismatch — `simp` normalizes
the hypothesis but its final `assumption` step does not see through the `ListDeriv` definition.
The replacement must be `exact`, never `simpa`.

**All sites** (from `grep -rn listImp_nil --include=*.lean Cslib/`):

- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — lines 188, 189, 194, 195, 200, 203
  (three near-identical cases: `necessitation`, `temporal_necessitation`, `temporal_duality`)
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — lines 169, 170, 175, 178
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — lines 136-137, 140-141
- `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` — lines 110, 125 (same idiom; in
  Foundations rather than Logics, so strictly outside the task's directory scope — include only
  if the implementer wants the family fixed consistently)

Repo-wide there are **24** `unfold ListDeriv` occurrences; the ones not in the list above
(e.g. in `ListDeduction.lean` itself, `GenericMCS.lean:255`) operate on non-empty contexts and
are likely still required. Each must be checked individually.

**Estimated reduction**: ~14 tactic lines removed, plus the `have h_thm : ... := by <3 tactics>`
blocks collapse to `have h_thm : ... := ih` (or inline). Roughly 6 lines → 3 lines per
`necessitation`-style case, across 6 cases in three files.

### F2 (HIGH VALUE, VERIFIED) — ModalConservativity `and`/`or` cases: 11 lines → 2

`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ModalConservativity.lean`

The `and` case (lines 164-174) and `or` case (lines 175-185) each hand-roll classical reasoning
(`by_contra`, `Classical.em`, `absurd`) over the Łukasiewicz encoding of `∧`/`∨`. Rewriting the
induction hypotheses **backward** first turns each goal into a pure two-atom propositional
tautology that `tauto` discharges.

**Verified** — `and` case, entire lines 165-174 replaced by one line:

```lean
simp only [Modal.Proposition.toBimodal, Bimodal.Formula.and, truthAt, Modal.Satisfies,
  ← ih1 w, ← ih2 w]; tauto
```

Returns zero goals; the following line reports "No goals to be solved", confirming the case is
fully closed.

**Verified** — `or` case, lines 177-185 replaced by one line (existing `simp only` at line 176
retained):

```lean
simp only [← ih1 w, ← ih2 w]; tauto
```

Returns zero goals. The merged single-`simp only` form (matching the `and` case shape) is
untested but is the same shape and is the recommended first attempt.

**Important negatives** — the backward IH rewrite is *essential*:

- plain `tauto` fails (goal still mentions `truthAt`, not `Satisfies`)
- `constructor <;> tauto` fails, leaving four residual goals requiring `ih1`/`ih2`
- `rw [← ih1 w, ← ih2 w]` fails — the IHs are `let`-bound statements
  (`let ℱ := ...; let M := ...; let Omega := ...; _ ↔ _`), which `rw` rejects as "not an
  equality or iff proof". `simp only [← ...]` handles the `let` binders and is required.

### F3 (VERIFIED DEAD END) — do NOT touch the `box` / `diamond` cases

`ModalConservativity.lean:186-210` (`box`) and `211-229` (`diamond`).

`simp only [← ih w]` on the `diamond` goal reports **"simp made no progress"**. The reason is
structural, not tactical: `ih` is stated at the fixed world `w`, while the goal quantifies over
accessible histories `σ` / worlds `w'`. The IH simply does not match. The existing proofs' work
— the `kripkeAdapterOmega_eq_of_accessible` rewrites that transport `Omega` between `w` and `w'`
using S5 transitivity/Euclideanness — is genuinely load-bearing.

The same argument applies to the `box` case. **These 44 lines should be left alone.** Any
implementation plan that proposes golfing them is chasing a dead end.

### F4 (RECOMMENDED AGAINST) — new `listDeriv_nil` lemma

`lean_local_search "listDeriv_nil"` returns **0 hits** — no such lemma exists. One could add to
`Cslib/Foundations/Logic/Metalogic/ListDeduction.lean`:

```lean
@[simp] theorem listDeriv_nil (φ : F) :
    ListDeriv (S := S) [] φ ↔ InferenceSystem.DerivableIn S φ := Iff.rfl
```

**Recommendation: do not add it.** F1 already eliminates every site by *deletion*, so the lemma
would have no consumers. It is also a new `@[simp]` declaration whose LHS is headed by a `def`
that is definitionally its own RHS, which is a plausible `simpNF` lint trigger. If a future task
wants the defeq to be *discoverable* (documentation value), that is a separate judgement call
and should be raised with the maintainer rather than smuggled in as proof golf.

### F5 (OUT OF SCOPE, FLAGGED) — duplicated `bigconj`

Two independent `bigconj` definitions coexist:

- `Cslib.Logic.Theorems.BigConj.bigconj` — `Cslib/Foundations/Logic/Theorems/BigConj.lean:60`,
  generic over `[HasBot F] [HasImp F]`, Łukasiewicz encoding
  `φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥`
- `Cslib.Logic.Temporal.bigconj` — `Cslib/Logics/Temporal/Syntax/BigConj.lean:32`, uses native
  `Formula.and` / `Formula.neg`

These are **not** definitionally interchangeable (native vs. encoded conjunction), so unifying
them is a real semantic refactor with downstream proof obligations, not proof golf. It is out of
scope for this task. Recommend a separate task if desired.

### F6 (LOW VALUE) — `simp only [<def name>]` vs. equation lemmas

Several sites write `simp only [Modal.Proposition.toBimodal, ...]` / `simp only
[Temporal.Formula.toBimodal, ...]` (unfolding the definition) even though `@[simp]`-tagged
equation lemmas (`toBimodal_atom`, `toBimodal_imp`, …) exist. Because these are `simp only` with
an explicit lemma list, Lean uses the auto-generated equation lemmas either way — the behaviour
is equivalent and the line count is unchanged. **No action recommended**; noted only so a future
reader does not re-litigate it.

Sites, for the record: `ModalConservativity.lean:156,159,161,165,176,187,212`;
`TemporalConservativity.lean:161,165,167,171,178`. Note that
`TemporalConservativity.lean:185,188` already use the named lemmas
(`Temporal.Formula.toBimodal_allFuture`, `toBimodal_allPast`) — the good pattern.

## Prior Consolidation Already Done

`Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean:270-275` carries an explicit
maintainer note that `bimodal_deriv_iff_algebraic` is "already the maximally consolidated shape
for the Temporal/Bimodal base bridges", with a documented reason (`Bimodal.HilbertTM` is a
bespoke `InferenceSystem` tag, so `HilbertTree` instance search for the generic assembler
fails). Do not attempt to route it through `GenericMCS.deriv_iff_algebraic_of_forward` — that
has been tried and documented as failing.

## Recommended Implementation Sequencing

Ordered by verified confidence and by build-blast-radius (Foundations last, since it triggers
the widest rebuild).

1. **Phase 1 — ModalConservativity `and` + `or`** (F2). Single file, two cases, ~18 lines
   removed. Highest verified confidence. Verify with
   `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.ModalConservativity`.
2. **Phase 2 — Bimodal `GenericMCSBridge`** (F1). Three cases, lines 185-204. Verify with
   `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge`.
3. **Phase 3 — Temporal + Modal `GenericMCSBridge`** (F1). Same idiom, fewer sites.
4. **Phase 4 (optional) — `MCSProperties.lean:110,125`** (F1 in Foundations). Wider rebuild;
   include only if the maintainer wants the idiom fixed library-wide.
5. **Final** — full `lake build`, then `lake lint` and `lake exe lint-style`.

## Zero-Debt Compliance

Every recommendation is a **proof-body edit only**: no new axioms, no `sorry`, no new
declarations (F4's candidate lemma is explicitly recommended against), no signature changes, no
vacuous definitions. Each edit either compiles or does not; there is no partial-completion
failure mode. If any individual site does not compile after the change, the correct response is
to **revert that one site** and leave the original proof — the original proofs are all
sorry-free today and remain the fallback. No site requires a `[BLOCKED]` escalation.

## Tactic Survey Results

Tactics tested against real goals in this codebase, with outcomes:

| Tactic | Target | Outcome |
|---|---|---|
| `exact ih` | `ListDeriv [] ψ` → `DerivableIn S ψ` | **works** (defeq) |
| `simpa using ih` | same | **fails** (type mismatch after simp) |
| `simp only [← ih1 w, ← ih2 w]; tauto` | ModalConservativity `and`, `or` | **works**, closes case |
| `tauto` | ModalConservativity `and` | fails |
| `constructor <;> tauto` | ModalConservativity `and` | fails (4 residual goals) |
| `rw [← ih1 w, ← ih2 w]` | ModalConservativity `and` | fails (`let`-bound IH) |
| `simp only [← ih w]` | ModalConservativity `diamond` | fails ("no progress") |

`aesop`, `omega`, `decide`, `norm_num`, `ring`, `linarith`, `positivity` are not applicable:
these goals are propositional/modal-semantic, with no arithmetic or algebraic content, and the
decidable-instance and numeric tactics have no purchase. `aesop` was not tested on the `and`/`or`
cases because `tauto` already closes them in one line.

## Appendix: Broader Landscape (OUT OF SCOPE — candidates for separate tasks)

A full survey of `Cslib/Logics/{Modal,Temporal,Bimodal}/` turned up far larger duplication than
this task's "lower priority proof-golf" framing covers. These are recorded so the opportunity is
not lost, but they are **explicitly not** part of this task: each is a multi-hundred-line
refactor with real regression risk, not a mechanical simplification.

### A1 — Four cloned tableau soundness mega-proofs (~2,200 lines)

`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`:

| Declaration | Lines | Diff vs. previous |
|---|---|---|
| `modalStepBranchGen_preserves_satIn` | 195-733 (539) | — |
| `modalStepBranchS5Gen_preserves_satIn` | 2588-3130 (543) | 88 lines differ |
| `modalStepBranchFive_preserves_satIn` | 3842-4389 (548) | 53 lines differ |
| `modalStepBranchKb5''_preserves_satIn` | 4585-5137 (553) | 51 lines differ |

Within these, one 9-line block (`simp only [Option.some.injEq, Prod.mk.injEq] at hsf; obtain …;
subst …; refine ⟨nf ++ b, List.mem_cons_self, W, m, f, hFC, hacc, ?_⟩; intro sf' hmem'; simp only
[List.mem_append] at hmem'; rcases …`) recurs **16 times** (count verified by grep) at lines
248, 269, 289, 310, 2644, 2665, 2686, 2707, 3899, 3920, 3941, 3962, 4642, 4663, 4684, 4705.
Extracting it as a helper lemma is the single highest-leverage change in the whole modal family.

### A2 — `LoopChecking.lean` repeated motifs

`Cslib/Logics/Modal/Tableau/LoopChecking.lean` — a 5-line `modalStepBranchS4KeyedOrdered_selected_mem`
+ `List.any_eq_false` motif recurs 15 times (2394, 2615, 2818, 3786, 4010, 4220, 4527, 4855,
5281, 5685, 6024, 6422, 7343, 7552, 10048); the `modalApplyOneS4Keyed = modalApplyOne` bridging
`have` recurs 14 times each for `.diamond` and `.box`. Six `_preserves_X` sibling pairs
(`…S4_` vs `…S4KeyedOrdered_`) are ~85% identical across ~2,000 lines.

### A3 — Bimodal soundness axiom-case clones

`Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean:177-567` (`axiom_swap_valid`, 391
lines) and `…/FrameClassVariants.lean:31-322` (`axiom_swap_valid_general`, 292 lines) — the
latter's own header comment concedes it "reproduces the proofs from `axiom_swap_valid`". Same
for `axiom_locally_valid` (`DenseValidity.lean:755-1039`) vs `axiom_locally_valid_general`
(`FrameClassVariants.lean:323-590`), ~60% duplicate.

### A4 — Untagged `truthAt` characterisation lemmas

`Cslib/Logics/Bimodal/Semantics/Truth.lean` has `someFuture_iff` (:158), `somePast_iff` (:178),
`future_iff` (:198), `past_iff` (:222) tagged `@[simp]`, but `bot_false` (:76), `imp_iff` (:90),
`atom_iff_of_domain` (:106), and `box_iff` (:142) are **not** tagged (verified). Meanwhile
`simp only [… truthAt …]` appears 158 times across
`Cslib/Logics/Bimodal/Metalogic/Soundness/` (DenseValidity 60, Soundness 52,
FrameClassVariants 40, Core 6 — verified by grep).

Tagging the four lemmas would let many of those sites use named lemmas. **But this is not safe
proof golf**: adding `@[simp]` lemmas changes the default simp set globally, can break unrelated
proofs across the library, and `box_iff`/`atom_iff_of_domain` have side conditions that make
them plausible `simpNF` offenders. This needs its own task with a full `lake build` gate.

The analogous situation exists for `Modal.Satisfies` (characterisation lemmas at
`Cslib/Logics/Modal/Basic.lean:252-264`, ~110 raw-unfold sites) and `Temporal.Satisfies`
(`Cslib/Logics/Temporal/Semantics/Satisfies.lean:89-174`, ~25 raw-unfold sites).

### A5 — Cross-directory clone

`Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Splitting.lean:268-460` and
`Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/XuGuard.lean:594-808`
(`lemma_2_7_seed_consistent`) share an identical proof skeleton over different types; likewise
`Splitting.lean:545-735` vs `XuGuard.lean:918-1110` (`lemma_2_8_seed_consistent`).

### A6 — Repeated hypothesis bundles (signature, not tactic, boilerplate)

`Cslib/Logics/Modal/Metalogic/Minimal/MinExtension.lean` repeats an 8-line hypothesis bundle at
15 sites (111, 288, 335, 417, 735, 849, 957, 1035, 1113, 1205, 1245, 1421, 1455, 1487, 1548);
the same pattern appears across `Cslib/Logics/Modal/Metalogic/Intuitionistic/`. A `structure` or
`variable` block would absorb these.

**Recommendation**: spawn separate tasks for A1 (highest leverage), A4 (needs a careful
simp-set-change gate), and A3. A2/A5/A6 are lower priority. None of them belongs in this task.

## Open Questions for the Implementer

1. In F1, after removing the normalization tactics, is the `have h_thm : ... := ih` indirection
   still worth keeping for readability, or should `ih` be inlined into the final `exact`? The
   `.toDerivation` projection in the `exact` needs the `DerivableIn` type ascription, so the
   `have` may still be the cleaner form. Test both.
2. In F2, does the merged single-`simp only` form work for the `or` case as it does for `and`?
   Verified for `and`; extrapolated for `or`.
