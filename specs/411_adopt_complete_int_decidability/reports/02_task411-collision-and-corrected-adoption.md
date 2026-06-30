# Report: Task 411 stall — task-number fork collision + corrected adoption path

- **Task**: 411 `adopt_complete_int_decidability` (parent 370)
- **Type**: cslib / research (diagnosis)
- **Date**: 2026-06-29
- **Supersedes/extends**: `reports/01_int-decidability-integration-findings.md` (integration analysis
  remains valid; this report corrects the EXECUTION path and re-verifies build-safety).
- **Baselines**: `main` HEAD `6c443815`; branch `refactor/prop_logic` HEAD `1970f234`.

---

## 1. Executive summary — what is actually wrong with 411

The deliverable is fine; the **execution approach is wrong because of a task-number fork collision**.

- **`main` task 411** = `adopt_complete_int_decidability` (status `not_started`) — a curated
  single-file adoption of the branch's complete `IntDecidability.lean` onto main.
- **`refactor/prop_logic` task 411** = `dma_concat_closure` (status `completed`) — an *unrelated*
  DMA automata-concat port (`DetConcat.lean` → `Cslib/Computability/Automata/DA/Concat.lean`).

These are **different tasks sharing the number 411** (the 408–416 number fork that report 01 and the
task description both warned about). The branch's last 22 commits — `1970f234 task 411: complete
orchestration`, `edf8a885 task 411 phase 7: concat_language_eq`, `… concat_toMuller`, `… concatPtr2`,
`… concat_freeSlot` — are all the **automata concat** task, NOT the IntDecidability work.

**Consequence:** any attempt to "merge task 411" from the branch into main lands automata-concat
work (and the colliding fork metadata), never the IntDecidability adoption. That is why
`main:IntDecidability.lean` is still the 272-line witness-only stub and the FMP instance never
appeared. The IntDecidability work on the branch was done under **tasks 415/416**, not 411.

## 2. The deliverable is sound (re-verified)

- `refactor/prop_logic:Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` = **436 lines**,
  reaches `int_fin_truth_lemma` → `int_fmp` → **`instDecidableDerivableIntPropAxiom'`**.
- **Genuinely sorry-free**: the only `sorry` textual matches (lines 16, 29, 429) are the words
  "sorry-free"/"no `sorryAx`" in prose. Zero proof-body sorries.
- Diff vs main's witness stub: **+294 / −130**.

## 3. Build-safety of the single-file swap — RE-VERIFIED (safe)

Report 01 claimed "only drift = the deleted `intBotMem_iff_false`." I checked the transitive deps:

| Sibling file | main vs branch | Matters? |
|---|---|---|
| `IntStrongCompleteness.lean` | **0+/11−** (branch only DELETED `intBotMem_iff_false`) | No — see below |
| `IntLindenbaum.lean` | **87+/29−** (branch's task-416 variant) | No — transitive only |
| `IntSoundness.lean`, `Semantics/SemanticConsequence.lean`, `Subformula.lean` | SAME | No |

The branch's `IntDecidability.lean` `public import`s only `IntStrongCompleteness` + `Subformula` +
`Mathlib.Data.Finset.Powerset` — it does **not** import `IntLindenbaum` directly, and references
`intBotMem_iff_false` **0 times**. Key argument:

- Branch `IntStrongCompleteness` = main `IntStrongCompleteness` **minus** 11 lines (one unused
  lemma). So main's public API for that module is a **superset** of the branch's.
- The branch's `IntDecidability.lean` was type-checked against that **subset** API. Adopting it onto
  main type-checks it against a **superset** → adding the unused lemma back cannot break it.
- `IntLindenbaum`'s 87+/29− divergence is **transitive only** (under `IntStrongCompleteness`).
  main's `IntLindenbaum → IntStrongCompleteness` chain **already builds green** on main, and
  `IntDecidability` sees only `IntStrongCompleteness`'s public interface — not `IntLindenbaum`'s
  internals.

**Verdict:** the swap is build-safe by static reasoning. Residual risk is low and confined to
proof-term defeq drift; the plan gates on an empirical `lake build` to convert "should build" into
"does build," with a contingency if `IntLindenbaum` drift bites.

## 4. Corrected execution (what the revised plan encodes)

1. **DO the curated single-file swap ON MAIN** — `git show refactor/prop_logic:…/IntDecidability.lean
   > main path`. Change nothing else.
2. **DO NOT `git merge refactor/prop_logic`** — it drags in 22 commits of automata-concat work,
   the add/add `IntDecidability.lean` conflict, the rename/delete `IntFMPSpike.lean` conflict, and
   the colliding 408–416 fork metadata. Wrong operation.
3. **Build-verify gate**: full `lake build` + `lake test` + `checkInitImports` + `lint-style` +
   `shake`; `#print axioms instDecidableDerivableIntPropAxiom'` shows only
   `propext`/`Classical.choice`/`Quot.sound`. If `IntLindenbaum` drift breaks the build, backport
   only the specific lemma(s) `IntStrongCompleteness`/`IntDecidability` need (contingency), re-verify.
4. **Leave Scheme.lean / GrindLint / IntStrongCompleteness / specs metadata untouched** (per the
   original 411 scope). The branch's colliding spec dirs must NOT be copied.
5. **Metadata note**: record the task-number collision so future readers don't re-attempt a branch
   merge for 411.

## 5. Downstream

- Unblocks **421** (Min-side FMP) and **422** (route reconciliation), which depend on the FMP
  instance being on main.
- The tableau-route sorries remain **317**'s obligation (unchanged by this adoption).
