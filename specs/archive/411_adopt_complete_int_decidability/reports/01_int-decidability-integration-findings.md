# Report: Integrating `IntDecidability` from `refactor/prop_logic` into `main`

- **Task**: 411 `adopt_complete_int_decidability` (parent 370)
- **Type**: cslib / research
- **Date**: 2026-06-29
- **Author**: orchestration findings (session sess_1782758338_7b4e50)
- **Scope**: How to bring the branch `refactor/prop_logic`'s Int-decidability work into `main`
  at highest quality, and what remains open for research.
- **Baselines**: `main` HEAD `07792009` (task 385 finalized); branch `refactor/prop_logic`
  HEAD `4722123c` (tasks 415/416 + 408 orchestration).

---

## 1. Executive summary

`main` and `refactor/prop_logic` independently worked the **same** intuitionistic
FMP-decidability file from a common broken ancestor (`IntFMPSpike.lean`). The result is a
semantic — not textual — conflict:

- **`main` (task 385)** fixed and **renamed** the spike to `IntDecidability.lean` to make
  `lake build` green, but the file **stops at `int_fin_imp_witness`** and delivers **no
  `Decidable` instance**.
- **The branch (tasks 415/416)** **deleted** the spike and authored a **complete**
  `IntDecidability.lean` that reaches `instDecidableDerivableIntPropAxiom'`, CI-green,
  no `sorryAx`.

**Highest-quality resolution: do not `git merge`.** Adopt the branch's complete
`IntDecidability.lean` as a **single-file swap** onto `main`, keeping everything else of
`main`'s. This was verified build-safe (only one unused-lemma dependency drift, already
accounted for). It upgrades `main` from "green but no decidability instance" to "green **with**
the decidability theorem" — the actual goal of parent task 370 — with zero metadata corruption.

---

## 2. Root cause of the conflict: two task lineages, one file

| | `main` (task 385) | `refactor/prop_logic` (415/416) |
|---|---|---|
| Action on the spike | renamed `IntFMPSpike.lean` → `IntDecidability.lean`, re-enabled import | deleted `IntFMPSpike.lean`, wrote fresh `IntDecidability.lean` |
| `IntDecidability.lean` | 272 lines, 7 decls | 436 lines, 10 decls |
| Final `Decidable` instance | **absent** (stops at `int_fin_imp_witness`) | **`instDecidableDerivableIntPropAxiom'`** (line 430) |
| Build | green (build-unblock only) | green + full CI, `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx` |

Because the path `IntDecidability.lean` was *created* on both sides with no common ancestor for
that path, `git merge` reports an **add/add conflict** on it, plus a **rename/delete conflict**
on `IntFMPSpike.lean`. Git would try to interleave two proof styles line-by-line — the wrong
operation. The correct unit of resolution is the **whole file**.

### Shared lineage (proof both versions share, in order)
```
IntFinWorld (structure) → IntFinWorld.ext → instPreorderIntFinWorld →
intFinWorld_carrier_injective → instFintypeIntFinWorld →
intFinWorld_propConsistent → int_fin_imp_witness        ← main STOPS here
```
### Branch-only completion (the 5 decls `main` lacks)
```
intFinVal → intFinVal_upward_closed → int_fin_truth_lemma →
int_fmp → instDecidableDerivableIntPropAxiom'            ← the actual decidability result
```

The branch version is a **strict completion** of `main`'s construction (it also refactors a
few shared signatures, e.g. `int_fin_imp_witness {φ}` implicit vs `main`'s `(φ)` explicit —
which is why the file diff shows +292/−127 rather than a pure append).

---

## 3. Build-safety verification (why the single-file swap is safe on `main`)

The branch `IntDecidability.lean` imports:
```
Cslib.Init                                         (SAME on both branches)
Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness   (DIFFERS — see below)
Cslib.Logics.Propositional.Subformula              (SAME)
Mathlib.Data.Finset.Powerset                       (external)
```

**Only drift: `IntStrongCompleteness.lean` (`main` vs branch = +0/−11).** The 11 lines are a
single auxiliary lemma with its docstring:
```
lemma intBotMem_iff_false (w : IntCanonicalWorld Atom) :
    (⊥ : PL.Proposition Atom) ∈ w.val ↔ False
```
- The branch **deleted** it; `main` keeps it.
- The complete `IntDecidability.lean` **does not reference** `intBotMem_iff_false` (grep: 0 hits).
- `main`'s `MinStrongCompleteness.lean:98` has a **docstring** that references it.

**Conclusion:** keep `main`'s `IntStrongCompleteness.lean` unchanged. The branch's
`IntDecidability.lean` compiles against it exactly as it does on the branch (the extra lemma is
inert for our file), and keeping it avoids orphaning the `MinStrongCompleteness` docstring
reference. The branch's deletion was strictly worse — do **not** adopt it.

**Grind-lint coupling (already satisfied):** the complete file makes the auto-generated
`Cslib.Logic.PL.IntFinWorld.mk.sizeOf_spec` theorem visible to grind analysis. `main`'s
`CslibTests/GrindLint.lean:79` **already** contains `#grind_lint skip
Cslib.Logic.PL.IntFinWorld.mk.sizeOf_spec`. So no grind-lint edit is needed — a subtlety a blind
line-merge would likely have missed.

**Import:** `main`'s `Cslib.lean:~420` already imports `IntDecidability` (task 385 re-enabled it).
The swap leaves it valid.

---

## 4. File-by-file resolution policy

| File | Conflict class | Resolution | Rationale |
|------|----------------|------------|-----------|
| `IntDecidability.lean` | add/add (semantic) | **take branch (complete)** | strict completion; build-safe; delivers the instance |
| `IntFMPSpike.lean` | rename/delete | **stays deleted** | both sides agree it's superseded |
| `IntStrongCompleteness.lean` | content (−11) | **keep main** | branch deleted a lemma `main`'s docstring still cites |
| `Scheme.lean` | content (convergent) | **keep main** | both at 2 sorries deferred-to-317; main has sequencing comments |
| `CslibTests/GrindLint.lean` | content (convergent) | **keep main** | already has the needed skip (line 79) |
| `specs/state.json`, `TODO.md`, multi-state | content | **keep main** | task numbers 408–416 are a **number fork** (different tasks); union impossible |
| Temporal FMP — 6 files (§6) | none (new) | **optional additive** | absent from `main`; independent of Int work |

> **The entire substantive conflict reduces to one file swap.** Everything else is "keep main."

---

## 5. Verification / acceptance (for the implementation pass)

1. `main`'s `IntDecidability.lean` contains `instDecidableDerivableIntPropAxiom'`
   (a `Decidable (Derivable IntPropAxiom φ)` instance).
2. `lake build` green for the whole library; `lake test`, `lake exe checkInitImports`,
   `lake exe lint-style`, `lake shake` all pass.
3. `#print axioms instDecidableDerivableIntPropAxiom'` (or `lean_verify`) shows **only**
   `propext`, `Classical.choice`, `Quot.sound` — **no `sorryAx`**.
4. No new `sorry`/`admit`; `main`'s pre-existing `Scheme.lean` sorries (deferred-to-317) untouched.
5. No metadata corruption: `specs/state.json` / `TODO.md` unchanged except this task's status.

---

## 6. Optional secondary scope — Temporal FMP decidability (task 408 on branch)

Six files exist **only** on the branch (`main` has none of them):
```
Cslib/Logics/Temporal/Metalogic/Decidability/Decidability.lean
Cslib/Logics/Temporal/Metalogic/Decidability/FMP/FMP.lean
Cslib/Logics/Temporal/Metalogic/Decidability/FMP/Filtration.lean
Cslib/Logics/Temporal/Metalogic/Decidability/FMP/FiniteModel.lean
Cslib/Logics/Temporal/Metalogic/Decidability/FMP/SubformulaClosure.lean
Cslib/Logics/Temporal/Metalogic/Decidability/FMP/TruthPreservation.lean
```
Their dependencies (`Temporal.Metalogic.Completeness` / `Soundness` / `DenseCompleteness` /
`DenseSoundness`) are already on `main`, so they should build there. This is purely additive
(plus their `Cslib.lean` imports) and **independent** of the Int decidability work. Note `main`
has its own *different* task 408 (`minimal_sequent_calculus_lm`) — these temporal files are not
the same work. Decide separately whether `main` wants this feature now.

---

## 7. Open questions for research

1. **Adopt vs. hand-reconcile.** Is a wholesale file swap acceptable, or should the 5 missing
   declarations be ported onto `main`'s witness-only base by hand (preserving `main`'s shared-decl
   signatures)? The swap is simpler and verified green; the hand-port preserves `main`'s implicit/
   explicit binder choices. Recommendation: swap, then normalize signatures if desired.
2. **The 3 deferred `Scheme.lean` sorries.** `main`'s `Scheme.lean:246` (truthLemma),
   `:519` (hsat), and `Completeness.lean:113` (IValid bridge) are deferred to task 317. They are
   **pre-existing on `main`** and **not** blocked by this task. See item 4.
3. **Task 415 (rule-redesign) is the real fix for those sorries.** Research on the branch
   (task 415) empirically proved `intuitionisticTableau_complete`/`minimalTableau_complete` are
   *false as stated* — the non-branching `T(→)` rule is incomplete (currying
   `((a∧b)→c)→(a→(b→c))` stays open). Closing the deferred sorries requires Fitting's branching
   `T(→)` rule + a Soundness re-proof + threading edges out of `intExpandBranches`. Full analysis:
   branch `specs/415_int_min_tableau_completeness_redesign/.return-meta.json` and
   `specs/317_propositional_tableau_completeness/handoffs/blocker-analysis-01.md`.
4. **Min decidability.** Both spikes were Int-only. Min FMP infra (`min_imp_witness`,
   `min_prime_exclusion`) exists sorry-free on the branch but no Min `Decidable` instance was
   built. Min decidability stays deferred under parent task 370.
5. **Temporal FMP intake** (§6) — wanted on `main` now, or later?

---

## 8. References

- `main` HEAD `07792009` "task 385: finalize IntDecidability rename + grind-lint skip".
- Branch `refactor/prop_logic` HEAD `4722123c`; key commits `05c088e6`/`13b8c986`/`bee0253d`
  (task 416 phases 1–3), `34b10d06` (task 408 orchestration sweep).
- Branch resolution report: `specs/416_int_min_fmp_spike_revise/reports/01_fmp-spike-resolution.md`.
- Branch source file (the deliverable):
  `git show refactor/prop_logic:Cslib/Logics/Propositional/Metalogic/IntDecidability.lean`.
- Drift lemma: `IntStrongCompleteness.lean` `intBotMem_iff_false` (deleted on branch; kept on main);
  cited by `MinStrongCompleteness.lean:98`.
- Grind-lint skip already present: `CslibTests/GrindLint.lean:79`.
