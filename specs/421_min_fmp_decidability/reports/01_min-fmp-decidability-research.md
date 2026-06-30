# Research Report: Min-side FMP Decidability (Task 421)

**Task**: Add a sorry-free `Decidable (Derivable MinPropAxiom φ)` instance via the finite
model property, mirroring `IntDecidability.lean` for minimal propositional logic.

**Status**: RESEARCHED — actionable, low-risk. The Min construction is a near-mechanical
mirror of Int that is *strictly simpler* (the consistency machinery vanishes). No blockers.

**Date**: 2026-06-30

---

## 1. Executive Summary

`Cslib/Logics/Propositional/Metalogic/IntDecidability.lean` (436 lines, now on main) is a
direct finite-canonical-Kripke-model construction. Every supporting Min lemma it needs
**already exists** in `MinLindenbaum.lean` / `MinStrongCompleteness.lean` / `MinSoundness.lean`,
with signatures that are exact analogues of the Int ones. The Min port is *easier* than Int
because minimal logic drops the consistency requirement on worlds:

- The Min world type `MinFinWorld` **drops the `consistent` field** entirely.
- The 40-line consistency helper `intFinWorld_propConsistent` **is eliminated** (not needed).
- The `min_imp_witness` / `min_prime_exclusion` lemmas **take no consistency hypothesis**.
- The bot case of the truth lemma is the genuine membership predicate, mirroring
  `min_truth_lemma`'s `| .bot => Iff.rfl`.

The only declarations *added* relative to Int are a `minFinBotForces` definition and its
one-line upward-closure lemma (Int inlines `fun _ => False`; Min cannot, because `⊥` may
legitimately belong to a minimal world).

**No Int helper lacks a Min analogue.** All sub-obligations are covered by existing code.

---

## 2. Declaration-by-Declaration Mapping (the 12 Int decls → Min)

`IntDecidability.lean` actually contains **12** top-level declarations (the task says 10; the
two extra are `IntFinWorld.ext` and the private `intFinWorldOfPrimeDCCS`). Mapping:

| # | Int declaration | Min analogue | Change |
|---|-----------------|--------------|--------|
| 1 | `structure IntFinWorld` (carrier, sub, closed, **consistent**, prime) | `structure MinFinWorld` (carrier, sub, closed, prime) | **DROP `consistent` field**; `closed` uses `SetDerivable MinPropAxiom` |
| 2 | `IntFinWorld.ext` | `MinFinWorld.ext` | identical (`cases; cases; congr`) |
| 3 | `instPreorderIntFinWorld` | `instPreorderMinFinWorld` | identical (carrier inclusion) |
| 4 | `intFinWorld_carrier_injective` | `minFinWorld_carrier_injective` | identical |
| 5 | `instFintypeIntFinWorld` (noncomputable) | `instFintypeMinFinWorld` | identical (`Fintype.ofInjective`) |
| 6 | `intFinWorld_propConsistent` | **ELIMINATED** | not needed — `min_imp_witness` requires no consistency |
| — | *(new)* | `minFinBotForces : MinFinWorld φ → Prop := (⊥ ∈ ·.carrier)` | NEW def (Int inlines `fun _ => False`) |
| — | *(new)* | `minFinBotForces_upward_closed` | NEW lemma, one line `hw hbf` |
| 7 | `int_fin_imp_witness` | `min_fin_imp_witness` | **simpler**: drop consistency step + `consistent'` field; `IntDCCS`→`MinTheory`, `.1.2`→`.1` |
| 8 | `intFinVal` | `minFinVal` | identical (`atom p ∈ w.carrier`) |
| 9 | `intFinVal_upward_closed` | `minFinVal_upward_closed` | identical (`hw hv`) |
| 10 | `int_fin_truth_lemma` | `min_fin_truth_lemma` | **bot case** becomes the `minFinBotForces` membership; uses `minFinBotForces` as the `bot_forces` arg; `IntPropAxiom.*`→`MinPropAxiom.*` |
| 11 | `intFinWorldOfPrimeDCCS` (private) | `minFinWorldOfPrimeTheory` (private) | drop `consistent`; `IntPrimeDCCS`→`MinPrimeTheory`; `hT.1.2`→`hT.1`; drop `int_dccs_bot_not_mem` line |
| 12 | `int_fmp` | `min_fmp` | forward uses `min_soundness_derivable` (6 explicit args incl. bot_forces); backward drops the `int_consistent`/`PropSetConsistent ∅` plumbing |
| 13 | `instDecidableDerivableIntPropAxiom'` | `instDecidableDerivableMinPropAxiom'` | identical (`decidable_of_iff … (min_fmp φ).symm`) |

---

## 3. Key Semantic Difference: No ⊥-Elimination / Explosion

Minimal logic (`MinPropAxiom`) has **no EFQ**. The codebase already encodes this difference
cleanly, and it makes the FMP construction *simpler*, not harder:

### 3a. Worlds need no `⊥ ∉ Σ` / consistency condition
`MinTheory` (`MinLindenbaum.lean:55`) is defined as deductive closure **only** — no
consistency conjunct — whereas `IntDCCS` (`IntLindenbaum.lean:38`) is
`PropSetConsistent ∧ closed`. Documentation at `MinLindenbaum.lean:49-54` states explicitly:
"Unlike `IntDCCS`, there is **no consistency requirement**. A MinTheory `S` may contain `⊥`."

Consequence for the FMP: `MinFinWorld` must **omit the `consistent` field**. A finite Min
world is just `carrier`/`sub`/`closed`/`prime`.

### 3b. `bot_forces` is a genuine predicate, not `fun _ => False`
`MinStrongCompleteness.lean:101` defines `minBotForces w := ⊥ ∈ w.val` and proves
`minBotForces_upward_closed` (line 105) and `minBotForces_iff_botMem := Iff.rfl` (line 113).
The FMP file needs the finite analogue:

```lean
def minFinBotForces {φ} (w : MinFinWorld φ) : Prop := (⊥ : PL.Proposition Atom) ∈ w.carrier
theorem minFinBotForces_upward_closed {φ} {w w' : MinFinWorld φ}
    (hw : w ≤ w') (hbf : minFinBotForces w) : minFinBotForces w' := hw hbf
```

Int's FMP inlines `fun _ => False` everywhere; Min **cannot** because `⊥ ∈ carrier` is
admissible. This is the only place new (non-mirrored) declarations are introduced.

### 3c. Truth lemma bot case **simplifies**
`int_fin_truth_lemma` bot case: `exact ⟨False.elim, w.consistent⟩` (needs the consistent
field). `min_truth_lemma` bot case (the infinite analogue) is `| .bot => Iff.rfl`
(`MinStrongCompleteness.lean:128`). So `min_fin_truth_lemma`'s bot case should be `Iff.rfl`
(since `IForces _ minFinBotForces w .bot` reduces definitionally to `minFinBotForces w =
(⊥ ∈ w.carrier)`).

### 3d. `intFinWorld_propConsistent` is eliminated
This 40-line helper (Int lines 131-169, an all-true-model structural induction feeding
`int_soundness`) exists **only** to supply the `PropSetConsistent` hypothesis to
`intDeductiveClosure_is_dccs` inside `int_fin_imp_witness`. Min's `minDeductiveClosure_is_theory`
(`MinLindenbaum.lean:125`) takes **no** consistency argument, and `min_imp_witness`
(`MinLindenbaum.lean:138`) takes only `MinTheory S`. **The entire helper and its uses
disappear.**

---

## 4. Min Analogues of Every Supporting Lemma (all verified to exist)

| Int helper used by FMP | Min analogue | Location | Notes |
|------------------------|--------------|----------|-------|
| `IntDCCS` (= consistent ∧ closed) | `MinTheory` (= closed only) | `MinLindenbaum.lean:55` | `.1.2` access → direct `.1` |
| `IntPrimeDCCS` (= IntDCCS ∧ prime) | `MinPrimeTheory` (= MinTheory ∧ prime) | `MinLindenbaum.lean:156` | `.1`=theory, `.2`=disjunction |
| `intDeductiveClosure` | `minDeductiveClosure` | `MinLindenbaum.lean:112` | |
| `intDeductiveClosure_is_dccs h_cons` | `minDeductiveClosure_is_theory` | `MinLindenbaum.lean:125` | **no consistency arg** |
| `int_subset_deductive_closure` | `min_subset_deductive_closure` | `MinLindenbaum.lean:118` | |
| `int_imp_witness (IntDCCS) h_not` | `min_imp_witness (MinTheory) h_not` | `MinLindenbaum.lean:138` | **no consistency** |
| `int_prime_exclusion (IntDCCS) h_not` | `min_prime_exclusion (MinTheory) h_not` | `MinLindenbaum.lean:169` | |
| `int_dccs_bot_not_mem` (for `consistent'`) | **N/A — dropped** | — | no consistent field |
| `intDeductiveClosure_iff_SetDerivable` | `minDeductiveClosure_iff_SetDerivable` | `MinStrongCompleteness.lean:243` | both `Iff.rfl` |
| `int_soundness_derivable` (4 args) | `min_soundness_derivable` (6 args: +bot_forces, +bf_uc) | `MinSoundness.lean:115` | returns `MValid` |
| `int_consistent` (∅ consistent, backward dir) | **N/A — dropped** | — | not needed |
| `SetDerivable`, `SetDerivable_mp`, `SetDerivable_of_mem`, `SetDerivable_of_Derivable`, `SetDerivable_weakening`, `SetDerivable_empty_iff` | same (axiom-polymorphic) | shared | instantiate at `MinPropAxiom` |
| `IForces`, `IForces_imp/and/or/atom/bot` | same | `Kripke.lean:81-112` | shared forcing relation |
| `MinPropAxiom.andI/andE1/andE2/orI1/orI2` | exist | `FragmentAxioms.lean:67-271` | confirmed for `.ax [] _ (.andI …)` |
| `Proposition.subformulas`, `IsSubformula.{imp_left,imp_right,and_left,and_right,or_left,or_right,trans}`, `self_mem_subformulas` | shared | `Subformula.lean` | |

**Gap analysis: NONE.** Every Int helper either has a confirmed Min analogue or is dropped
because of the missing-consistency simplification.

---

## 5. Module Location & Imports

**New file**: `Cslib/Logics/Propositional/Metalogic/MinDecidability.lean`

**Header** (mirror Int lines 7-12, swapping the completeness import):

```lean
module

import Cslib.Init
public import Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness
public import Cslib.Logics.Propositional.Subformula
public import Mathlib.Data.Finset.Powerset
```

Verified: `MinStrongCompleteness` is a `public import` chain that re-exports `MinLindenbaum`
(`MinTheory`, `MinPrimeTheory`, `min_imp_witness`, `min_prime_exclusion`,
`minDeductiveClosure*`) and `MinSoundness` (`min_soundness_derivable`). `Subformula` and
`Mathlib.Data.Finset.Powerset` are the same as Int.

**Namespace / preamble** (verbatim from Int lines 46-56):
```lean
@[expose] public section
namespace Cslib.Logic.PL
open Cslib.Logic
universe u
variable {Atom : Type u} [DecidableEq Atom]
attribute [local instance] Classical.propDecidable
```
Note: `[DecidableEq Atom]` is **required** (as in Int) for `Finset (PL.Proposition Atom)` and
`φ.subformulas`. The Min *completeness* files use `{Atom : Type*}` without it, but the FMP
file needs it — match Int exactly.

**Barrel wiring**: add to `Cslib.lean` immediately after line 423
(`public import Cslib.Logics.Propositional.Metalogic.IntDecidability`):
```lean
public import Cslib.Logics.Propositional.Metalogic.MinDecidability
```
Prefer `lake exe mk_all --module` to regenerate the barrel rather than hand-editing.

---

## 6. Proof Difficulty Assessment

| Min declaration | Difficulty vs Int | Rationale |
|-----------------|-------------------|-----------|
| `MinFinWorld` + `ext` + preorder + injective + Fintype | TRIVIAL (=Int, minus a field) | mechanical |
| `minFinBotForces` + upward_closed | TRIVIAL (new, but one-liners) | mirrors `minBotForces` |
| `minFinVal` + upward_closed | TRIVIAL (=Int) | mechanical |
| `min_fin_imp_witness` | EASIER than Int | drops consistency step (~10 lines) + `consistent'` field |
| `min_fin_truth_lemma` | EASIER than Int | bot case `Iff.rfl`; rest mechanical (`.1.2`→`.1`) |
| `minFinWorldOfPrimeTheory` | EASIER than Int | drops `consistent` field |
| `min_fmp` | EASIER than Int | backward dir drops `PropSetConsistent ∅` plumbing; forward adds 2 bot_forces args |
| `instDecidableDerivableMinPropAxiom'` | TRIVIAL (=Int) | mechanical |

**No declaration is materially harder for Min than Int.** Lowest-risk port possible.

### Note for task 422 (DO NOT implement here)
The two FMP files differ along exactly the same `Cons` axis that `GenericLindenbaum` /
`Metalogic.prime_exclusion` already parametrize over (`Cons := fun _ => True` for Min,
consistency for Int — see `MinLindenbaum.lean:144,176`). A shared
`FinWorld`/`fmp`/`Decidable` abstraction parametrized over a consistency predicate `Cons`
(plus a `bot_forces` convention) is plausible and would absorb both files. The differences
that a parametric version must reconcile: (a) optional `consistent` field, (b) `bot_forces`
= `fun _ => False` vs `⊥ ∈ carrier`, (c) the `propConsistent` helper (present only for Int).
Flagging only; reconciliation is task 422's scope.

---

## 7. Recommended Phase Breakdown (with CI at each boundary)

CI per boundary: `lake build Cslib.Logics.Propositional.Metalogic.MinDecidability` (scoped,
fast). Full pipeline + `#print axioms` only at the final phase.

- **Phase 1 — Scaffold + world type + Fintype + valuation/bot_forces layer.**
  File header/imports/preamble; `MinFinWorld`, `MinFinWorld.ext`, `instPreorderMinFinWorld`,
  `minFinWorld_carrier_injective`, `instFintypeMinFinWorld`, `minFinVal`,
  `minFinVal_upward_closed`, `minFinBotForces`, `minFinBotForces_upward_closed`.
  Boundary: scoped `lake build`.

- **Phase 2 — `min_fin_imp_witness`.**
  Port Int lines 187-248 dropping steps 2-3 (consistency) and the `consistent'` field; use
  `minDeductiveClosure_is_theory`, `min_imp_witness`, `min_prime_exclusion`, `MinTheory.1`.
  Boundary: scoped `lake build`.

- **Phase 3 — `min_fin_truth_lemma`.**
  Port Int lines 275-356; bot case `Iff.rfl`; pass `minFinBotForces` as the `bot_forces` arg;
  `IntPropAxiom.*` → `MinPropAxiom.*`; `w.closed`/`v.closed` MP-closure cases unchanged.
  Boundary: scoped `lake build`.

- **Phase 4 — FMP + Decidable instance + barrel + full CI.**
  `minFinWorldOfPrimeTheory` (private), `min_fmp` (forward via `min_soundness_derivable …
  minFinVal minFinBotForces minFinVal_upward_closed minFinBotForces_upward_closed w`;
  backward via `min_prime_exclusion (minDeductiveClosure_is_theory ∅) …`),
  `instDecidableDerivableMinPropAxiom'`. Wire `Cslib.lean` (`mk_all --module`).
  Boundary: full `lake build`; `lake exe checkInitImports`; `lake exe lint-style`;
  `lake shake --add-public --keep-implied --keep-prefix`; `lake test`.

- **Final gate — axiom audit.** Add a `#print axioms instDecidableDerivableMinPropAxiom'`
  (or `lean_verify Cslib.Logic.PL.instDecidableDerivableMinPropAxiom'`) and confirm the
  closure is exactly `{propext, Classical.choice, Quot.sound}` with **no `sorryAx`**.
  (`Classical.propDecidable` as a local instance reduces to `Classical.choice`/`propext`.)

---

## 8. Lint-Prevention Notes (CSLib standards)

- Every new declaration needs a docstring (docBlame) — copy/adapt Int's docstrings.
- Prop-valued results are `theorem`/`lemma`; `def`s only for `MinFinWorld`, `minFinVal`,
  `minFinBotForces`, `minFinWorldOfPrimeTheory`.
- lowerCamelCase, no underscores in *def* names (defsWithUnderscore applies to defs; the
  existing codebase uses snake_case `theorem` names like `min_fin_imp_witness` — match the
  sibling Int file's established convention, which passes CI).
- `instFintypeMinFinWorld` and `instDecidableDerivableMinPropAxiom'` are `noncomputable
  instance` (mirror Int).
- No new `@[simp]` lemmas are introduced, so simpNF is not a concern.

---

## 9. Zero-Debt Confirmation

This is a sorry-free target by construction: every step maps to an existing, sorry-free Min
lemma. No new axioms, no `sorry`, no vacuous definitions. If any single step resists porting,
the escalation path is to inspect the corresponding Int proof line and the exact Min lemma
signature (all catalogued in §4) — not to defer with `sorry`.
