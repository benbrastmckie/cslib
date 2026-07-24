# Research Report: CS5 Completeness via a Native Hilbert Canonical Model over Fallible `CKValid` (Route B)

- **Task**: 539 — cs5_native_hilbert_pair_lindenbaum_completeness (owns the native Hilbert
  canonical-model completeness for constructive CS5, over the fallible-world `CKValid` semantics)
- **Date**: 2026-07-24
- **Session**: session_013h2qsatYrD4BG7EE4C8niu
- **Status**: Researched — a single, precisely-located open lemma (a constructively-sound
  two-sided / pair Lindenbaum construction) blocks an otherwise-complete native Hilbert proof.
  Nothing is proven impossible; every naive shortcut is mechanically ruled out; a sound repair is
  sketched (not built).
- **Approach constraint**: This task deliberately pursues the **native** route — the completeness
  theorem must be produced by CS5's *own* fallible-world segment canonical model over
  `CKValid`/`CKValidFC`, uniform with the CK/CT/CS4 column — **not** by transporting IS5's
  birelational result (that alternative is Route A, recorded in §10 as an explicit non-goal here).

## Executive Summary

Constructive CS5 (`CS5 = CK + T + 4 + B`, with `B` axiomatised by symmetry `bBox : A → □◇A`,
`bDia : ◇□A → A`, **not** the classical euclidean `5`) is the only member of the constructive
column (`CK`, `CT`, `CS4`, `CS5`) whose completeness is not yet delivered by the shared
fallible-world segment canonical model. The library currently proves CS5 completeness only via a
labelled natural-deduction system (`cs5_completeness : CKValidFC cs5FCIncest φ → NIKTheorem TS5 φ`,
`Constructive/Labelled/Completeness.lean:132`), whose conclusion is the labelled `NIK` theoremhood,
not Hilbert `Derivable CS5ModalAxiom`.

**The native Hilbert route is open at exactly one step: the box-backward case of the truth lemma.**
`B`'s symmetry forces a two-sided canonical relation, which moves the hard truth-lemma case from
the *diamond*-backward direction (where CS4's hereditary `excl`-tail solves it) to the
*box*-backward direction. Refuting an unwarranted `□A` at a canonical world requires producing a
*symmetric predecessor* omitting `A`, and that needs a **simultaneous, two-sided maximal theory
pair** `⟨H', T⟩` — which the library's single-set Lindenbaum / single-formula primeness engine
cannot supply as stated.

Everything else is in place:

- **Soundness** is fully landed: `cs5_axiom_sound` over `cs5FC` (`CS5.lean:248`) and, crucially,
  the axiom-free `cs5_axiom_sound''` over the genuinely-weaker `cs5FC''` (`CS5.lean:366`), the
  frame condition the canonical model must satisfy.
- The **symmetric-tail canonical model** is designed and its frame clauses are discharged, with
  canonical symmetry obtained *by construction* (`cs5Tail_symm`), never derived from maximality —
  so the negation-completeness objection does **not** arise for the frame condition.
- The **pair poset** for the box-backward step is defined and three of its four Lindenbaum
  ingredients are already sorry-free (seed membership, chain upper bound, component maximality;
  `probes/cs5-pair-primeness.lean`).
- The two axioms `CK` drops but `CS5` needs — `k3`/`cd` (`cs5_dia_or`, `CS5.lean:555`) and
  `k5`/`dbot` (`cs5_dia_bot_imp_bot`, `CS5.lean:740`) — are proven, which is *why* the fallible
  apparatus is inert at CS5 and the tail is `Set.univ`-free automatically.

The single missing piece — component **primeness** of the pair under the cross-conditions — has a
documented sound repair: **encode the pair as one quasi-prime theory over the doubled atom space
`Atom ⊕ Atom`** under a combined axiom system carrying the two cross-condition implications, so the
existing single-formula primeness engine (`prime_maximal_is_prime`) applies to the single combined
theory. This report specifies that construction and orders the remaining work.

---

## 1. Goal and Target Theorem

Deliver, sorry-free and Hilbert-native:

```lean
theorem cs5_completeness'' {Atom : Type u} {φ : Proposition Atom} :
    CKValidFC.{u, u} cs5FC'' φ → Derivable (@CS5ModalAxiom Atom) φ
```

via the fallible-world **segment canonical model** of `CKExtension.lean` (the same scaffold that
yields `ck_completeness`, `ct_completeness`, `cs4_completeness`), instantiated at CS5 with the
symmetric tail of task 509. The frame-condition target is `cs5FC''` (`CKExtension.lean:184`), which
weakens `cs5FC` to *plain* symmetry + *plain* transitivity + the re-basing/`FCsym_box` clauses and
is the strongest condition the canonical model can actually satisfy (`cs5FC_implies_cs5FC''`,
`CKExtension.lean`; `cs5_axiom_sound''` establishes the matching soundness).

Optionally also deliver the `cs5FCIncest` variant used by the labelled route, but `cs5FC''` is the
primary target because its soundness is already axiom-free.

**Uniformity thesis (the point of Route B).** With this theorem, all four constructive systems
`CK/CT/CS4/CS5` are complete by the *same* fallible-world canonical-model method over `CKValid`,
with no labelled detour and no cross-column transport — one truth lemma, one segment model, four
logics.

## 2. Current CS5 Status — what is landed vs open

**Landed, sorry-free / axiom-clean:**

| Asset | Location | Role |
|---|---|---|
| `cs5_axiom_sound` (over `cs5FC`) | `CS5.lean:248` | soundness, strong FC |
| `cs5_axiom_sound''` (over `cs5FC''`, axiom-free) | `CS5.lean:366` | soundness, the FC the model satisfies |
| `cs5_dia_or` (`k3`: `◇(A∨B)→◇A∨◇B`) | `CS5.lean:555` | collapse witness; voids fallible defects |
| `cs5_dia_bot_imp_bot` (`k5`: `◇⊥→⊥`) | `CS5.lean:740` | `Set.univ`-freeness of tails |
| `cs5TwoSidedR_iff_cs5Tail` | `CS5Canonical.lean:511` | two-sided ◇ clause ≡ box clause over CS5 theories |
| `cs5_boxInv_subset_iff` (`boxInv T ⊆ H ↔ T ⊆ diaInv H`) | `CS5.lean` | tail clause bridge |
| symmetric-tail construction + `cs5Tail_symm` | `CS5Canonical.lean` | canonical symmetry **by construction** |
| pair poset seed / chain-union / component-maximality | `probes/cs5-pair-primeness.lean` | 3 of 4 Lindenbaum ingredients |
| `prime_set_exclusion` box-exclusion pattern | `Foundations/.../PrimeExclusion.lean` | discharges the box-exclusion side conditions |

**Open:** the box-backward truth-lemma case, reducible (per §6) to **component primeness of the
pair poset under the cross-conditions**.

## 3. The Precise Obstruction — the box-backward truth-lemma case

In the segment canonical model, the truth lemma is proved by induction on `φ`. The hard direction
of the `□`-case is *backward*: to show `□A ∉ head(w) → w ⊮ □A`, one must exhibit a canonical
successor `u` with `w r u` and `A ∉ head(u)` (so that `A` is refuted at an accessible world).

Under `B` the canonical relation `r` is **symmetric**, so this successor is simultaneously a
*predecessor*, and its own box-content must be compatible with `w`. Concretely the witness is not a
single Lindenbaum extension but a **pair** `⟨H', T⟩` (a head/tail pair) satisfying, simultaneously:

- designated-formula exclusions: `□A ∉ H'` and `A ∉ T`;
- the two **cross-conditions** enforcing symmetric accessibility: `boxInv H' ⊆ T` and
  `boxInv T ⊆ H'` (equivalently, via `cs5_boxInv_subset_iff`, the diamond-tail forms);
- deductive closure + primeness of each component.

A single-set Lindenbaum extension cannot produce two mutually-constrained maximal sets at once:
extending `H'` changes `boxInv H'`, which changes the constraint on `T`, and vice versa. This
mutual dependency is the entire difficulty.

## 4. Why the naive canonical relations fail — the mechanized negatives

The library already rules out, by mechanized counterexample, every attempt to avoid the pair
construction by cleverly choosing a *one-set* canonical relation:

1. **Box-based one-sided relation collapses to plain symmetry, then fails at Ω.**
   `r w u := boxInv(head w) ⊆ head u`. Because `boxInv` is monotone, an incestuality witness
   `u' ≥ u` can never help, so the ≤-mediated condition degenerates to plain symmetry
   (`cs5Incest_forces_symm`, `CS5Canonical.lean:643`); plain symmetry then fails at the exploding
   world `Ω` (`head = Set.univ`), reachable from all worlds but reaching back to none.
   Mechanized: `cs5Incest_cs5CanonMreach_false` (`CS5Canonical.lean:465`).

2. **The `Ω`-excluding (`excl`-style) world type also fails.**
   `cs5Incest_cs5PrimeMreach_false` (`CS5Canonical.lean:688`) — even restricting to hereditary,
   non-exploding worlds does not rescue the one-set relation.

3. **The two-sided Simpson diamond relation is not an escape.**
   Over quasi-prime CS5 theories the diamond clause `Δ ⊆ diaInv Γ` is *literally equivalent* to
   the box clause `boxInv Δ ⊆ Γ` (`cs5TwoSidedR_iff_cs5Tail`, `CS5Canonical.lean:511`), so
   restoring the diamond clause reinstates exactly the same box-backward wall
   (`cs5_symmetric_tail_box_gap`, with the explicit 3-world `cs5FC''` countermodel
   `CS5BoxGapWorld`).

4. **General monotonicity collapse** (`CS5Canonical.lean:634`) generalises (1): any box-based
   relation on a monotone head order collapses the ≤-mediated clause to plain symmetry.

**Reading:** these are negatives about *specific one-set relations*, establishing that the pair
construction is *necessary*, not that completeness is impossible. The frame condition itself
(`cs5FC''`) is satisfiable by the symmetric-tail model with symmetry obtained by construction — so
the obstruction is entirely in the *truth lemma's* witness supply, not in the frame condition.

## 5. The published proof is unsound here — Pacheco Lemma 18 → 16

Pacheco (`Pacheco2024`, `CS5 ≡ IS5`, Theorem 13) supplies the pair construction as Lemma 18, whose
primeness step delegates to Lemma 16. Lemma 16's proof contains, verbatim, the negation-complete
move (probe corpus confirmation, `cs5-pair-primeness.lean`):

> *"if ϕ ∉ Θ and ψ ∉ Θ, we would have that ¬ϕ ∈ Θ and ¬ψ ∈ Θ. By MP, ¬(ϕ ∨ ψ) ∈ Θ."*

This `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` step is unsound for a **poset-maximal, quasi-prime** `Θ`: in a pair poset
carrying cross-conditions, maximality can fail via a cross-condition violation (`Θ'□ ⊄ Σ`), not via
inconsistency, so absence of `ϕ` does not license presence of `¬ϕ`. Any port of the textbook proof
must replace this step. `Pacheco2024` is therefore cited as the source of the *technique*, not as
an importable result.

## 6. What is already free, and the exact gap (from `cs5-pair-primeness.lean`)

Define the pair poset `cs5PairPoset H φX φY`: pairs `⟨X, Y⟩` with `H ⊆ X`, designated exclusions
`□A ∉ X`, `A ∉ Y`, and cross-conditions `boxInv X ⊆ Y`, `boxInv Y ⊆ X`, ordered componentwise by
`⊆`.

**Free (proved sorry-free in the probe):**

1. **Seed** — `(H, cl (boxInv H)) ∈ cs5PairPoset` whenever `□A ∉ H` (`cs5_pair_seed_mem`). Needs no
   MP-closure/◇-preprocessing: `boxInv H ⊆ H` (axiom `T`) gives `cl (boxInv H) ⊆ H`, and
   `A ∉ cl (boxInv H)` follows from `□A ∉ H` via `box_mem_of_boxed_context`. Fixes Pacheco's merely
   asserted seed (his defect (c)).
2. **Chain upper bound** — `boxInv` and designated-formula membership are *pointwise*, so they
   commute with **arbitrary** unions; no directed-union lemma needed (`cs5_pair_chain_union_mem`).
   Fixes Pacheco's absent defect (d).
3. **Component maximality** — a `Maximal` pair `⟨X,Y⟩` yields `X` maximal in the slice
   `{X' | ⟨X',Y⟩ ∈ poset}` (`cs5_pair_maximal_component_left`), pure order theory
   (`Maximal.le_of_ge`).

**The gap (the whole task):** converting slice-maximality into component **primeness** via the
library engine `prime_maximal_is_prime` (`PrimeExclusion.lean:428`) requires the slice to be a
`PrimeExcludingSupersets D Cons S φX` for a `Cons` predicate that is **closure-stable**
(`cl_admissible_of_cons : Cons Z → Cons (cl Z)`, used internally when the engine closes
`insert ψ X` and must stay in the poset). The natural candidate `Cons_Y Z := boxInv Z ⊆ Y`
(cross-condition, `Y` fixed) is **not** closure-stable: `cl (insert ψ Z)` can derive a *new* `□B`
(e.g. from `ψ` and `ψ → □B` both admitted) whose witness `B` was never required to be in `Y`. In
general `boxInv (cl Z) ⊆ Y` does **not** follow from `boxInv Z ⊆ Y`.

Contrast Phase 6/7's box-exclusion *set* `E := {□B | B ∉ H}`, which is stated and discharged
entirely in terms of `H` and needs no `cl`-stability of a side predicate — that is why the
one-sided box exclusion works and the two-sided cross-condition does not.

## 7. The Sketched Sound Repair — a combined theory over `Atom ⊕ Atom`

Encode the *pair* as a **single** quasi-prime theory over the doubled atom space, so the
single-formula primeness engine applies to one set rather than a mutually-constrained pair:

- **Atoms**: `Atom ⊕ Atom`. Tag `X`-component formulas via `Sum.inl`, `Y`-component via `Sum.inr`
  (lift by the obvious `Proposition (Atom ⊕ Atom)` relabelling on each side).
- **Combined axiom system** `CS5Pair`: `CS5ModalAxiom` on each tagged copy, **plus** the two
  cross-condition implications internalised as axioms, so that the deductive closure of the
  combined theory *automatically* propagates the cross-conditions rather than leaving them as an
  external, non-`cl`-stable side predicate. Concretely, axioms encoding
  `□(inl φ) ↔ (something over inr)` realising `boxInv X ⊆ Y` and `boxInv Y ⊆ X` as *derivable*
  facts of the combined system.
- **Result**: cross-conditions become part of `cl`, hence closure-stable *by construction*, and
  `prime_maximal_is_prime` applies to the single combined theory. Project back to `⟨X, Y⟩` via
  `Sum.inl`/`Sum.inr` preimages to recover the two prime components.

This is the construction the probe docstring names ("encode the pair as a single quasi-prime theory
over the doubled atom space `Atom ⊕ Atom` under a combined axiom system that adds the two
cross-condition implications"). It is **sketched, not built**. The main research risk (§9) is
whether the two cross-condition implications are simultaneously (i) sound for the intended
projection and (ii) strong enough to force the cross-conditions on the projected components without
over-constraining primeness.

## 8. Work Items, in dependency order

1. **`CS5Pair` axiom system + doubled-atom relabelling.** Define `Proposition (Atom ⊕ Atom)`
   lifts, `CS5PairAxiom`, and the projection maps. Prove the lifts are homomorphisms for
   `imp/box/dia` and that per-side `CS5PairAxiom` restricts to `CS5ModalAxiom`.
   *(new, self-contained; ~foundational)*
2. **Cross-condition internalisation.** State the two cross-condition implication axioms; prove
   soundness of the combined system for the intended pair semantics; prove `cl`-stability of the
   cross-conditions as a corollary of closure under the combined axioms.
   *(the crux; the sound replacement for Pacheco Lemma 16)*
3. **Pair primeness.** Instantiate `prime_maximal_is_prime` at the combined theory; project to
   recover `⟨H', T⟩` prime with `□A ∉ H'`, `A ∉ T`, `boxInv H' ⊆ T`, `boxInv T ⊆ H'`.
   Reuse the probe's seed / chain-union / component-maximality facts.
4. **Box-backward truth-lemma case.** Feed the pair witness into the CS5 truth lemma's `□`-backward
   case in the symmetric-tail canonical model; close it.
5. **Assemble `cs5_completeness''`.** Compose the completed truth lemma with
   `ckvalidFC_completeness` (`CKExtension.lean`) and `cs5_axiom_sound''`; state the
   soundness-completeness biconditional `cs5_soundness_completeness''`.
6. **(Optional) `cs5FCIncest` variant** for parity with the labelled route.

## 9. Risks and Reuse

**Reuse (CSLib):** `CKExtension.ckvalidFC_completeness` (canonical-model driver),
`Segment.lean`/`SegmentLindenbaum.lean` (quasi-prime theories, refuting segments),
`PrimeExclusion.prime_maximal_is_prime` + `prime_set_exclusion`, the symmetric-tail construction
and `cs5Tail_symm`, `cs5_boxInv_subset_iff`, `cs5_dia_or`, `cs5_dia_bot_imp_bot`, and the three
probe facts (`cs5_pair_seed_mem`, `cs5_pair_chain_union_mem`, `cs5_pair_maximal_component_left`).
Little-to-no Mathlib beyond `Zorn` (already used).

**Risks:**

- **R1 — the combined axioms may not be `cl`-stable-and-sound simultaneously.** This is the single
  make-or-break. If the internalised cross-conditions are too weak they fail to force the
  projection; too strong and they break per-component primeness. *Mitigation:* prototype in a
  `probes/` file first (a `cs5-pair-combined-atomsum.lean` probe), exactly as task 509 prototyped
  the pair poset, before touching library files.
- **R2 — projection faithfulness.** The `Sum.inl`/`Sum.inr` preimages must yield deductively-closed
  prime components; relabelling must not smuggle cross-tag derivations. *Mitigation:* prove a
  conservativity lemma "combined ⊢ inl φ ⟺ X-system ⊢ φ modulo cross-conditions."
- **R3 — scope creep into the truth lemma.** Item 4 assumes the rest of the CS5 truth lemma is
  otherwise complete in the symmetric-tail model; confirm no *other* case regresses once the box
  case is filled.

## 10. Explicit non-goals (recorded for scope discipline)

Two sound alternatives exist and are **out of scope** for this task, which is defined by the native
mandate:

- **Route A (collapse-then-reuse):** prove `CS5 ⊢ idb` (`k4`; `cd`/`k3` and `dbot`/`k5` already
  landed), obtain `is5Derivable ⟺ cs5Derivable`, and inherit completeness from the birelational
  `is5_completeness` (`IS5.lean:364`) via a `CKValid`/`IValid` validity-coincidence bridge. Sound
  and mostly done, but the completeness is *not* produced by CS5's own fallible canonical model —
  it re-bases the semantics onto IS5's birelational frame class. Tracked separately if desired.
- **Route C (adequacy bridge):** prove Simpson Ch. 6 `NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`
  and corollarise from the landed labelled completeness. Yields a Hilbert *statement* but retains
  the labelled system as the engine — not a uniform Hilbert *method*.

Route B is preferred **iff** the objective is method-uniformity across the constructive column and
faithfulness to the fallible-world model theory as a primitive object. If the objective is instead
minimal sound debt, Route A dominates (see the session analysis that spawned this task).

## 11. Verdict

Native Hilbert completeness for CS5 over `CKValid` is **open, not impossible, and blocked at a
single, precisely-located lemma**: constructively-sound primeness of the two-sided cross-condition
pair. Every one-set shortcut is mechanically refuted; the frame condition is satisfiable with
symmetry by construction; three of four Lindenbaum ingredients are landed; the two collapse axioms
are proven. The remaining work is the `Atom ⊕ Atom` combined-theory construction of §7, whose
make-or-break is a single soundness-and-closure-stability question (R1) best de-risked in a probe
before any library edit.

## References

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — CS5 axioms, `cs5_axiom_sound''`,
  `cs5_dia_or`, `cs5_dia_bot_imp_bot`, module docstring (box-backward gap, Pacheco cross-check).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — symmetric tail, `cs5Tail_symm`,
  the mechanized negatives (`cs5Incest_cs5CanonMreach_false`, `cs5Incest_cs5PrimeMreach_false`,
  `cs5_symmetric_tail_box_gap`, `cs5TwoSidedR_iff_cs5Tail`, general monotonicity collapse).
- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — `cs4FC'`, `cs5FC`, `cs5FC''`,
  `ckvalidFC_completeness`.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` — the diamond-backward technique that works
  (hereditary `excl` tail, `cs4_not_dia_dia`) and its docstring stating CS5 cannot reuse it.
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` — `prime_maximal_is_prime` (`:428`),
  `prime_set_exclusion`.
- `Cslib/Logics/Modal/Metalogic/Intuitionistic/IS5.lean` — `is5_completeness` (Route A target).
- `specs/archive/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean` — the
  pair poset, the three landed ingredients, the closure-stability finding, and the `Atom ⊕ Atom`
  repair sketch.
- `specs/archive/509_.../reports/01_cs5-symmetric-tail-construction.md` — the symmetric-tail
  construction and the box-backward gap analysis.
- [Pacheco 2024, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024] — source
  of the pair-construction technique (Lemma 18); its primeness step (Lemma 16) is unsound here and
  must be replaced.

## Artifacts (planned outputs of task 539)

- `specs/539_cs5_native_hilbert_pair_lindenbaum_completeness/reports/01_route-b-native-hilbert-cs5-research.md` (this report)
- `specs/539_.../probes/cs5-pair-combined-atomsum.lean` (planned — de-risk R1 before library edits)
- `specs/539_.../plans/01_route-b-native-hilbert-plan.md` (planned)
- library target: `cs5_completeness''` / `cs5_soundness_completeness''` in
  `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (or a new `CS5Completeness.lean`)
