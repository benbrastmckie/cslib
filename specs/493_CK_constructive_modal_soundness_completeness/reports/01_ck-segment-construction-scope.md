# Research Report 01: Correct Canonical Construction for Bare CK (Scoping Pass)

- **Task**: 493 — CK (constructive/bare modal K) soundness + completeness over birelational semantics
- **Mode**: `--hard --lit` (H2 anti-analysis, H3 BibKey grounding Tier 1, H4 adversarial verification)
- **Reference grounding tier**: Tier 1 (literature-backed; ground truth = ianshil/CK Coq mechanization + `Wijesekera1990`)
- **Verdict**: The task description's premise "instantiating the intuitionistic modal framework (task 480)" is **WRONG for bare CK** and must be corrected. Bare CK cannot reuse 480's prime-pair/consistent-prime-theory canonical model. CK requires a **separate segment / fallible-world construction** with a distinguished exploding world, stated against **`MValid`** (not `IValid`). This is forced, not a preference: 480's `IValid` semantics *validates* `◇⊥→⊥` (Nd), which is **not** a CK theorem, so CK is provably incomplete for any consistent-prime-theory model. What IS reusable is substantial: the entire `Birelational.lean` semantic layer, the Foundations-level `prime_set_exclusion` (its consistency predicate is a free parameter), and the non-modal proof patterns. Feasibility: **tractable, zero-debt, ~4 new files / 8-11 phases**, comparable to 480's modal portion but WITHOUT its single hardest lemma (`box_witness_pair_underivable`). Highest risk: the segment saturation/realization lemma.

---

## 1. Source-to-Implementation Mapping (H3, Tier 1)

| Source claim | BibKey / artifact | Lean target (this task) | Translation notes |
|--------------|-------------------|--------------------------|-------------------|
| Bare CK = int. prop. + Kb + Kd + necessitation only (no Cd, Idb, Nd) | ianshil/CK `theories/GHC/CKH.v` `NoAdAx := fun _ => False`; `Wijesekera1990` §2 | `CKModalAxiom` inductive | = `IKModalAxiom` **minus** `cd`, `idb`, `dbot` |
| Fallible/exploding worlds; `◇⊥` satisfiable | `Wijesekera1990` (`references.bib:885`) — fallible-world Kripke models | `MValid` (already exists, `Birelational.lean`) | `botForces` is a free parameter; exploding world forces `⊥` |
| Segment worlds `⟨head, tail⟩` + 4 constraints; exploding `cexpl` | ianshil/CK `Completeness_seg/general_seg_completeness.v` (`segment`, `cexpl`, `cmreach`, `cval`, `cireach`) | new `CKSegment` structure, `cexpl`, `cmreach`, `cval`, `cireach` | diamonds witnessed **by construction** via `tail` |
| Bare-CK completeness routed through segments, NOT prime pairs | ianshil/CK `Completeness_seg/CK_seg_completeness.v` (`ClassF := fun _ => True`, `NoAdAx`) | `ck_completeness : MValid φ → Derivable CKModalAxiom φ` | no `CK_th_completeness.v` exists — deliberate |
| Generic Lindenbaum / prime-set exclusion (consistency predicate parametric) | `ChagrovZakharyaschev1997` (`references.bib:75`) Lemma 5.5; `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean:558` | reused for segment saturation with a **quasi-consistency** predicate | `Cons : Set F → Prop` is a free parameter → admits the exploding theory |
| Birelational semantics, F1/F2, `MValid`/`IValid` | `Simpson1994` (`references.bib:86`) Ch. 3; `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) | reused wholesale | CK uses the same `BFrame`/`BModel`/`BForces`, differs only in world data |

**BibKey verification** (against `/home/benjamin/Projects/cslib/references.bib`): `Wijesekera1990` ✅ (line 885, `@article`, "Constructive Modal Logics I"), `Simpson1994` ✅ (line 86), `ChagrovZakharyaschev1997` ✅ (line 75). `Wijesekera1990` is also present in `specs/literature-index.json` (`doc_id: wijesekera_1990_constructivemodallogicsi`) as the canonical source for independent, non-interdefinable box/diamond and fallible-world semantics. No new BibKey required. (Bierman & de Paiva 2000, also in the lit index, is CK with both modalities primitive — an optional supporting cite, not required.)

---

## 2. The Correct CK Canonical Construction (Deliverable 1)

### 2.1 What a CK canonical world is: a *segment* (fallible-capable)

From ianshil/CK `general_seg_completeness.v` (fetched verbatim): a world is a record
`segment` with `head : Ensemble form` and `tail : Ensemble (Ensemble form)`, subject to four
constraints — (1) **closure**: head and tail deductively closed (w.r.t. `AllForm`); (2)
**quasi-primality**: head and tail are *quasi-prime* (prime **or** the whole set — the exploding
case is the degenerate quasi-prime theory); (3) **box reflection**: `□A ∈ head → ∀ th ∈ tail, A ∈ th`;
(4) **diamond witness**: `◇A ∈ head → ∃ th ∈ tail, A ∈ th`.

The distinguished **exploding world** `cexpl` has `head := AllForm`, `tail := {AllForm}`. Because
`AllForm` contains `⊥` and every formula, `cexpl` forces `⊥` (it is *fallible*) and forces
everything. Quasi-primality (not primality) is exactly what lets `cexpl` be a legal world — a
`ModalPrimeTheory` (480) would *forbid* it, being consistency-bearing.

Lean-shaped sketch (over `Modal.Proposition Atom`, targeting `BFrame`/`BModel`/`BForces` from
`Birelational.lean`):

```lean
/-- A CK canonical world: a segment. `head` is a set of formulas; `tail` is a set of
"successor heads". Fallible worlds (where ⊥ ∈ head) are permitted (quasi-prime, not prime). -/
structure CKSegment (Axioms : Proposition Atom → Prop) where
  head : Set (Proposition Atom)
  tail : Set (Set (Proposition Atom))
  head_closed  : Metalogic.DeductivelyClosed (modalDerivationSystem Axioms) head
  head_qprime  : QuasiPrime Axioms head                 -- prime ∨ head = univ
  tail_realizable : ∀ t ∈ tail, QuasiPrime Axioms t ∧ DeductivelyClosed … t
  box_reflect  : ∀ A, (□A) ∈ head → ∀ t ∈ tail, A ∈ t
  diam_witness : ∀ A, (◇A) ∈ head → ∃ t ∈ tail, A ∈ t

/-- Exploding world: everything holds, including ⊥. -/
def cexpl (Axioms) : CKSegment Axioms :=
  { head := Set.univ, tail := {Set.univ}, … }
```

### 2.2 Accessibility, preorder, valuation (structurally different from 480)

Verbatim from ianshil: `cmreach P0 P1 := (tail P0) (head P1)`, `cireach P0 P1 := head P0 ⊆ head P1`,
`cval s p := (head s) (# p)`. Sketch:

```lean
/-- CK preorder: head inclusion. Reflexive+transitive ⇒ `Preorder (CKSegment Axioms)`. -/
instance : Preorder (CKSegment Axioms) where le P Q := P.head ⊆ Q.head; …

/-- CK accessibility: P can reach any segment whose head is a member of P's tail. -/
def cmreach (P Q : CKSegment Axioms) : Prop := Q.head ∈ P.tail

/-- CK valuation: atom membership in the head. -/
def cval (s : CKSegment Axioms) (p : Atom) : Prop := (Proposition.atom p) ∈ s.head
```

Contrast with 480's `canonicalR w v := (∀φ, □φ∈w → φ∈v) ∧ (∀φ, φ∈v → ◇φ∈w)` over
`CanonicalPrimeWorld` (consistent prime theories). In 480 the diamond half of `canonicalR` is a
*proof obligation* discharged via Cd/Idb (`canonical_diamond_witness` needs `h_Cd`,
`canonical_box_witness` needs `h_Idb`). In CK the diamond half is *structural*: `diam_witness`
is a field of the world, and `cmreach` simply reads the `tail`. **This is why CK needs neither
Cd nor Idb** — the witnesses are built into the world, not derived from Fischer-Servi axioms.

### 2.3 Role of the exploding world

`cexpl` is the semantic home for `◇⊥`. In CK, `◇⊥` is consistent (CK does not prove `◇⊥→⊥`). A
segment `s` with `◇⊥ ∈ head` must, by `diam_witness`, have some `t ∈ tail` with `⊥ ∈ t`; the only
quasi-prime theory containing `⊥` is `univ`, i.e. `cexpl`'s head. So `cmreach s cexpl` holds and
`s` forces `◇⊥`. Without a fallible world in the model, `◇⊥` could never be forced and the truth
lemma would break at the diamond case. `cexpl` is precisely the device that makes the CK truth
lemma hold for `◇⊥` — and, dually, that *refutes* Nd, giving CK (not IK).

### 2.4 Truth lemma and completeness statement (targeting `MValid`)

```lean
/-- CK truth lemma: forcing coincides with head-membership. `botForces := (⊥ ∈ ·.head)`. -/
theorem ck_truth_lemma (s : CKSegment Axioms) (φ) :
    BForces cmreach cval (fun s => Proposition.bot ∈ s.head) s φ ↔ φ ∈ s.head

/-- CK completeness: MValid ⇒ derivable. NOTE: MValid, not IValid. -/
theorem ck_completeness {φ} (h : MValid.{u,u} φ) : Derivable CKModalAxiom φ
```

The diamond and box cases of `ck_truth_lemma` fall out of `diam_witness` / `box_reflect`
(IH + the structural fields), needing **no** modal axiom beyond Kb/Kd (which enter only through
the saturation lemma that *builds* segments with these fields). The five non-modal cases mirror
`truth_atom/bot/and/or/imp_case` exactly (see §3).

---

## 3. Reuse Analysis (Deliverable 2): the precise boundary

### 3.1 Axiom-agnostic — REUSABLE for CK

| Asset | File | Reuse form |
|-------|------|------------|
| `BFrame`, `BModel`, `BForces`, all `BForces_*` simp lemmas, `bforces_persistence`, `IValid`, `MValid`, `mvalid_implies_ivalid` | `Cslib/Logics/Modal/Semantics/Birelational.lean` (task 490) | **Verbatim, no change.** CK targets `MValid` directly; `botForces` is already a free, upward-closed parameter — this is exactly the fallible-world hook CK needs. |
| `prime_set_exclusion` | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean:558` | **Reused with a weaker `Cons`.** Signature is generic over `(D : DerivationSystem F) (Cons : Set F → Prop)` and a closure operator `cl`. Instantiating `Cons` with a *quasi-consistency* predicate (trivially-true, or "prime-or-univ") lets the same Lindenbaum machinery build segment heads/tails that *admit* the exploding theory. Confirmed by reading the signature (lines 558-579). |
| `DerivationTree`, `Derivable`, `deductionTheorem`, `DerivExcludes`, `modalDeductiveClosure`, `modalDerivationSystem`, `DeductivelyClosed` | `Metalogic/DeductionTheorem.lean`, `MCS.lean`, `PrimeTheory.lean` (generic parts) | **Verbatim.** All parametric over `Axioms`; CK supplies `CKModalAxiom`. |
| Non-modal truth-lemma cases `truth_atom_case`, `truth_bot_case`, `truth_and_case`, `truth_or_case`, `truth_imp_case` | `Metalogic/Intuitionistic/TruthLemma.lean` | **Reusable as proof patterns, not verbatim.** They are pinned to `canonicalR`/`canonicalVal`; CK re-states them over `cmreach`/`cval`. The *proofs* (using only closure, primality, `≤`-inclusion, and the `botForces` bridge) transliterate with near-zero change — `truth_bot_case` already takes an explicit `botForces w ↔ ⊥ ∈ w.val` bridge, which CK discharges by `Iff.rfl` since `botForces := (⊥ ∈ ·.head)`. |
| `Preorder`-by-inclusion instance pattern | `CanonicalModel.lean:85` | Pattern reused for `cireach`. |

### 3.2 Genuinely NEW for CK

| New asset | Why 480 has no analogue | Difficulty |
|-----------|--------------------------|------------|
| `CKModalAxiom` (9 int-prop + `k` + `kdia`) | 480's `IKModalAxiom` has the extra `cd`/`idb`/`dbot`; CK is the strict sub-system | Trivial (delete 3 constructors) |
| `CKSegment` structure + `cexpl` | 480 worlds are consistent prime theories; segments are `⟨head, tail⟩` with quasi-primality (fallible-admitting) + box-reflect + diam-witness fields | **Core novelty** |
| `cmreach` / `cireach` / `cval` | 480's `canonicalR` is a 2-clause derivation obligation; `cmreach` is a structural `tail`-lookup | Low once the structure exists |
| **Segment saturation / realization lemma** | 480's Lindenbaum builds a single prime theory; CK must build a segment with a `tail` whose every member is itself realizable as a segment head, plus diamond-witness saturation — a two-level simultaneous construction | **Highest risk (see §5)** |
| `ck_truth_lemma` box/diamond cases over segments | 480's box/diamond cases consume `canonical_box_witness`/`canonical_diamond_witness` (Cd/Idb-dependent); CK's consume `box_reflect`/`diam_witness` fields | Low–moderate; *simpler* than 480 |
| `canonical_f1`/`canonical_f2` for the segment model | Must reprove up/down confluence for `cireach`/`cmreach` | Moderate |
| `ck_axiom_sound`/`ck_soundness` over `MValid` | 480's `ik_axiom_sound` is over `IValid` (fixed `botForces`); CK needs arbitrary `botForces` | Low — see §4 |

### 3.3 NOT reusable (480 pieces CK must skip)

`box_witness_pair_underivable` + its entire `bigAnd`/`boxOr_of_boxDisj`/`unpack_conj_partial`/
`dia_bigAnd_to_bigAnd_dia` support cast (the single largest lemma in 480,
`CanonicalModel.lean:415-519`), `canonical_box_witness`, `canonical_diamond_witness`,
`canonical_f1`/`canonical_f2` (prime-pair versions), and the `.box`/`.diamond` truth-lemma cases
that consume them. All are Cd+Idb-specific. **CK never imports them** — a net *reduction* in the
hardest proof-theoretic burden.

---

## 4. Why CK uses `MValid` not `IValid` (Deliverable 3)

`Birelational.lean` already provides everything: `BModel.botForces : World → Prop` is a free
field with an upward-closure obligation `bf_upward_closed`; `MValid` universally quantifies over
*arbitrary* upward-closed `botForces`, whereas `IValid` fixes `botForces = fun _ => False`.

The decisive reason CK must use `MValid`: under `IValid`, `IK.lean`'s `dbot` case proves
`◇⊥→⊥` is valid —
```
BForces r val (fun _ => False) w' (◇⊥) = ∃ u, r w' u ∧ False = False
```
so `◇⊥→⊥` is *vacuously* `IValid` (`IK.lean:185-189`). But `◇⊥→⊥` (Nd) is **not** a CK theorem.
Hence **CK is incomplete w.r.t. `IValid`** — Nd is a valid-but-underivable formula. Completeness
forces the semantics to admit worlds where `⊥` is genuinely forced (`botForces` not identically
`False`), i.e. `MValid` with a fallible witness. The canonical `botForces` is `(⊥ ∈ ·.head)`,
which is non-trivially true exactly at `cexpl` and its head-supersets, and upward-closed for free
under `cireach` (head inclusion). The completeness statement is therefore
`ck_completeness : MValid φ → Derivable CKModalAxiom φ`, and soundness is
`ck_soundness : Derivable CKModalAxiom φ → MValid φ`.

**Soundness is easy over `MValid`.** `ik_axiom_sound`'s `k`/`kdia` cases (`IK.lean:162-170`) and
all nine non-modal cases never inspect `botForces` (the non-modal ones route through
`bforces_persistence`, which is generic over `botForces` via `bf_uc`). So `ck_axiom_sound` is
`ik_axiom_sound` restricted to `{k, kdia}` + non-modal, re-generalized to arbitrary `botForces` —
a near-mechanical adaptation. CK drops the only frame-condition-consuming case (`idb`, which used
`f2`) and the vacuous `dbot`.

---

## 5. Feasibility + Risk (Deliverable 4)

**Verdict: zero-debt Lean formalization of CK completeness is tractable.** Scale is comparable to
480's modal portion, but the risk profile is *inverted*: CK trades away 480's hardest proof
(`box_witness_pair_underivable`, ~250 lines of `bigAnd`/`bigOr` derivation gymnastics) for a new
hardest proof (segment saturation). Net difficulty roughly par with 480, plausibly a touch lower.

**Estimated shape** (~4 new files under `Cslib/Logics/Modal/Metalogic/Constructive/`,
namespace `Cslib.Logic.Modal`; mirrors the `Intuitionistic/` layout):

1. `Segment.lean` — `CKSegment`, `cexpl`, `cireach` (+`Preorder`), `cmreach`, `cval`, `QuasiPrime`. (~150-250 lines)
2. `SegmentLindenbaum.lean` — the saturation/realization lemma via `prime_set_exclusion` with a quasi-consistency `Cons`. **Hardest phase.** (~300-500 lines)
3. `CKTruthLemma.lean` — 5 non-modal cases (transliterate from `TruthLemma.lean`) + box/diamond via `box_reflect`/`diam_witness` + `f1`/`f2` for the segment model. (~250-400 lines)
4. `CK.lean` — `CKModalAxiom`, `ck_axiom_sound`/`ck_soundness`/`ck_soundness_derivable` (MValid), `ck_completeness`, `ck_consistent`, `ck_soundness_completeness`. (~200-300 lines)

Rough total ~900-1450 lines; **8-11 phases** (480 was 12). Zero `sorry`/`axiom`: all modal
assumptions enter as `CKModalAxiom` constructors, exactly as 480 threads its `h_*` hypotheses.

**Highest-risk proof: the segment saturation/realization lemma** (`SegmentLindenbaum.lean`).
Building a segment requires simultaneously saturating the `head` (quasi-prime, deductively closed)
**and** populating the `tail` so that (a) every `◇A ∈ head` has a witness `t ∈ tail` with `A ∈ t`,
(b) every `t ∈ tail` is itself a realizable (quasi-prime, closed) head, and (c) `□`-reflection
holds. This is a two-level construction (a theory of theories) with no direct 480 analogue —
480's `modal_prime_exclusion` is single-level. **This is the CK counterpart of the moment 480
discovered it needed the new `prime_set_exclusion` Foundations infra.** Mitigation: `prime_set_exclusion`
is generic enough (free `Cons`) to build each *individual* segment head/tail-member; the genuinely
new work is the *outer* fixpoint assembling `tail` and threading the box/diamond constraints.
Recommend the plan carve this into its own phase with an explicit sub-lemma budget, and flag it as
the candidate for possible additional Foundations infrastructure (a generic "saturated
witness-family" lemma) if the inline construction proves unwieldy.

**Second risk:** `cmreach`/`cireach` up/down-confluence (`f1`/`f2`) for the segment model — the
interaction between head-inclusion and tail-membership must be checked, including at `cexpl`.
Moderate, not blocking.

---

## 6. Implications for Task 501 (CK extensions CT/CS4/CS5) — high-level (Deliverable 5)

The segment/fallible-world model **extends cleanly**, exactly mirroring how 480's `IValid`
framework extended to IT/IS4/IS5. In ianshil this is the `ClassF` + `AdAx` parametrization of
`general_seg_completeness.v`: bare CK is `ClassF := fun _ => True`, `NoAdAx`; CT/CS4/CS5 set
`ClassF` to the reflexive / reflexive-transitive / equivalence frame class and add the matching
axioms (T: `□A→A`; 4: `□A→□□A`; 5: `◇A→□◇A`) to `AdAx`. **Recommendation for 493:** define
`CKSegment` and the truth/completeness machinery parametric over `Axioms` (as 480 already is),
so 501 instantiates by adding constructors + a frame-class hypothesis on `cmreach`, with no
re-derivation of the segment core.

- **Reflexivity/transitivity extend smoothly.** `cexpl` satisfies them (`cmreach cexpl cexpl`
  holds: `cexpl.head = univ ∈ {univ} = cexpl.tail`), so fallibility does not obstruct the frame
  conditions.
- **Euclidean-vs-symmetry concern (as in task 494) propagates and is the primary 501 risk.**
  CS5 needs an equivalence (or euclidean) frame condition on `cmreach` over segments. As 494
  found for the classical/intuitionistic S5 line, the *canonical* relation tends to yield
  euclideaness directly, and matching that to a symmetric/equivalence frame class (and validating
  axiom 5 against it) required care. The same wrinkle recurs for CS5: proving `cmreach` euclidean
  from axiom 5, over segments-with-`cexpl`, is where 501's difficulty will concentrate. Flag now;
  resolve in 501.

---

## Adversarial Self-Verification (H4)

**Challenge: Can bare CK reuse the 480 prime-pair framework after all, via a clever `botForces`
choice — avoiding the separate segment construction?**

Checked honestly, three ways; the answer is a firm **No**:

1. **`botForces` is orthogonal to the obstruction.** 480's `mvalid_completeness`
   (`Completeness.lean:263`) already exposes an *arbitrary* `botForces`, yet it *requires*
   `h_Idb`, `h_Cd`, `h_dbot` as arguments (threaded into `canonical_f1`, `canonical_f2`,
   `canonical_truth_lemma`, and the box/diamond witnesses). Bare CK does not prove Cd, Idb, or Nd,
   so **the dischargers simply do not exist** — you cannot even *call* `mvalid_completeness` at
   `CKModalAxiom`. `botForces` affects only the `⊥` truth-case, never the modal witnesses.
   **Confirmed by reading the exact hypothesis lists** (`Completeness.lean:263-283`).

2. **The consistent-prime-theory world type structurally cannot witness `◇⊥`.** Even discarding
   `canonicalR` and inventing a new relation over `CanonicalPrimeWorld` (= *consistent* prime
   theories, `CanonicalModel.lean:79`), no world contains `⊥` (`canonical_bot_not_mem`,
   `TruthLemma.lean:85`). So any `botForces := (⊥ ∈ ·.val)` collapses to `fun _ => False`, i.e.
   back to `IValid`. The diamond truth-case for `◇⊥ ∈ w` then has no witness world → truth lemma
   fails. Fallible worlds are unavoidable, and `ModalPrimeTheory` forbids them (it bakes in
   consistency). **Confirmed.**

3. **The completeness *target* itself rules it out.** Under `IValid`, `◇⊥→⊥` (Nd) is vacuously
   valid (`IK.lean:185-189`, read verbatim) but is **not** a CK theorem. Any completeness route
   whose semantics coincides with `IValid` (which every consistent-prime-theory model does, per
   #2) would therefore prove `Derivable CKModalAxiom (◇⊥→⊥)` — false. So the reuse is not merely
   inconvenient, it is **logically impossible**: it would prove a non-theorem. **Decisive.**

This triangulates with the ground-truth architecture (report 03 §1): ianshil ships
`Completeness_seg/CK_seg_completeness.v` and deliberately **no** `Completeness_th/CK_th_completeness.v`.

**Other challenged claims:**
- *"`prime_set_exclusion` is reusable for fallible worlds."* Verified against the signature
  (`PrimeExclusion.lean:558-579`): `Cons : Set F → Prop` and the closure operator are free
  parameters, so instantiating `Cons` with a quasi-consistency predicate admits the exploding
  theory. HIGH confidence. Residual: the *outer* two-level tail-assembly is genuinely new (flagged
  §5), so "reusable" means "reusable for each individual head/tail-member," not for the whole
  segment in one shot. Stated precisely in §3.1/§5.
- *"Soundness is easy over `MValid`."* Verified `ik_axiom_sound`'s `k`/`kdia`/non-modal cases do
  not touch `botForces` (`IK.lean:137-170`). HIGH confidence.
- *"CK = IK minus cd/idb/dbot."* Grounded on ianshil `CKH.v` `NoAdAx` + `IK.lean`'s own
  documentation that its 5 modal constructors are `{K, Kdia, Cd, Idb, Nd}`. HIGH confidence.
  (One caveat worth a plan-time check: some authors call *Wijesekera's* logic — CK **+** Nd — "CK";
  this task's scope, per the delegation and ianshil `NoAdAx`, is the **bare** system without Nd or
  Cd. The plan should pin the exact axiom list against `Wijesekera1990`/ianshil before coding
  `CKModalAxiom`.)

**No forbidden outputs:** report ends in concrete Lean sketches, a file/phase plan, a precise
reuse table, and an actionable direction (correct the task premise; build the segment
construction). **Zero-debt:** every modal assumption is a `CKModalAxiom` constructor; no
`sorry`/`axiom`/vacuous-def recommended. **Reuse check exhausted:** Foundations (`prime_set_exclusion`),
existing typeclasses (`BFrame`/`BModel`, `HasBox`/`HasDia`), notation, Mathlib
(`Preorder`), and the Logics namespace (480 framework) were all checked before recommending any
new definition.

**Confidence summary:** CK-cannot-reuse-480 HIGH (three independent arguments + ground truth);
segment construction shape HIGH (verbatim ianshil fetch); MValid requirement HIGH; reuse boundary
HIGH; feasibility/scale MEDIUM-HIGH (segment saturation is the estimate's main uncertainty);
501 euclidean concern MEDIUM (flagged for downstream).
