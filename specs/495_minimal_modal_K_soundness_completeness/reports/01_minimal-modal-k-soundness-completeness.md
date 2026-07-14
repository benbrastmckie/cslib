# Research Report 01: MK (Minimal Modal Logic K) — Soundness + Completeness over the Task-480 Birelational Framework

- **Task**: 495 — MK = modal logic over the MINIMAL propositional base (no efq / explosion), instantiating the task-480 intuitionistic modal framework MINUS efq, over the task-490 birelational semantics with the minimal ⊥ treatment (⊥ an ordinary proposition), proved sound + complete via the (prime-theory) canonical model.
- **Task type**: cslib | **Session**: sess_1784044271_09e821_495 | **Date**: 2026-07-14
- **Territory** (concurrent sessions active): NEW files only, under `Cslib/Logics/Modal/Metalogic/Minimal/` (proposed). No edits to delivered IK/CK/Intuitionistic/Constructive files.

## Verdict (one line)

MK is **not** "IK completeness with the `h_efq` lambda deleted". The delivered `mvalid_completeness`/`ivalid_completeness` and the whole `Intuitionistic/CanonicalModel.lean` **consume `h_efq` essentially** in two distinct roles — (a) proving *consistency* of every constructed canonical world, and (b) the `⊥`-base cases of the box/diamond distribution lemmas (`⊥ → □⊥`, and `◇⊥ → ⊥` via `h_dbot`) — and **neither `⊥ → φ` nor `◇⊥ → ⊥` is an MK theorem**. The correct MK construction drops consistency entirely (worlds = **quasi-prime** theories, `Cons := fun _ => True`, fallible worlds admitted, `botForces := ⊥ ∈ w.val`) and **reuses the already-delivered, Axioms-parametric, efq-free `QuasiPrime` + `quasi_prime_exclusion` + `imp_refuting_theory` + `box_refuting_theory` + `dia_refuting_theory` machinery in `Constructive/Segment.lean` + `Constructive/SegmentLindenbaum.lean`**, packaged into a birelational (`MValid`, ∃-diamond, F1/F2) canonical model mirroring the propositional `MinStrongCompleteness.lean`. Soundness is a short new proof mirroring `ik_axiom_sound`'s minimal-propositional + `k/kdia/cd/idb` cases (all of which are already `botForces`-agnostic), dropping the `efq` and `dbot` cases.

---

## Source-to-Implementation Mapping (files located)

All paths absolute under `/home/benjamin/Projects/cslib/`.

| Concern | Delivered file | Reuse verdict for MK |
|---|---|---|
| Birelational semantics, `MValid` (F1/F2, arbitrary `botForces`), `BForces`, `bforces_persistence` | `Cslib/Logics/Modal/Semantics/Birelational.lean` | **REUSE as-is**. `MValid` (lines 205–216) is exactly MK's semantics. `mvalid_implies_ivalid` (218) confirms `IValid = MValid @ botForces:=False`. |
| Modal Hilbert calculus `DerivationTree Axioms` (ax/assumption/mp/**necessitation**/weakening), `Derivable`, `modalDerivationSystem` | `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` | **REUSE as-is** (axiom-parametric, no classical/efq dependency). |
| Deduction theorem (needs only implyK/implyS) | `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` | **REUSE as-is** (minimal-safe). |
| Generic prime exclusion, `Admissible`, `PrimeAdmissible`, `Cons`-parametric | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` | **REUSE as-is**. Header line 19: "use `fun _ => True` for the minimal case"; line 21: EFQ bridge "vacuous when `Cons = fun _ => True`". |
| **`QuasiPrime` = `PrimeAdmissible … (fun _ => True)`** (deductively closed + disjunction property, **no consistency**; exploding `Set.univ` admitted) | `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean:64` | **REUSE as-is** — this IS the minimal modal prime theory. `QuasiPrime.closed`/`QuasiPrime.disj`/`quasiPrime_univ` provided. |
| **`quasi_prime_exclusion`** (Lindenbaum for quasi-prime, **no efq bridge**), `imp_refuting_theory` (efq-free analogue of `modal_imp_witness`), `box_refuting_theory`, `dia_refuting_theory`, `box_mem_of_boxed_context`, `quasi_head_realization` | `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean:64,142,168,194,242` | **REUSE as-is** — all Axioms-parametric (`Cons=True`), efq-free. Header: "so task 501's CT/CS4/CS5 extensions can reuse it" → MK reuses too. |
| IK axiom datatype + soundness (`k/kdia/cd/idb` cases `botForces`-agnostic) | `Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean:75,131` | **STRUCTURAL TEMPLATE** — copy minus `efq`,`dbot` constructors & cases. |
| Parametric completeness (`ivalid_completeness`/`mvalid_completeness`) — **efq-bearing** | `Cslib/Logics/Modal/Metalogic/Intuitionistic/Completeness.lean:187,263` | **NOT reusable for MK** (see Crux §2). Structural reference only. |
| Truth-lemma cases — `truth_bot_case` already `botForces`-parametric | `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean:141` | `truth_atom/bot/and/or` cases **structurally reusable** over quasi-prime worlds; `imp/box/diamond` need quasi-prime witnesses. |
| Propositional minimal completeness (the EXACT template) — `MinTheory`, `min_imp_witness`, `min_prime_exclusion` (`Cons=True`, no efq), `MinCanonicalWorld`, `minBotForces := ⊥∈w.val`, `min_truth_lemma`, `min_completeness`, `min_soundness_completeness` | `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean`, `MinStrongCompleteness.lean` | **STRUCTURAL TEMPLATE** — MK is the modal lift of exactly this development. |
| Minimal propositional base (`MinPropAxiom`, `MinimalHilbert`, subsumption) | `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`, `Foundations/Logic/ProofSystem.lean` | Referenced for axiom shapes; `MinPropAxiom` has 8 schemata (no efq, no peirce). |

**BibKeys** (verified in `/home/benjamin/Projects/cslib/references.bib`): `Simpson1994` (86), `Wijesekera1990` (885), `ChagrovZakharyaschev1997` (75), `Johansson1937` (317, minimal logic origin). All present.

Barrel: new MK files must be added to `Cslib.lean` via `lake exe mk_all --module` (IK is at `Cslib.lean:372`; Constructive block at 353–361).

---

## Crux (Task Deliverable 2): Exactly which IK steps depend on efq/explosion, and how they change

I traced every `h_efq` occurrence in `Intuitionistic/CanonicalModel.lean` (1273 L), `TruthLemma.lean` (504 L), `PrimeTheory.lean` (360 L), `Completeness.lean` (335 L). `h_efq` splits into **three roles**:

### Role A — World consistency (REMOVED wholesale by `Cons := fun _ => True`)

IK worlds are `CanonicalPrimeWorld Axioms := {S // ModalPrimeTheory Axioms S}` where `ModalPrimeTheory` (`PrimeTheory.lean:71`) **bakes in `ModalSetConsistent` (⊥-not-derivable)**. Every witness/frame lemma must re-establish consistency of the set it builds, and that is where most `h_efq` uses live:

- `modal_imp_witness` (`PrimeTheory.lean:267`): Step 1 "`S ∪ {φ}` is consistent" runs the classical intuitionistic argument `S∪{φ}⊢⊥ ⟹ S⊢¬φ ⟹`(via `modalNegPhiImpPsi`, efq)`⟹ S⊢φ→ψ`. **This entire step vanishes** when there is no consistency requirement — cf. `min_imp_witness` (`MinLindenbaum.lean:138`, "no EFQ or consistency sub-proof is needed") and its already-delivered modal form `imp_refuting_theory` (`SegmentLindenbaum.lean:142`).
- `modal_prime_exclusion`'s EFQ bridge (`PrimeTheory.lean:337–346`): "`phi ∈ cl X` when `X` inconsistent" — the hypothesis `¬ Cons X` is `¬ True = False` for MK, so the bridge is **vacuous** (`quasi_prime_exclusion` supplies `fun {X} h => absurd trivial h`, `SegmentLindenbaum.lean` / `MinLindenbaum.lean:186`).
- `canonical_bot_not_mem` (`TruthLemma.lean:85`) uses world consistency `w.property.1.1`. For MK this lemma is **dropped**: the `.bot` truth case is `botForces w = (⊥∈w.val)`, so `truth_bot_case` (already `botForces`-parametric, `TruthLemma.lean:141`) closes by `h_bot := fun _ => Iff.rfl` — no consistency, no efq. (Contrast IK's `mvalid_completeness` line 314 which passes `fun _ => Iff.rfl` too but over *consistent* worlds; MK passes it over *quasi-prime* worlds.)
- The many `h_cons_raw : ModalSetConsistent …` obligations in the box/diamond/f1/f2 witnesses (`CanonicalModel.lean:665,693,942,1162,1230`, each discharged via `hbwu/hdwu … bigOr_nil_eq_bot`) **all disappear** — quasi-prime worlds carry no consistency field.

**Net:** Role A is not "changed", it is *deleted*. Already done for MK in `Segment.lean`/`SegmentLindenbaum.lean`.

### Role B — `⊥`-base cases of the box/diamond DISTRIBUTION lemmas (the genuine obstruction)

These are **not** about consistency; they are the combinatorial core that preserves the **diamond-image clause** of `canonicalR` under witness construction. They use `⊥`-theorems that MK does **not** have:

- `boxOr_of_boxDisj` (`CanonicalModel.lean:240`), empty case (line 254): goal `bigOr [] .imp box(bigOr [])` = **`⊥ → □⊥`**, proved `.ax [] _ (h_efq (□⊥))`. **`⊥ → □⊥` is NOT an MK theorem** (efq-only).
- `diaOr_of_diaDisj` (`CanonicalModel.lean:785`), empty case (line 791): goal `(◇ bigOr []).imp bigOr []` = **`◇⊥ → ⊥`**, proved `.ax [] _ h_dbot`. **`◇⊥ → ⊥` (Nd) is NOT an MK axiom** (MK drops Nd — confirmed report 492 §Adversarial: Nd is only `IValid`-sound).
- `dia_bigAnd_to_bigAnd_dia` (line 315) empty case and `bigAnd_mem_u` (line 359) empty case use `h_efq ⊥` **only to prove `⊤ = ⊥→⊥`** — this is *replaceable*: `⊤` is derivable in minimal logic from implyK+implyS (the identity combinator, already built as `d_id` in `PrimeTheory.lean:205–213`). So these two are **not** true obstructions; substitute a minimal `⊤`-proof.

The real obstructions are `⊥ → □⊥` and `◇⊥ → ⊥`. Both arise from the **empty-list (`bigOr [] = ⊥`) base case** of the `bigOr` set-exclusion machinery IK uses to keep the diamond witness simultaneously prime, consistent, and diamond-clause-preserving.

**How they change for MK — the resolution:** In MK, worlds MAY contain `⊥` (fallible) and MAY contain `◇⊥`. The very obstructions `⊥→□⊥`, `◇⊥→⊥` that IK needs to *avoid fallible worlds* are exactly what MK does **not** need, because MK *embraces* fallible worlds. The exploding theory `Set.univ` (`quasiPrime_univ`, `Segment.lean:80`) trivially satisfies every diamond/box clause. Consequently MK's box/diamond witnesses should be built from the **efq-free** `box_refuting_theory`/`dia_refuting_theory` (`SegmentLindenbaum.lean:168,194`) — which extend `boxInv H` by `quasi_prime_exclusion` and witness diamonds without any `bigOr`/`⊥→□⊥`/`◇⊥→⊥` step — **not** from IK's `boxOr_of_boxDisj`/`diaOr_of_diaDisj`. This is the single most important design decision in the plan (§Design, and §Risk).

### Role C — Inconsistent-case split in `*_completeness` (REMOVED)

`ivalid_completeness`/`mvalid_completeness` (`Completeness.lean:241–254, 317–330`) `by_cases` on consistency of `cl ∅`; the inconsistent branch uses `h_efq` (`d_efq := .ax [] _ (h_efq φ)`) to derive `φ`. For MK there is **no consistency predicate**, so **there is no case split**: the contrapositive proof extends `cl ∅` (a quasi-prime-extendable `MinTheory`/`QuasiPrime`) directly by `quasi_prime_exclusion`, exactly as propositional `min_strong_completeness` (`MinStrongCompleteness.lean`) does (single branch, no efq). MK is **weak**-complete like IK; the `Γ=∅` instantiation suffices, but strong completeness comes free from the same template if wanted.

---

## Minimal ⊥ Treatment (Task Deliverable 3): effect on the canonical model

Confirmed via the propositional template (`MinStrongCompleteness.lean:40–104`) and CK's `Segment.lean` (fallible-world design). MK's canonical model:

1. **Worlds = quasi-prime theories** `{S // QuasiPrime MKModalAxiom S}` (deductively closed + disjunction property, **no consistency**). `⊥ ∈ S` is *permitted*; `⊥ ∈ S → S = Set.univ` is *not* forced (unlike with efq — cf. `Segment.lean:60` note "With `efq`, quasi-prime ⇒ consistent-prime OR exploding; without efq, genuinely intermediate fallible worlds exist"). This is the mathematical heart of "⊥ ordinary".
2. **`botForces w := ⊥ ∈ w.val`** (`minBotForces`, `MinStrongCompleteness.lean:101`; `cbotForces`, `Segment.lean`). Upward-closed for free via `≤ = ⊆` (`minBotForces_upward_closed`).
3. **`.bot` truth-lemma case is `Iff.rfl`** (`truth_bot_case` with `h_bot := fun _ => Iff.rfl`). No `canonical_bot_not_mem`, no consistency, no efq.
4. **`≤ = set inclusion`, `canonicalVal p := atom p ∈ w.val`** — identical shape to IK/`MinCanonicalWorld` (`MinStrongCompleteness.lean:74–91`).
5. **Semantics is `MValid`** (birelational, ∃-diamond, **F1/F2 confluence**), NOT `CKValid`. Justification (from `Constructive/CK.lean` header, verified): MK **keeps** Cd and Idb, which are exactly the axioms `MValid`'s F1/F2 + ∃-diamond validate (`ik_axiom_sound` `cd`/`idb` cases). MK **drops** efq (not `MValid`-sound, but MK has no efq to be unsound) and Nd (not `MValid`-valid under arbitrary `botForces`, and MK has no Nd). So `MValid` is precisely MK's semantics — MK is the `MValid` sibling of IK, whereas CK is the weaker `CKValid` (∀∃, no confluence) sibling. **Do not** route MK through the CK segment/`CKValid` model; reuse only CK's *quasi-prime prime-theory* lemmas, not its segment *forcing*.

---

## Recommended Lean 4 Design (Task Deliverable 4)

Namespace `Cslib.Logic.Modal` (singular `Logic`, per convention). Proposed subtree
`Cslib/Logics/Modal/Metalogic/Minimal/` (parallel to `Intuitionistic/`, `Constructive/`), keeping all delivered files untouched (Zero-Debt / concurrent-session safety).

### Phase 1 — `MK.lean` axiom datatype + soundness (small, near-deterministic)

```lean
namespace Cslib.Logic.Modal
open Cslib.Logic
variable {Atom : Type*}

/-- Axiom schemata for minimal modal logic MK = IK − efq − Nd: the 8 MINIMAL propositional
schemata (mirroring `MinPropAxiom`, i.e. `IntPropAxiom` without `efq`) plus the 4 modal
schemata `k`,`kdia`,`cd`,`idb` (NO `dbot`/Nd). -/
inductive MKModalAxiom : Proposition Atom → Prop where
  | implyK (φ ψ) : MKModalAxiom (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ) : MKModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | andI (φ ψ)  : MKModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  | andE1 (φ ψ) : MKModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  | andE2 (φ ψ) : MKModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  | orI1 (φ ψ)  : MKModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  | orI2 (φ ψ)  : MKModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  | orE (φ ψ χ) : MKModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  | k (φ ψ)    : MKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  | kdia (φ ψ) : MKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  | cd (φ ψ)   : MKModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  | idb (φ ψ)  : MKModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
```

Soundness mirrors `ik_axiom_sound` (`IK.lean:131`) but returns **`MValid`** (arbitrary `botForces`) and keeps only the 8 minimal-prop cases + `k`/`kdia`/`cd`/`idb`. Verified from `IK.lean`: those four modal cases and the eight propositional cases **never inspect `botForces`** (only `efq` uses `hbot.elim` and `dbot` uses the `False` witness — both dropped). So they transcribe verbatim, replacing the `IValid` intro-prologue (`intro World _ r f1 f2 val v_uc w; have bf_uc … := fun _ h => h.elim`) with the `MValid` prologue (`intro World _ r f1 f2 val botForces v_uc bf_uc w`). The `idb` case still consumes `f2` identically.

```lean
theorem mk_axiom_sound {φ : Proposition Atom} (h : MKModalAxiom φ) : MValid.{u,v} φ := …
theorem mk_soundness {Γ φ} (d : DerivationTree MKModalAxiom Γ φ) … : BForces r val botForces w φ := …  -- mirror ik_soundness; necessitation case identical
theorem mk_soundness_derivable {φ} (h : Derivable MKModalAxiom φ) : MValid.{u,v} φ := …
theorem mk_consistent : ¬ Derivable MKModalAxiom (Proposition.bot : Proposition Atom) := …
  -- corollary of soundness at a NON-fallible one-point frame (botForces := fun _ => False),
  -- mirroring ik_consistent (IK.lean:248); OR lift to MinPropAxiom soundness à la min_consistent.
```

Estimated ~150–200 L. Zero new machinery. **This phase is low-risk and should land first.**

### Phase 2 — `MinPrimeTheory.lean` (mostly reuse; thin wrappers)

Reuse `QuasiPrime MKModalAxiom`, `quasi_prime_exclusion`, `imp_refuting_theory`,
`box_refuting_theory`, `dia_refuting_theory`, `box_mem_of_boxed_context`,
`quasi_head_realization` from `Constructive/{Segment,SegmentLindenbaum}.lean` **directly**
(they are `Axioms`-parametric at `Cons=fun _ => True`). Add only:
- `MinCanonicalPrimeWorld := {S // QuasiPrime MKModalAxiom S}` + `Preorder` (⊆) + `canonicalVal` + `minBotForces := ⊥∈w.val` + upward-closure (all copy `MinStrongCompleteness.lean:74–108`).
- `min_head_realization`: `¬ Derivable MKModalAxiom φ → ∃ quasi-prime T, φ∉T` (wrap `quasi_head_realization`, `SegmentLindenbaum.lean:242`).

### Phase 3 — `MinCanonicalModel.lean` (the crux; highest risk — build the birelational ∃-diamond canonical R over quasi-prime worlds)

`canonicalR w v := (∀φ, □φ∈w → φ∈v) ∧ (∀φ, φ∈v → ◇φ∈w)` (both clauses; ∃-diamond needs the image clause). Then:
- `min_canonical_box_witness`: `□φ∉w → ∃ quasi-prime v, canonicalR w v ∧ φ∉v` — **build from `box_refuting_theory`** (`SegmentLindenbaum.lean:168`, efq-free), NOT `boxOr_of_boxDisj`.
- `min_canonical_diamond_witness`: `◇φ∈w → ∃ quasi-prime v, canonicalR w v ∧ φ∈v` — **build from `dia_refuting_theory`** (`SegmentLindenbaum.lean:194`). Diamond-image-clause obligations that IK discharged via `diaOr_of_diaDisj`+`h_dbot` are discharged here by **fallible worlds** (a would-be `◇⊥→⊥` obstruction is moot because `◇⊥∈w` is permitted; worst case the witness is `Set.univ`).
- `min_canonical_f1`/`min_canonical_f2` (F1 via diamond witness, F2 via box witness; standard confluence over quasi-prime worlds, efq-free).

### Phase 4 — `MinTruthLemma.lean`

`min_canonical_truth_lemma : BForces canonicalR canonicalVal minBotForces w φ ↔ φ∈w.val`, by induction:
- `atom` = `Iff.rfl`; **`bot` = `Iff.rfl`** (minBotForces def); `and`/`or` = copy `TruthLemma.lean` cases (they use only closure + disjunction property, both in `QuasiPrime`);
- `imp` = via `imp_refuting_theory` (efq-free) + `quasi_prime_exclusion`;
- `box`/`diamond` = via Phase-3 witnesses.

### Phase 5 — `MinCompleteness.lean` + wire barrel

```lean
theorem mk_completeness {φ} (h : MValid.{u,u} φ) : Derivable MKModalAxiom φ := by
  by_contra h_not
  -- single branch (NO consistency case split): extend cl ∅ by quasi_prime_exclusion,
  -- apply MValid at the canonical model (botForces := ⊥∈·), truth lemma, contradict exclusion.
  …
theorem mk_soundness_completeness {φ} : MValid.{u,u} φ ↔ Derivable MKModalAxiom φ :=
  ⟨mk_completeness, mk_soundness_derivable⟩
```
Mirror `min_strong_completeness` (`MinStrongCompleteness.lean`) at `Γ=∅`. Then `lake exe mk_all --module` to add all five files to `Cslib.lean`.

---

## Reusable Lemmas & Mathlib API (Task Deliverable 5)

**Reuse (in-repo, all confirmed present):** `QuasiPrime`, `QuasiPrime.closed/.disj`, `quasiPrime_univ`, `quasi_prime_exclusion`, `imp_refuting_theory`, `box_refuting_theory`, `dia_refuting_theory`, `box_mem_of_boxed_context`, `quasi_head_realization` (`Constructive/Segment.lean`, `SegmentLindenbaum.lean`); `Metalogic.prime_exclusion`, `Admissible`, `PrimeAdmissible` (`Foundations/Logic/Metalogic/PrimeExclusion.lean`); `DerivationTree`/`modalDerivationSystem`/`Derivable`, `deductionTheorem`/`hasDeductionTheorem` (`Modal/Metalogic/{DerivationTree,DeductionTheorem}.lean`); `BForces`/`MValid`/`bforces_persistence`/`mvalid_implies_ivalid` and the `@[simp]` `BForces_*` unfolds (`Semantics/Birelational.lean`); the `botForces`-parametric `truth_atom/bot/and/or_case` (`TruthLemma.lean`); `box_mono`/`dia_mono`/`imp_trans0`/`unpack_conj_partial`/`bigAnd`/`bigOr` helpers (`CanonicalModel.lean`, if the ∃-diamond witness needs them — but prefer the segment lemmas). Structural templates: `MinLindenbaum.lean`, `MinStrongCompleteness.lean`, `IK.lean`.

**Mathlib API needed: essentially none new.** The existing development already uses only `Set` operations (`Set.subset_union_left`, `Set.mem_union/insert/singleton_iff`, `Set.Subset.trans/refl`), `Preorder`/`le_refl`/`le_trans`, `List.mem_*`, `Classical.propDecidable`, and Zorn (inside `prime_exclusion`, already discharged generically). No new `import Mathlib.*` beyond what `PrimeTheory.lean`/`Birelational.lean` already pull. Every MK file begins `import Cslib.Init`.

---

## Adversarial Self-Verification (H4-style) & Risk

1. **"MK = delete the `h_efq` lambda from `mvalid_completeness`" — REFUTED.** `mvalid_completeness` (`Completeness.lean:263`) takes `h_efq` and uses it at line 329 (inconsistent branch) AND its worlds are `ModalSetConsistent` (consistency baked in); every witness lemma it calls (`canonical_f1/f2`, `canonical_truth_lemma`, `modal_prime_exclusion`) threads `h_efq` for consistency (Role A) and the `bigOr` base cases thread it for `⊥→□⊥` (Role B). MK has no `h_efq` to supply. Confidence: HIGH (direct source read).
2. **"MK could reuse IK's `boxOr_of_boxDisj`/`diaOr_of_diaDisj`" — REFUTED.** Their empty-list base cases are `⊥→□⊥` (efq, line 254) and `◇⊥→⊥` (`h_dbot`, line 791) — neither is derivable in MK. Confidence: HIGH.
3. **"MK should target `CKValid` like CK (task 493)" — REFUTED.** MK keeps Cd+Idb, which are `MValid`-valid (`ik_axiom_sound` `cd`/`idb`) but NOT `CKValid`-derivable-only-with-extensions. MK is the `MValid` sibling; CK is the `CKValid` sibling (CK.lean header, verified). MK reuses CK's quasi-prime *prime-theory* lemmas but NOT its segment *forcing*. Confidence: HIGH.
4. **"The `⊤`-via-efq base cases (`bigAnd_mem_u`, `dia_bigAnd_to_bigAnd_dia`) block MK" — REFUTED.** Those prove `⊤ = ⊥→⊥`, derivable in minimal from implyK+implyS (identity combinator, present at `PrimeTheory.lean:205–213`). Not an obstruction; substitute the minimal `⊤`-proof. Confidence: HIGH.
5. **Residual GENUINE RISK (flagged honestly): the ∃-diamond diamond-witness over quasi-prime worlds (Phase 3).** IK preserves `canonicalR`'s diamond-image clause via the `bigOr` set-exclusion (efq+dbot). MK must preserve the *same* clause without those. The report's resolution — reuse `dia_refuting_theory` and let fallible/exploding worlds discharge the obligations — is well-motivated by CK's fallible-world design and the propositional Min template, **but the exact ∃-diamond (vs CK's ∀∃) canonicalR diamond-clause preservation has no line-for-line in-repo precedent** (CK uses segments; propositional Min has no modality). **Mitigation & Zero-Debt directive:** implement Phase 1 (soundness, low-risk) first and commit; in Phase 3, first attempt the `dia_refuting_theory`-based witness; if a diamond-clause obligation cannot be closed sorry-free, do **NOT** insert `sorry`, `axiom`, or a vacuous `def := True` — mark the phase **[BLOCKED]**, record the exact unclosable goal state, and escalate to user review (candidate escalation: whether MK's canonical `R` should adopt CK's segment head/tail structure while retaining the ∃-diamond `BForces`, or whether MK completeness is more naturally stated with the fallible-world `Set.univ` witness inlined). Confidence that a sorry-free construction EXISTS: MEDIUM-HIGH (standard Fischer-Servi minimal-modal completeness result); confidence it reuses cleanly without a small bespoke diamond lemma: MEDIUM.

**Zero-debt**: no step in this plan recommends `sorry`/`axiom`/placeholder. Every axiom of MK is a `DerivationTree`-carried schema; every reused lemma is sorry-free on `main`.

---

## Next Step

`/plan 495` — five phases as above; Phase 1 (axioms+soundness) and Phase 2 (quasi-prime wrappers) are near-deterministic and should land + commit first; Phase 3 (∃-diamond diamond-witness over quasi-prime worlds) is the crux and the sizing bottleneck — plan it as its own phase with an explicit [BLOCKED]-escalation clause. Consider `/plan 495 --hard` given the literature-faithful, previously-unbuilt diamond-witness step.
