# Research Report 01: Minimal Modal Extensions MT / MS4 / MS5 as Modular Extensions of MK

- **Task**: 496 — minimal-base analogues of T / S4 / S5 as modular extensions of minimal modal
  logic MK (task 495, COMPLETED), via the axiom↔frame-condition correspondences over the minimal
  birelational (`MValid`) semantics. (Lower priority / exploratory.)
- **Task type**: cslib | **Session**: sess_1784044271_09e821_496 | **Date**: 2026-07-14
- **Territory** (concurrent sessions active): NEW files only, under
  `Cslib/Logics/Modal/Metalogic/Minimal/` (proposed `MT.lean`, `MS4.lean`, `MS5.lean`, plus a
  shared `MinExtension.lean` scaffold). No edits to delivered MK / IK / CK files. Single shared
  edit: the `Cslib.lean` barrel (via `lake exe mk_all --module`).

---

## Verdict (one line)

**MT / MS4 / MS5 completeness is TRACTABLE and zero-debt, mirroring the IK extension pattern of
task 494 — it does NOT inherit the CS4 / CS5 blocker of task 501.** The reason is structural and
decisive: MK reuses IK's **birelational, single-world, two-clause `minCanonicalR` over quasi-prime
worlds with F1/F2 confluence**, over which the T/4/B frame-condition closures are proved
**positively** (`min_axiom_mem` + MP-closure via `QuasiPrime.closed`) for *every* quasi-prime
world — exactly as IK's `it_/is4_/is5_canonical_*` do for prime worlds. The CS4/CS5 obstruction
lives **entirely** in CK's *segment* model (head + tail, `cmreach = tail membership`, no F1/F2,
blanket ≤-composed FC, `diamRefutingSegment` restricted-tail-vs-maximal-tail tension) — a structure
MK **does not use**. Consequently: (a) frame conditions are **plain** (`∀ w, r w w`, plain
transitivity, plain symmetry on the raw `r`), **NOT** the ≤-composed form CK required, because
`MValid`'s ambient F1/F2 absorb the ≤-composition in the box-form soundness cases (as MK's `idb`
already uses `f2`); (b) **no world-subtype invariant** is needed; (c) axiomatize **MS5 via B
(symmetry), not euclidean-5**, as IK/CK both did. Highest residual risk: the MS5 symmetric closure
(`min_canonical_symmetric`) — but it is a verbatim port of the already-compiled, fully positive
`is5_canonical_symmetric` (`IS5.lean:341`), so risk is LOW-MODERATE, not the research-scale blocker
CS5 hit. Confidence: **HIGH** (grounded in direct reads of all delivered MK/IK/CK files).

---

## Source-to-Implementation Mapping (files located, all verified)

All paths absolute under `/home/benjamin/Projects/cslib/`.

| Concern | Delivered file | Reuse verdict for MT/MS4/MS5 |
|---|---|---|
| **MK axioms + `MValid` soundness** (`MKModalAxiom`, `mk_axiom_sound`, `mk_soundness`, `mk_soundness_derivable`, `mk_consistent`) | `Cslib/Logics/Modal/Metalogic/Minimal/MK.lean` | **STRUCTURAL BASE** — extend `MKModalAxiom` with T/4/B constructors; extend `mk_axiom_sound`'s `cases` with new cases; reuse `mk_soundness` structural wrapper (threads `botForces`/`bf_uc`) verbatim with an extra FC parameter. |
| **MK quasi-prime worlds** (`MinCanonicalPrimeWorld`, `Preorder` (⊆), `minCanonicalVal`, `minBotForces`, upward-closure, `min_head_realization`) | `Cslib/Logics/Modal/Metalogic/Minimal/MinPrimeTheory.lean` | **REUSE as-is**. Same world type for all three extensions; no subtype. |
| **MK two-clause canonical R + witnesses + F1/F2** (`minCanonicalR`, `min_canonical_box_witness`, `min_canonical_diamond_witness`, `min_canonical_f1`, `min_canonical_f2`, bespoke `bigOr1`/`bigAnd1`/`quasi_prime_set_exclusion1` nonempty-list machinery) | `Cslib/Logics/Modal/Metalogic/Minimal/MinCanonicalModel.lean` (~1090 L) | **REUSE as-is** — the witnesses and F1/F2 are FC-agnostic; each extension only *adds* a positive FC-closure lemma about the *same* `minCanonicalR`. |
| **MK truth lemma** (`min_canonical_truth_lemma`, `bot` = `Iff.rfl`, `imp` via `imp_refuting_theory`) | `Cslib/Logics/Modal/Metalogic/Minimal/MinTruthLemma.lean` | **REUSE as-is** — the truth lemma is over `minCanonicalR`/`minCanonicalVal`/`minBotForces`, unchanged by the FC restriction (the FC is only supplied at the *completeness* application). |
| **MK completeness** (`mk_completeness` single-branch, `mk_soundness_completeness`) | `Cslib/Logics/Modal/Metalogic/Minimal/MinCompleteness.lean` | **STRUCTURAL TEMPLATE** for `mkvalidFC_completeness` — a ~2-line generalization threading `h_canonFC : FC minCanonicalR` into the `h_valid` application (see §4). |
| **`QuasiPrime` deductive closure** (`QuasiPrime.closed : DeductivelyClosed …`, `QuasiPrime.disj`) | `Cslib/Logics/Modal/Metalogic/Constructive/Segment.lean:64,68,74` | **REUSE as-is** — the sole engine of the positive FC closures (`min_axiom_mem`, `min_imp_property`). |
| **IK extension scaffold** (`IValidFC`, `ivalidFC_completeness`, `axiom_mem`) | `Cslib/Logics/Modal/Metalogic/Intuitionistic/Extension.lean` | **STRUCTURAL BLUEPRINT** for `MinExtension.lean` — but NOT importable (it hardcodes `botForces := fun _ => False` and consistent prime worlds; MK keeps arbitrary `botForces` and quasi-prime worlds). |
| **IK per-system files** (`itFC`/`is4FC`/`is5FC` LOCAL predicates on raw `r`; `it_/is4_/is5_axiom_sound`; positive `*_canonical_reflexive/transitive/symmetric`; `*_completeness`; euclidean-vs-B finding) | `Cslib/Logics/Modal/Metalogic/Intuitionistic/{IT,IS4,IS5}.lean` | **STRUCTURAL TEMPLATE** — the 6-part per-system shape, the box+diamond axiom pairing, the local-FC-predicate convention (Mathlib `Reflexive`/`Transitive`/`Symmetric` are `@[deprecated]` in the pinned Mathlib — do NOT use them), the positive-closure proof style, and the B-not-euclidean decision all copy. |
| **IK `canonical_imp_property`** (MP-closure `(φ→ψ)∈w → φ∈w → ψ∈w`) | `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean:99` | **PORT** — the MK analogue `min_imp_property` is a one-liner over `QuasiPrime.closed`. |

**BibKeys** (verified present in `references.bib` by tasks 494/495): `Simpson1994`,
`Wijesekera1990`, `ChagrovZakharyaschev1997`, `Johansson1937`. No additions needed. Sources for
this task: Simpson1994 Ch. 3 (birelational frame classes T/S4/S5, `MValid`), and the delivered IK
IT/IS4/IS5 as the faithful in-repo template.

---

## Deliverable 1 — MK machinery from task 495 that MT/MS4/MS5 will extend

### 1.1 The axiom base (`MK.lean`)

`MKModalAxiom` (MK.lean:68–105) = **8 minimal-propositional schemata** (`implyK`, `implyS`,
`andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE` — `MinPropAxiom`, i.e. `IntPropAxiom` minus `efq`)
**+ 4 modal schemata** `k` (Kb), `kdia` (Kd), `cd` (Fischer-Servi Cd), `idb` (Fischer-Servi Idb).
**No** `efq`, **no** `dbot`/Nd. `mk_axiom_sound` (MK.lean:116) proves each instance `MValid.{u,v}`
under the prologue `intro World _ r f1 f2 val botForces v_uc bf_uc w`; the four modal cases never
inspect `botForces`, and `idb` (MK.lean:157–163) consumes `f2` to relocate the `◇φ`-witness world.
`mk_soundness` (MK.lean:170) is the structural-induction wrapper (`ax`/`assumption`/`modus_ponens`/
`necessitation`/`weakening`); `mk_consistent` (MK.lean:212) instantiates a non-fallible one-point
`ℕ`-frame.

### 1.2 The canonical model (the crux MK delivered)

- **Worlds** = `MinCanonicalPrimeWorld Atom := {S // QuasiPrime MKModalAxiom S}`
  (MinPrimeTheory.lean:58): quasi-prime = deductively closed + disjunction property, **no
  consistency** (`⊥ ∈ S` permitted; fallible/exploding worlds admitted). `≤` = set inclusion.
- **`minCanonicalR w v := (∀φ, □φ∈w → φ∈v) ∧ (∀φ, φ∈v → ◇φ∈w)`** (MinCanonicalModel.lean:75) —
  the SAME two-clause relation as IK's `canonicalR`, defined **directly on the single quasi-prime
  world type** (no segments, no tails).
- **`minBotForces w := ⊥ ∈ w.val`** (MinPrimeTheory.lean:97) — a genuine predicate, upward-closed
  for free. `.bot` truth case = `Iff.rfl`.
- **Witnesses + confluence**: `min_canonical_box_witness` (:717), `min_canonical_diamond_witness`
  (:886), `min_canonical_f1` (:1036), `min_canonical_f2` (:1063). The diamond witness produces a
  *single* quasi-prime world `v` with `minCanonicalR w v ∧ φ∈v` — the ∃-diamond of `MValid`.
- **The bespoke nonempty-list exclusion machinery** MK had to build (because IK's
  `Metalogic.prime_set_exclusion` is `efq`-dependent via `bigOr`'s `⊥`-terminating base case):
  `bigOr1`/`bigAnd1` (terminate at the list *head*, not `⊥`), `quasi_prime_set_exclusion1`,
  `box_witness_pair_underivable1`, `diamond_witness_underivable1`, `canonical_f1_underivable1`
  (MinCanonicalModel.lean:78–1030). **This machinery is entirely internal to the witnesses/F1/F2
  and is FC-agnostic — the extensions reuse it untouched and never re-enter it.**
- **Completeness** `mk_completeness` (MinCompleteness.lean:55) is **single-branch** (no consistency
  case split): `min_head_realization h_not_deriv` extends `cl ∅` to a quasi-prime `T` omitting `φ`;
  instantiate `MValid` at the canonical model rooted at `⟨T,hT⟩`; apply `min_canonical_truth_lemma`;
  contradict `φ∉T`.

### 1.3 The IK-extension pattern to mirror (task 494)

Task 494 delivered `Intuitionistic/{Extension,IT,IS4,IS5}.lean`. The scaffold `Extension.lean`
has exactly three declarations:

- `IValidFC (FC) φ` (Extension.lean:74): a copy of `IValid` with one extra binder `_fc : FC r`
  threaded **alongside** `f1`/`f2`. `IValid = IValidFC (fun _ => True)`.
- `ivalidFC_completeness` (Extension.lean:97): a ~2-line generalization of `ivalid_completeness`,
  taking `h_canonFC : FC (@canonicalR Atom Axioms)` and passing it into the `h_valid` application
  (Extension.lean:142). (It retains IK's consistent/inconsistent `by_cases`; the inconsistent
  branch uses `h_efq` — MK drops this branch entirely, see §4.)
- `axiom_mem` (Extension.lean:181): `Axioms φ → φ ∈ w.val` via `w.property.1.2 [] φ … ⟨.ax [] _ h⟩`.

Each per-system file is a uniform 6-part shape: (1) axiom inductive = predecessor + **two** new
schemata (box-form AND diamond-form, both required — ◇ is primitive, Wijesekera1990); (2) LOCAL
FC predicate on raw `r` (`itFC r := ∀ w, r w w`, etc. — verified NOT Mathlib `Reflexive`, which
is deprecated, IT.lean:25,127); (3) `*_axiom_sound` = inherited cases + 2 new cases; (4) positive
canonical FC closure via `axiom_mem` + `canonical_imp_property` (IT.lean:246–252 confirms
"no `by_contra`, no negation"); (5) `*_completeness` = `ivalidFC_completeness` instantiation;
(6) `*_consistent` + `*_soundness_completeness` biconditional. `is5_canonical_symmetric`
(IS5.lean:341) — the one closure routing a box membership back through the diamond clause via
`bDia` — is fully positive and already compiles.

---

## Deliverable 2 — Axiom ↔ frame-condition correspondences over `MValid`

Because `MValid` is IK's `IValid` semantics **with an arbitrary upward-closed `botForces`** (MK.lean
docstring lines 17–19, verified), the axiom shapes and the frame conditions are **identical to
IK's** — the only change is that soundness threads `botForces`/`bf_uc` through `intro` and the new
cases never inspect them (exactly as MK's own `k`/`kdia`/`cd`/`idb` cases do).

### 2.1 Axiom schemata (extend `MKModalAxiom`, box-form + diamond-form each)

```lean
-- MT (reflexivity):    tBox : □A → A       ;  tDia : A → ◇A
-- MS4 (+ transitivity): fourBox : □A → □□A ;  fourDia : ◇◇A → ◇A
-- MS5 (+ symmetry, B):  bBox : A → □◇A      ;  bDia : ◇□A → A       [B, NOT euclidean ◇A→□◇A]
```

### 2.2 Frame conditions — PLAIN form on raw `r` (KEY FINDING, contra the task's "≤-composed" prompt)

The task statement asks for the correspondences "stated in the appropriate ≤-composed form". That
phrasing carries over from CK/task-501, where the ≤-composed form was **forced** by `CKValid`
having **no F1/F2 confluence**. **`MValid` DOES carry F1/F2** (the same birelational confluence as
`IValid` — verified in MK.lean:175–176 and the `mk_soundness` signature). Therefore, for MK the
correct correspondences use the **plain** conditions on the raw relation `r`, and the ≤-composition
in the box-form soundness cases is discharged by the ambient F1/F2 — **not** folded into the frame
condition. This mirrors IK exactly (its `4□`/`B□` soundness use `f1`/`f2`, and MK's `idb` already
does — MK.lean:161).

| Axiom pair | Frame condition on `r` | Lean predicate (LOCAL, not Mathlib) |
|-----------|------------------------|-------------------------------------|
| `tBox`/`tDia` | **reflexive** `∀ w, r w w` | `def mtFC {World} (r) : Prop := ∀ w, r w w` |
| `fourBox`/`fourDia` | **transitive** `∀ ⦃w u v⦄, r w u → r u v → r w v` | `def ms4FC {World} (r) : Prop := (∀ w, r w w) ∧ (∀ {w u v}, r w u → r u v → r w v)` |
| `bBox`/`bDia` | **symmetric** `∀ ⦃w u⦄, r w u → r u w` | `def ms5FC {World} (r) : Prop := reflexive ∧ transitive ∧ (∀ {w u}, r w u → r u w)` |

Refl + trans + symm ⇒ equivalence relation ⇒ Simpson's S5 birelational frame class. Define these
LOCALLY (Mathlib `Reflexive`/`Transitive`/`Symmetric` are `@[deprecated]` in the pinned Mathlib
and would break the zero-warnings gate — IT.lean:25,127 and the CK finding both confirm). Note MK's
predicates, unlike CK's, do **NOT** need `[Preorder World]` in scope (no `≤` appears in them).

### 2.3 Soundness cases (over `BForces` with arbitrary `botForces`)

Copy the six new cases from task 494 Deliverable 3 verbatim; they are `botForces`-agnostic:

- **`tDia` `A→◇A`**, **`tBox` `□A→A`**: EASY, plain reflexivity + `bforces_persistence`.
- **`fourDia` `◇◇A→◇A`**: EASY, plain transitivity on the two `r`-steps.
- **`fourBox` `□A→□□A`**: MODERATE — uses `f2` to relocate (as `idb`/IS4 do).
- **`bDia` `◇□A→A`**: EASY, plain symmetry.
- **`bBox` `A→□◇A`**: EASY-MOD — persistence + symmetry, no F-relocation.

`bforces_persistence` takes `bf_uc` and works for arbitrary `botForces`, so every case transcribes
under the `MValidFC` prologue with the FC threaded unused into the inherited cases.

### 2.4 S5 via B, not euclidean-5 (adversarial, reconfirmed)

Axiomatize MS5 via **B (symmetry)**. The classical `canonical_eucl`/`canonical_eucl_from_5` proofs
are `by_contra` + `mcs_neg_of_not_mem` + double-negation, depending on **negation-completeness of
maximal-consistent sets**. Quasi-prime theories are *even further* from negation-complete than IK's
prime theories (they admit `Set.univ` and impose no consistency), so the euclidean route has no
analogue here. Symmetry closure from B is fully positive (MP-closure only) and transfers cleanly —
this is the same finding tasks 494 and 501 made, propagating with extra force to the quasi-prime
setting.

---

## Deliverable 3 — Completeness tractability: CONCRETE VERDICT

**Verdict: MT/MS4/MS5 completeness is TRACTABLE (all three), zero-debt, and does NOT hit a
`diamRefutingSegment`-style obstruction. It follows the IK/task-494 pattern, not the CK/task-501
pattern.** Confidence: HIGH.

### 3.1 Why CS4/CS5 blocked (the obstruction, precisely — from the task-501 summary)

The CS4/CS5 blocker has three interlocking causes, **all specific to CK's segment model**:

1. `CKValid` carries **no F1/F2**, forcing ≤-composed blanket frame conditions.
2. The canonical model is a **segment** model: worlds are `⟨head, tail, …⟩`; the frame relation is
   `cmreach P Q := Q.head ∈ P.tail` (tail membership). `cmreach` is **not** globally reflexive/
   transitive/symmetric (a segment may have an arbitrary tail), so `CKValidFC FC` — which demands
   `FC` on the *entire* world type — fails.
3. The truth lemma's diamond-backward case **structurally requires** `diamRefutingSegment` (a
   *restricted*-tail witness omitting a formula `A`). But a maximal-tail witness (which *would*
   make ≤-composed transitivity hold) always contains `Set.univ` in its tail and trivially forces
   every diamond, degenerating the model. These two requirements are in **direct tension**;
   resolving it needs a *hereditary* diamond-refuting construction (new Lindenbaum machinery) or a
   different technique (filtration/unraveling) — "research-scale, not a single-lemma fix."

### 3.2 Why MK escapes all three

| CS4/CS5 blocker cause | MK/MT/MS4/MS5 status |
|---|---|
| (1) No F1/F2 ⇒ ≤-composed FC | **`MValid` HAS F1/F2** (verified MK.lean:175–176). Frame conditions are **plain** on raw `r`; ≤-composition is absorbed by F1/F2. No ≤-composed predicates. |
| (2) Segment model; `cmreach` = tail membership; FC fails globally | **No segment model.** `minCanonicalR` is the two-clause relation over **single** quasi-prime worlds (MinCanonicalModel.lean:75), defined directly on the world type. The FC closure `min_canonical_reflexive : ∀ w, minCanonicalR w w` (etc.) is proved **positively for every quasi-prime world** via `min_axiom_mem` + MP-closure — so `FC minCanonicalR` holds on the whole world type, **no subtype restriction**. |
| (3) `diamRefutingSegment` restricted-tail-vs-maximal-tail tension | **No `diamRefutingSegment`, no tails.** MK's diamond witness (`min_canonical_diamond_witness`) yields a single quasi-prime world; the box/diamond witnesses and F1/F2 are FC-agnostic and are reused untouched. The extensions only *add* a positive closure lemma about `minCanonicalR`; they never re-enter the witness construction. |

### 3.3 The positive-closure argument transfers from prime to quasi-prime worlds

The IK closures (`it_/is4_/is5_canonical_*`) use exactly two ingredients: `axiom_mem` (place an
axiom instance into the world via deductive closure) and `canonical_imp_property` (MP-closure).
Both depend **only on deductive closure**, which quasi-prime worlds have via `QuasiPrime.closed :
DeductivelyClosed (modalDerivationSystem Axioms) S` (Segment.lean:68). **Neither uses consistency,
`efq`, or the disjunction property.** Hence:

- `min_axiom_mem (h : MKModalAxiom φ) : φ ∈ w.val := w.property.1.2 [] φ (fun _ h => nomatch h) ⟨.ax [] _ h⟩`
  (or via `(QuasiPrime.closed w.property) …`) — one-liner, mirrors `axiom_mem`.
- `min_imp_property {w} : (φ.imp ψ) ∈ w.val → φ ∈ w.val → ψ ∈ w.val` — MP-closure via
  `QuasiPrime.closed` applied to `[φ.imp ψ, φ] ⊢ ψ`, mirrors `canonical_imp_property`
  (TruthLemma.lean:99). One short proof.

Every T/4/B closure clause is then a chain of `min_axiom_mem` + `min_imp_property` over
`minCanonicalR`'s two clauses — identical to IK's proofs (task 494 Deliverable 4), which are
already compiled and positive. The highest-risk one, `min_canonical_symmetric` (routing `□φ∈v →
φ∈w` back through the diamond clause via `bDia`), is a verbatim port of `is5_canonical_symmetric`
(IS5.lean:341).

### 3.4 Residual risk (honest)

The only non-mechanical step is porting `is5_canonical_symmetric` and `is4_canonical_transitive`
from `canonicalR`/prime worlds to `minCanonicalR`/quasi-prime worlds. Because the proofs use only
deductive closure (present in both) and never consistency, the port is expected to be verbatim
modulo the `min` prefix and the `QuasiPrime.closed` accessor. **Confidence a sorry-free
construction exists: HIGH** (it is a strictly-simpler analogue of an already-compiled IK proof).
**Confidence it needs zero bespoke lemmas: HIGH** for MT/MS4, **MEDIUM-HIGH** for MS5 (the symmetry
closure is the least obvious chaining, but is already solved for IK). This is categorically unlike
CS5, whose blocker was a structural impossibility in the segment model, not a closure-proof
difficulty.

---

## Deliverable 4 — Recommended Lean 4 design + phase decomposition

Namespace `Cslib.Logic.Modal`. New files under `Cslib/Logics/Modal/Metalogic/Minimal/`, all
beginning `import Cslib.Init`. Prefix all shared-shape names with `min`/`mt`/`ms4`/`ms5` from the
start (task 495 hit a `canonicalR`/`canonicalVal` name collision with IK in the same namespace —
summary Follow-ups). Names use `theorem`/`lemma` for Prop-valued; docstrings on every declaration
(docBlame); `@[expose] public section`; `lowerCamelCase` (existing `mk_`/`it_` theorems use
underscores — keep identical, it passes the current lint).

### Phase 1 — `MinExtension.lean` (scaffold; LOW risk, near-deterministic)

The segment/birelational analogue of IK's `Extension.lean`, but keeping arbitrary `botForces`:

- **`MValidFC (FC) φ`**: a copy of `MValid` with one extra binder `_fc : FC r` threaded alongside
  `f1`/`f2`, **retaining** the `botForces`/`bf_uc` binders (unlike `IValidFC`, which hardcodes
  `fun _ => False`). `MValid = MValidFC (fun _ => True)`.
- **`mkvalidFC_completeness (FC) (dischargers…) (h_canonFC : FC minCanonicalR) (h_valid : MValidFC FC φ) : Derivable MKModalAxiom φ`**:
  copy `mk_completeness` (MinCompleteness.lean:55) — **single branch, no `efq`, no consistency case
  split** — and thread `h_canonFC` into the `h_valid` application (the one line
  `h_valid (MinCanonicalPrimeWorld Atom) minCanonicalR h_canonFC (min_canonical_f1 …) …`). This is
  a ~2-line diff and is *simpler* than `ivalidFC_completeness` (no inconsistent branch).
- **`min_axiom_mem`** and **`min_imp_property`** helpers (§3.3).

Estimated ~120–160 L. Should land + commit first.

### Phase 2 — `MT.lean` (reflexivity; LOW risk)

`MTModalAxiom` (MK constructors + `tBox`/`tDia`); `mtFC r := ∀ w, r w w`; `mt_axiom_sound`
(inherited MK cases + `tBox`/`tDia`) over `MValidFC mtFC`; `mt_soundness`/`_soundness_derivable`;
`min_canonical_reflexive_mt : mtFC minCanonicalR` (positive, `min_axiom_mem`/`min_imp_property`);
`mt_completeness` = `mkvalidFC_completeness mtFC … min_canonical_reflexive_mt`; `mt_consistent`
(one-point `ℕ`-frame, `mtFC` trivial); `mt_soundness_completeness`. ~200–260 L.

### Phase 3 — `MS4.lean` (reflexivity + transitivity; LOW-MODERATE risk)

`MS4ModalAxiom` (MT constructors + `fourBox`/`fourDia`); `ms4FC`; `ms4_axiom_sound` (`fourBox`
via `f2`, `fourDia` plain); `min_canonical_reflexive`/`min_canonical_transitive` bundled into
`min_canonical_ms4FC` (positive, port of `is4_canonical_*`); `ms4_completeness`; consistency;
biconditional. ~240–300 L.

**Zero-Debt STOP clause (Phase 3):** the transitivity closure `min_canonical_transitive` is a port
of `is4_canonical_transitive` and is expected verbatim. If a clause cannot be closed sorry-free,
do **NOT** insert `sorry`/`axiom`/vacuous `def`; mark the phase **[BLOCKED]**, record the exact
open goal state, and escalate. (Assessed LOW-MODERATE risk — the IK analogue compiles.)

### Phase 4 — `MS5.lean` (equivalence via B; MODERATE risk — the crux)

`MS5ModalAxiom` (MS4 constructors + `bBox`/`bDia`, **B not euclidean**); `ms5FC` (refl ∧ trans ∧
symm); `ms5_axiom_sound` (`bBox` persistence+symmetry, `bDia` plain symmetry); `min_canonical_
symmetric` bundled with refl/trans into `min_canonical_ms5FC` (positive port of
`is5_canonical_symmetric`, IS5.lean:341); `ms5_completeness`; consistency; biconditional.
~260–320 L.

**Zero-Debt STOP clause (Phase 4, HIGHEST risk):** `min_canonical_symmetric` routes `□φ∈v → φ∈w`
back through `minCanonicalR`'s diamond clause via `bDia` — the least obvious chaining. First
attempt the verbatim port of `is5_canonical_symmetric` (replace `canonicalR` two-clause
destructuring, `axiom_mem`→`min_axiom_mem`, `canonical_imp_property`→`min_imp_property`). If it
cannot be closed sorry-free after genuine effort, do **NOT** insert `sorry`/`axiom`/vacuous
placeholder — mark **[BLOCKED]**, record the exact open goal state, and escalate to user review
(candidate escalation: whether MS5 needs a small bespoke `bDia`-membership lemma). Assessed
MODERATE risk, HIGH confidence a positive proof exists (the IK proof is compiled and uses only
deductive closure, which quasi-prime worlds have).

### Phase 5 — Barrel wiring + full CI

`lake exe mk_all --module` to register the new files; then the full CSLib CI order:
`lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
`lake shake --add-public --keep-implied --keep-prefix` → `lake test`. Confine all edits to the
`Minimal/` subtree; the only shared-file touch is `Cslib.lean`. Commit artifacts promptly
(concurrent sessions active).

**Import chain caveat** (from task 501): although the conceptual chain is `MK ← MT ← MS4 ← MS5`,
`lake shake` may flag it if each `*ModalAxiom` copies its predecessor's constructors verbatim
rather than referencing them as terms — in that case import `MinExtension` (+ `MinCompleteness`)
directly, as CK's `CS4`/`CS5` ended up doing. Let `shake` decide; do not pre-optimize.

---

## Deliverable 5 — Reusable lemmas + Mathlib API

**Reuse as-is (all verified present, sorry-free on `main`):**
- MK: `MKModalAxiom`, `mk_axiom_sound`, `mk_soundness`, `mk_soundness_derivable`,
  `MinCanonicalPrimeWorld` (+ `Preorder`, `le_iff`), `minCanonicalVal` (+ upward-closed),
  `minBotForces` (+ upward-closed, `iff_botMem`), `min_head_realization`, `minCanonicalR`,
  `min_canonical_box_witness`, `min_canonical_diamond_witness`, `min_canonical_f1`,
  `min_canonical_f2`, `min_canonical_truth_lemma`, `mk_completeness`.
- Quasi-prime engine: `QuasiPrime` (+ `.closed`, `.disj`), `quasiPrime_univ`
  (`Constructive/Segment.lean`); `quasi_head_realization`, `imp_refuting_theory`,
  `box_refuting_theory`, `dia_refuting_theory` (`Constructive/SegmentLindenbaum.lean`) — pulled in
  transitively via `MinPrimeTheory`/`MinCanonicalModel`, no new imports.
- Semantics: `BForces`, `MValid`, `bforces_persistence`, the `@[simp]` `BForces_*` unfolds
  (`Semantics/Birelational.lean`).

**Structural templates (copy shape, do NOT import):** `Intuitionistic/Extension.lean`
(→ `MinExtension.lean`), `Intuitionistic/{IT,IS4,IS5}.lean` (→ `MT`/`MS4`/`MS5`), IK
`canonical_imp_property` (→ `min_imp_property`), `mk_completeness`/`mk_consistent` (→ FC variants).

**New Mathlib API required: NONE.** Everything is `Set` operations (`Set.Subset.refl/trans`,
`Set.mem_*`), `Preorder` (`le_refl`, `le_trans`), `List.mem_*`, and `Classical.propDecidable` —
all already pulled by the delivered files. Do **NOT** use Mathlib `Reflexive`/`Transitive`/
`Symmetric` (deprecated in the pinned Mathlib); define local `mtFC`/`ms4FC`/`ms5FC` predicates.

---

## Adversarial Self-Verification (H4-style)

1. **"MK extensions inherit the CS4/CS5 blocker" — REFUTED.** The blocker is entirely a property
   of CK's *segment* model (no F1/F2 ⇒ ≤-composed blanket FC; `cmreach` = tail membership fails
   global FC; `diamRefutingSegment` restricted-vs-maximal tension). MK uses IK's *single-world
   two-clause* `minCanonicalR` with F1/F2 (verified MinCanonicalModel.lean:75, MK.lean:175–176).
   None of the three causes applies. Confidence: HIGH (direct source reads of both the MK canonical
   model and the task-501 summary's blocker analysis).
2. **"Frame conditions must be ≤-composed (per the task prompt)" — REFUTED for MK.** The ≤-composed
   form was CK-specific, forced by the *absence* of F1/F2. `MValid` has F1/F2, so plain conditions
   on raw `r` suffice and the ≤-composition is absorbed by F1/F2 in the box-form soundness cases
   (as MK's `idb` already uses `f2`, MK.lean:161; as IK's `is4`/`is5` do). Recommending plain
   predicates. Confidence: HIGH.
3. **"The positive closure needs consistency, so it fails over quasi-prime worlds" — REFUTED.** The
   IK closures (`it_/is4_/is5_canonical_*`, IT.lean:246–252 "no `by_contra`, no negation") use only
   `axiom_mem` + `canonical_imp_property`, both = deductive closure, which quasi-prime worlds have
   via `QuasiPrime.closed` (Segment.lean:68). No consistency, no `efq`. Confidence: HIGH.
4. **"MK completeness needs the consistent/inconsistent split like IK" — REFUTED.**
   `mk_completeness` is already single-branch (MinCompleteness.lean:55, no `by_cases`, no `efq`), so
   `mkvalidFC_completeness` is *simpler* than `ivalidFC_completeness`. Confidence: HIGH.
5. **"Use euclidean-5 for MS5" — REFUTED.** Quasi-prime theories are strictly further from
   negation-complete than prime theories (admit `Set.univ`); the euclidean canonical closure needs
   `mcs_neg_of_not_mem`/double-negation. Use B/symmetry (positive, MP-only). Confidence: HIGH
   (tasks 494 + 501 both concur).
6. **Residual GENUINE RISK (flagged): the `min_canonical_symmetric` port (Phase 4).** It is a
   verbatim analogue of the already-compiled `is5_canonical_symmetric`; risk is that a small
   `bDia`-membership helper is needed. Mitigation: Zero-Debt STOP/[BLOCKED] clause on Phase 4 (and
   Phase 3), never `sorry`/axiom/vacuous-def. Confidence a sorry-free construction exists:
   HIGH; confidence zero bespoke lemmas are needed: MEDIUM-HIGH.

**Reuse Check Protocol:** Foundations (`QuasiPrime.closed`, `minCanonicalR`, witnesses, F1/F2)
checked; typeclass reuse (local FC predicates, NOT deprecated Mathlib `Reflexive`) checked; no new
notation; both `Foundations/Logic/` and `Logics/` searched; classical `Systems/{T,S4,S5}` mirror
pattern noted. **Zero-debt:** no step recommends `sorry`/axiom/vacuous placeholder; every new axiom
is a `DerivationTree`-carried schema; every reused lemma is sorry-free on `main`.

---

## Next Step

`/plan 496` — five phases as above; Phase 1 (`MinExtension.lean` scaffold) and Phase 2 (`MT.lean`)
are near-deterministic and should land + commit first; Phase 4 (`MS5.lean` symmetric closure) is
the crux and carries the explicit Zero-Debt [BLOCKED]-escalation clause. `--hard` is optional; the
literature-faithful, already-compiled IK template makes this lower-risk than task 501 was.
