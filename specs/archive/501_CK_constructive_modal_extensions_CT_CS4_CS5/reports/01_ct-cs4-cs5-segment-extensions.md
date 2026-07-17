# Research Report 01: CK Constructive Modal Extensions CT / CS4 / CS5

- **Task**: 501 — sound and complete axiomatizations of the constructive (CK-based) analogues
  of T / S4 / S5, as modular extensions of CK (task 493) over the Wijesekera-style
  fallible-world semantics, mirroring the IK extension pattern of task 494.
- **Session**: sess_1784044271_09e821_501
- **Task type**: cslib. **Mode**: standard (no `--hard`, no `--lit`).
- **Reference grounding**: task 493 files (verbatim), task 494 files (verbatim), the task-493
  research report (ianshil/CK `general_seg_completeness.v` grounding), the task-494 research
  report (euclidean-vs-symmetry adversarial finding). `Wijesekera1990`, `Simpson1994`,
  `ChagrovZakharyaschev1997` cited via existing module docstrings.

---

## Executive Summary / Verdict

**The task is tractable and zero-debt, but it is NOT a mechanical copy of task 494.** The two
findings that drive the whole design:

1. **CK extensions must reuse the SEGMENT / fallible-world model (task 493's
   `Constructive/` namespace), NOT the birelational prime-theory canonical model (task 494's
   `Intuitionistic/Extension.lean`).** The reason bare CK is incomplete for the birelational
   `BForces` semantics (Cd and Idb are birelationally valid but not CK-derivable) *persists
   verbatim* for CT/CS4/CS5: adding T, 4, or B does not derive Cd or Idb. So the sound-and-
   complete semantics for each extension is `CKForces` (the ∀∃ diamond, no F1/F2 confluence)
   plus the three explosion conditions, restricted to frames whose modal relation `r`
   satisfies the appropriate frame condition. The birelational `IValidFC`/`ivalidFC_completeness`
   scaffold of task 494 is the structural *template*, but not a reusable dependency.

2. **The frame conditions must be stated in "≤-composed" (order-saturated) form, and — the
   primary implementation challenge — the frame condition does NOT hold globally on the raw
   segment world type `CKSegment Axioms`.** The completeness proof applies validity to the
   canonical segment model, so the frame condition must hold for *every* segment of the world
   type. It does not: a segment with a consistent head and tail `{Set.univ}` is well-formed
   yet is not `cmreach`-reflexive. Task 493's report §6 ("reflexivity/transitivity extend
   smoothly … cexpl satisfies them") is correct about `cexpl` but *understates* this global
   obstruction. The resolution is to build each extension's canonical model over a **restricted
   world subtype** carrying the frame condition as an invariant (or, equivalently, over
   FC-saturated tails), and to re-establish the truth lemma there — all constructions used in
   the truth lemma (`CKSegment.ofHead`, `diamRefutingSegment`, `cexpl`) provably satisfy the
   invariants, so the port is mechanical for CT and moderate for CS4/CS5.

The good news, confirmed by reading every file: **the entire segment core is already
`Axioms`-parametric** (`CKSegment Axioms`, `cmreach`, `cval`, `cbotForces`, `ck_truth_lemma`,
`segment_realization`, all Lindenbaum/refuting-theory lemmas), so extensions add constructors +
frame-condition hypotheses without re-deriving the core. `CKForces`/`CKValid` persistence and
explosion lemmas are also reusable unchanged.

Estimated scale: **3–4 new files under `Constructive/`, ~800–1,200 lines, ~6–9 phases**,
comparable to task 494 plus the world-subtype port. Recommend axiomatizing **CS5 via B
(symmetry), NOT the euclidean/5 axiom** — the same adversarial finding task 494 made, and it
propagates with *extra* force here (quasi-prime theories are even further from negation-complete
than prime theories: they admit `Set.univ`).

---

## Deliverable 1 — Task 493's CK Formalization (files, derivation system, semantics, canonical model)

### Files (all under `Cslib/Logics/Modal/Metalogic/Constructive/`, wired into `Cslib.lean:353–357`)

| File | Lines | Content |
|------|-------|---------|
| `Forcing.lean` | 196 | `CKForces` (∀∃ diamond), `@[simp]` unfolds, `ckforces_persistence` (no F1), `CKValid` (3 explosion conditions), `ckforces_of_exploding` |
| `Segment.lean` | 226 | `QuasiPrime`, `boxInv`/`diaInv`, `CKSegment` structure, `cexpl`, `CKSegment.ofHead`, `Preorder (CKSegment)`, `cmreach`/`cval`/`cbotForces`, upward-closure + explosion-condition lemmas |
| `SegmentLindenbaum.lean` | 271 | `quasi_prime_exclusion`, `box_mem_of_boxed_context`, `imp_/box_/dia_refuting_theory`, `segment_realization` |
| `CKTruthLemma.lean` | 211 | `mem_of_axiom`, `mem_head_mp`, `diamRefutingSegment`, `ck_truth_lemma` |
| `CK.lean` | 427 | `CKModalAxiom`, `ck_axiom_sound`/`ck_soundness`/`ck_soundness_derivable`, `ck_completeness`, `ck_consistent`, `ck_soundness_completeness`; secondary `EValid` block (birelational soundness only) |

Namespace throughout: `Cslib.Logic.Modal`. Formula type: `Proposition Atom` (from
`Cslib.Logics.Modal.Basic`), with primitive `box`/`diamond` (◇ is NOT □-definable). Proof
system: `DerivationTree`/`Derivable` with `modalDerivationSystem`, `necessitation` rule
(recurses into empty-context premise), `deductionTheorem`.

### The bare-CK derivation system (`CKModalAxiom`, `CK.lean:104–138`)

11 constructors: 9 intuitionistic-propositional schemata (`implyK`, `implyS`, `efq`, `andI`,
`andE1`, `andE2`, `orI1`, `orI2`, `orE`) + `k` (Kb: `□(φ→ψ)→(□φ→□ψ)`) + `kdia`
(Kd: `□(φ→ψ)→(◇φ→◇ψ)`). **Deliberately absent** (each is a non-theorem and non-`CKValid`):
`cd` (◇(φ∨ψ)→◇φ∨◇ψ), `idb` ((◇φ→□ψ)→□(φ→ψ)), `dbot` (Nd: ◇⊥→⊥).

### The Wijesekera semantics (`CKForces`, `Forcing.lean:67–76`)

Clauses coincide with `BForces` except **diamond is ∀∃**:
`◇φ @ w ⟺ ∀ w' ≥ w, ∃ u, r w' u ∧ φ @ u`. Box is the usual ∀∀: `□φ @ w ⟺ ∀ w' ≥ w, ∀ u, r w' u → φ @ u`.
`imp` absorbs `≤` on the left. Consequences that matter for 501:

- `ckforces_persistence` holds on **arbitrary** frames (no F1) — every modal clause universally
  quantifies over `≤`-successors, so persistence closes by `le_trans` alone (`Forcing.lean:122`).
- `CKValid` (`Forcing.lean:159`) quantifies over: arbitrary `Preorder World`, arbitrary
  `r : World → World → Prop` (**no F1/F2**), upward-closed `val` and `botForces`, and the three
  explosion conditions — `botForces w → val w p`, `botForces w → r w u → botForces u`,
  `botForces w → ∃ u, r w u ∧ botForces u`. `ckforces_of_exploding` (`Forcing.lean:172`) proves
  exploding worlds force everything.

### The canonical segment model

- **World** = `CKSegment Axioms` = `⟨head, tail, head_qprime, tail_qprime, box_reflect,
  diam_witness⟩` (`Segment.lean:115`). `head : Set (Proposition Atom)`; `tail : Set (Set …)`.
  Both head and tail members are `QuasiPrime` (`PrimeAdmissible` at the trivially-true
  consistency predicate — admits `Set.univ`, giving fallible worlds). Fields: box reflection
  `□A ∈ head → ∀ t ∈ tail, A ∈ t`; diamond witness `◇A ∈ head → ∃ t ∈ tail, A ∈ t`.
- `cexpl` (`Segment.lean:131`): `head = tail-member = Set.univ`; forces `⊥` and `◇⊥`.
- `CKSegment.ofHead hH` (`Segment.lean:142`): realizes any quasi-prime `H` as a segment with the
  **maximal tail** `{t | QuasiPrime t ∧ boxInv H ⊆ t}`; diamonds witnessed by `Set.univ ∈ tail`.
- `≤` = head inclusion (`Segment.lean:161`); `cmreach P Q := Q.head ∈ P.tail` (`Segment.lean:173`);
  `cval s p := atom p ∈ s.head`; `cbotForces s := ⊥ ∈ s.head`. The three `CKValid` explosion
  conditions are discharged for this model by `cbotForces_val`/`cbotForces_mreach`/
  `cbotForces_mreach_wit` (`Segment.lean:202–224`).
- **Truth lemma** `ck_truth_lemma` (`CKTruthLemma.lean:133`): `CKForces cmreach cval cbotForces
  s φ ↔ φ ∈ s.head`. Backward `box` case re-tails via `CKSegment.ofHead` (maximal tail) +
  `box_refuting_theory`; backward `diamond` case re-tails via `diamRefutingSegment` (restricted
  tail omitting the witness) + `dia_refuting_theory` (the **only** place `Kd` enters the
  construction). The ∀∃ diamond clause is exactly what licenses the re-tailing.
- `ck_completeness` (`CK.lean:240`): contrapositive — `segment_realization` gives an `ofHead`
  segment `s` omitting an underivable `φ`; `CKValid` forces `φ` at `s` in the canonical model;
  truth lemma converts to `φ ∈ s.head` — contradiction.

**Critical parametricity fact for 501**: every one of `CKSegment`, `cexpl`, `ofHead`, `cmreach`,
`cval`, `cbotForces`, the explosion lemmas, `quasi_prime_exclusion`, `box_mem_of_boxed_context`,
`imp_/box_/dia_refuting_theory`, `quasi_head_realization`, `segment_realization`,
`diamRefutingSegment`, and `ck_truth_lemma` is stated `{Axioms : Proposition Atom → Prop}`-
polymorphically, taking only the *specific* axiom dischargers it needs (never the full CK list).
So CT/CS4/CS5 instantiate them at `CTModalAxiom`/`CS4ModalAxiom`/`CS5ModalAxiom` with **zero**
re-derivation of the core. `Segment.lean`'s own module docstring names this: "parametric over
`Axioms` (so task 501's CT/CS4/CS5 extensions can reuse it)".

---

## Deliverable 2 — How task 494 structured the IK extensions IT/IS4/IS5 (the pattern to mirror)

Files under `Cslib/Logics/Modal/Metalogic/Intuitionistic/`: `Extension.lean` (scaffold),
`IT.lean`, `IS4.lean`, `IS5.lean` (+ reused `IK.lean`, `CanonicalModel.lean`, `TruthLemma.lean`,
`Completeness.lean`, `PrimeTheory.lean`).

### The scaffold (`Extension.lean`)

Three declarations generalize task 480/492's birelational completeness to a restricted frame
class cut out by a frame-condition predicate `FC`:

- `IValidFC (FC) φ` (`Extension.lean:74`): a copy of `IValid` with one extra hypothesis
  `_fc : FC r` threaded alongside the confluence conditions `f1`/`f2`. `IValid` untouched;
  `IValid = IValidFC (fun _ => True)`.
- `ivalidFC_completeness` (`Extension.lean:97`): a ~2-line generalization of `ivalid_completeness`
  taking `h_canonFC : FC (@canonicalR Atom Axioms)` and threading it into the validity
  application. All Lindenbaum/truth-lemma machinery reused verbatim.
- `axiom_mem` (`Extension.lean:181`): `Axioms φ → φ ∈ w.val` for a `CanonicalPrimeWorld` — the
  one-liner every per-extension canonical-closure proof uses.

### The per-system files (uniform 6-part shape)

Each of `IT.lean`/`IS4.lean`/`IS5.lean` is:

1. **Axiom inductive** = the previous system's constructors verbatim + two new schemata (box-form
   AND diamond-form, both required because ◇ is primitive): IT adds `tBox : □A→A`, `tDia : A→◇A`;
   IS4 adds `fourBox : □A→□□A`, `fourDia : ◇◇A→◇A`; IS5 adds `bBox : A→□◇A`, `bDia : ◇□A→A`.
2. **Local frame-condition predicate** `xFC {World} (r) : Prop` (NOT Mathlib's
   `Reflexive`/`Transitive`/`Symmetric`, which are `@[deprecated]` in the pinned Mathlib — using
   them would break the zero-warnings gate). `itFC r := ∀ w, r w w`;
   `is4FC r := (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y)`;
   `is5FC r := reflexive ∧ transitive ∧ (∀ {w x}, r w x → r x w)`.
3. **Soundness** `x_axiom_sound` — the inherited cases verbatim (unused new FC hypotheses threaded
   through), + 2 new cases. Note the new cases use `bforces_persistence`, `f1`/`f2`, and the FC
   parts. (IS4 `fourBox` uses `f2`; IS5 `bBox`/`bDia` use persistence + symmetry.)
   Then `x_soundness` (structural recursion over `DerivationTree`) and `x_soundness_derivable`.
4. **Canonical FC closure** `x_canonical_reflexive`/`_transitive`/`_symmetric` — each discharged
   **positively** (`refine ⟨?_, ?_⟩` over the box/dia clauses of `canonicalR`) via
   `axiom_mem (…) ` + `canonical_imp_property` (MP-closure). No `by_contra`, no negation. Bundled
   into `x_canonical_fc`.
5. **Completeness** = instantiate `ivalidFC_completeness xFC (dischargers…) x_canonical_fc h_valid`.
6. **Consistency** via a trivial one-point frame on `ℕ`; `x_soundness_completeness` biconditional.

### The euclidean-vs-symmetry adversarial finding (task 494 report Deliverable 6)

IS5 is axiomatized via **B (symmetry)**, not the classical euclidean/5 axiom `◇A→□◇A`. The
classical canonical-euclideanness proofs (`canonical_eucl`/`canonical_eucl_from_5`) are
`by_contra` + `mcs_neg_of_not_mem` + double-negation arguments depending on **negation-
completeness of maximal-consistent sets**. Canonical *prime* theories are deliberately NOT
negation-complete, so that route has no intuitionistic analogue. Symmetry closure from B is fully
positive (MP-closure only) and transfers cleanly. Reflexive + transitive + symmetric = equivalence
relation = Simpson's IS5 frame class.

---

## Deliverable 3 — Recommended Lean 4 design for CT / CS4 / CS5

### D3.0 Naming, files, wiring

Namespace `Cslib.Logic.Modal`, files under `Cslib/Logics/Modal/Metalogic/Constructive/`:

- `Constructive/CKExtension.lean` — the segment analogue of `Extension.lean`: `CKValidFC`,
  the restricted world subtype (below), and the parametric `ckvalidFC_completeness`.
- `Constructive/CT.lean`, `Constructive/CS4.lean`, `Constructive/CS5.lean` — one per system,
  each depending on the previous (CT ← CKExtension ← CK; CS4 ← CT; CS5 ← CS4), mirroring the
  `IK ← IT ← IS4 ← IS5` import chain.

Add to `Cslib.lean` via `lake exe mk_all --module`. Every file begins `import Cslib.Init`.
Names lowerCamelCase, no underscores in declaration names (`ct_axiom_sound` uses underscores as
the existing `ck_`/`it_` theorems do — this is the established convention in these files and
passes the current `lake lint`; keep it identical). Prop-valued: use `theorem`/`lemma`. Every
new declaration needs a docstring (docBlame).

### D3.1 Axiom inductives (mirror IT/IS4/IS5 exactly, but extend `CKModalAxiom`, not `IKModalAxiom`)

```lean
/-- Bare `CK` (`k`, `kdia`, 9 int-prop) + the two `T` schemata. -/
inductive CTModalAxiom : Proposition Atom → Prop where
  | implyK … | implyS … | efq … | andI … | andE1 … | andE2 …
  | orI1 … | orI2 … | orE …
  | k (φ ψ) : CTModalAxiom ((□(φ.imp ψ)).imp ((□φ).imp (□ψ)))
  | kdia (φ ψ) : CTModalAxiom ((□(φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  | tBox (φ) : CTModalAxiom ((□φ).imp φ)          -- □A → A
  | tDia (φ) : CTModalAxiom (φ.imp (◇φ))          -- A → ◇A

-- CS4ModalAxiom = CTModalAxiom's constructors + fourBox (□A→□□A), fourDia (◇◇A→◇A)
-- CS5ModalAxiom = CS4ModalAxiom's constructors + bBox (A→□◇A), bDia (◇□A→A)   [B, NOT euclidean 5]
```

**Recommendation (adversarial, carried from task 494 Deliverable 6, reinforced): use B for
CS5.** The euclidean-5 canonical closure needs negation-completeness; quasi-prime theories are
*strictly further* from negation-complete than prime theories (they admit `Set.univ` and impose
no consistency). Symmetry closure on `cmreach` is provable positively (see D3.4). Refl+trans+symm
= equivalence = Simpson's constructive S5 frame class.

### D3.2 Frame conditions — the ≤-COMPOSED ("order-saturated") form (KEY FINDING)

Because `CKValid` frames carry **no F1/F2 confluence**, the frame conditions cannot be the plain
`r`-relations used by IT/IS4/IS5. Deriving each axiom's soundness directly from the `CKForces`
clauses (done by hand below, D3.3) shows that **the box-form axioms require the frame condition in
its ≤-saturated form** (the plain form validates only the diamond-form axiom). Recommended
predicates on the raw relation `r` and preorder `≤`:

```lean
/-- CT frame condition: reflexivity. (tBox and tDia both need only plain `r w w`.) -/
def ctFC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop := ∀ w, r w w

/-- CS4 frame condition: reflexivity + ≤-composed transitivity.
    `fourDia` needs plain transitivity; `fourBox` needs the ≤-composed form
    `r w u → u ≤ u' → r u' t → r w t` (which implies plain transitivity by `u' := u`). -/
def cs4FC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w) ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)

/-- CS5 frame condition: reflexivity + ≤-composed transitivity + ≤-composed symmetry.
    `bDia` needs plain symmetry; `bBox` needs `r w u → u ≤ u' → r u' w`. -/
def cs5FC {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → r u' w)
```

Rationale (each derived directly from the ∀∃ `CKForces` clauses in D3.3):

| Axiom | Diamond-form needs | Box-form needs | Chosen `FC` clause |
|-------|-------------------|----------------|--------------------|
| T | plain `r w w` | plain `r w w` | `∀ w, r w w` |
| 4 | plain transitivity | `r w u → u≤u' → r u' t → r w t` | ≤-composed transitivity |
| B | plain symmetry | `r w u → u≤u' → r u' w` | ≤-composed symmetry |

Because `≤` is reflexive, each ≤-composed clause specializes (`u' := u`) to the plain clause, so
one predicate serves both the box-form and diamond-form soundness cases. This matches the task
statement's phrase "compatible with the ≤-R confluence": in the confluence-free CK setting the
compatibility is folded directly into the frame condition rather than supplied by F1/F2.

Define these locally (do NOT use Mathlib `Reflexive`/`Transitive`/`Symmetric` — deprecated in the
pinned Mathlib, per `IT.lean`'s docstring). Note these predicates need `[Preorder World]` in scope
(they mention `≤`), unlike the IK versions.

### D3.3 Soundness (over `CKForces`, verified by hand from the clauses)

Define `CKValidFC (FC) φ` as `CKValid` (`Forcing.lean:159`) with an extra hypothesis `FC r`
threaded in. The 11 bare-CK cases are `ck_axiom_sound`'s cases verbatim (`CK.lean:149–183`, with
`ckforces_persistence`/`ckforces_of_exploding`, no confluence), FC threaded unused. The new cases
(worked out directly from the `CKForces` clauses — all discharge cleanly):

- **tBox `□A→A`**: `intro w' _ hbox; exact hbox w' (le_refl w') w' (hrefl w')`. Plain reflexivity.
- **tDia `A→◇A`**: `intro w' _ hφ w'' hw''; exact ⟨w'', hrefl w'', ckforces_persistence … hw'' hφ⟩`.
  Plain reflexivity + persistence (∀∃ clause introduces `w'' ≥ w'`).
- **fourDia `◇◇A→◇A`**: from `◇◇A@w'` at `w'' ≥ w'` get `u` with `r w'' u ∧ ◇A@u`; instantiate
  `◇A@u` at `u` (`le_refl`) to get `t` with `r u t ∧ A@t`; witness `t` via **plain** transitivity
  `r w'' u`, `r u t` (`u'=u`).
- **fourBox `□A→□□A`**: the nested box goal introduces `w'' ≥ w'`, `r w'' u`, `u' ≥ u`, `r u' t`;
  need `A@t`; supply it from `□A@w'` at `w''` (`≥ w'`) and `t`, using **≤-composed transitivity**
  `r w'' u → u ≤ u' → r u' t → r w'' t`. (This is where F2 was used in IS4; here the FC absorbs it.)
- **bDia `◇□A→A`**: at `w'` (`le_refl`) get `u` with `r w' u ∧ □A@u`; instantiate `□A@u` at `u`
  (`le_refl`) and `w'` via **plain** symmetry `r w' u → r u w'`; yields `A@w'`.
- **bBox `A→□◇A`**: goal `∀ w'' ≥ w', ∀ u, r w'' u → ◇A@u`; unfold `◇A@u` at `u' ≥ u`; witness
  `w''` via **≤-composed symmetry** `r w'' u → u ≤ u' → r u' w''`, with `A@w''` by persistence from
  `w' ≤ w''`.

Then `ct_soundness`/`cs4_soundness`/`cs5_soundness` (structural recursion over `DerivationTree`,
copy `ck_soundness` `CK.lean:189` threading the FC hypotheses) and `x_soundness_derivable`.

### D3.4 Completeness — the world-subtype construction (PRIMARY CHALLENGE)

**The obstruction.** `ck_completeness` applies `CKValid` to the model `(CKSegment CKModalAxiom,
cmreach, …)`. For an extension, `CKValidFC FC` additionally demands `FC cmreach` — i.e. the frame
condition holds for **every** `P : CKSegment CTModalAxiom`. It does not. Counterexample (well-
formed CT segment): `⟨head, {Set.univ}, …⟩` with a consistent `head ≠ Set.univ`. `box_reflect`
and `diam_witness` hold trivially (only tail member is `Set.univ`), yet
`cmreach P P = (head ∈ {Set.univ}) = False`, so `cmreach` is not globally reflexive. Task 493's
report §6 verified `cmreach cexpl cexpl` (true) but did not address arbitrary segments; **this
global obstruction is the real content of task 501.**

**Recommended resolution: restrict the world type to a subtype carrying the FC as an invariant,**
and re-establish the truth lemma there. For CT:

```lean
/-- CT canonical worlds: segments whose head is a modal successor of itself
    (the T-invariant `cmreach s s`). -/
structure CTSegment where
  seg : CKSegment CTModalAxiom
  refl : seg.head ∈ seg.tail          -- ≡ cmreach seg seg

instance : Preorder CTSegment := Preorder.lift (·.seg)   -- head inclusion, lifted
def ctMreach (P Q : CTSegment) : Prop := cmreach P.seg Q.seg
def ctVal (s : CTSegment) (p) : Prop := cval s.seg p
def ctBot (s : CTSegment) : Prop := cbotForces s.seg
```

`ctFC ctMreach` is then `∀ P, P.seg.head ∈ P.seg.tail`, immediate from the `refl` field. The
truth lemma must be re-proved over `CTSegment`; the key obligations (all discharge because the T
axioms are in scope):

1. **Every constructed segment satisfies `refl`.** For CT, `boxInv H ⊆ H` holds for *every*
   quasi-prime `H` (deductively closed, `tBox`-closed: `□B ∈ H ⇒ (□B→B) ∈ H ⇒ B ∈ H` by MP —
   exactly `mem_head_mp`/`axiom_mem` reasoning). Hence:
   - `CKSegment.ofHead hH`: `H ∈ {t | QuasiPrime t ∧ boxInv H ⊆ t}` since `boxInv H ⊆ H`. ✅
   - `diamRefutingSegment s h_not` (head `= s.head`, tail members omit `A`): `s.head` is in its
     restricted tail because `boxInv s.head ⊆ s.head` (T) **and** `A ∉ s.head` (from `◇A ∉ s.head`
     + `tDia`: `A ∈ s.head ⇒ ◇A ∈ s.head`, contradiction). ✅
   - `cexpl`: `Set.univ ∈ {Set.univ}`. ✅
2. **`ck_truth_lemma` port.** Because `ctMreach`/`ctVal`/`ctBot` are literally `cmreach`/`cval`/
   `cbotForces` on the `.seg` projection, and the truth-lemma constructions stay within
   `CTSegment` by (1), the existing `ck_truth_lemma` proof transfers structurally. Cleanest
   implementation: keep the truth lemma on `CKSegment CTModalAxiom` and note the invariant is only
   needed to supply `FC ctMreach` at the *completeness* application — i.e. build the canonical
   model over `CTSegment` but reuse `ck_truth_lemma` by transporting along `.seg`. (An
   alternative that avoids a new structure: define `CKValidFC` to quantify over models and prove
   `FC` for the *reachable submodel from the realizing `ofHead` segment*; the subtype is cleaner.)

For **CS4**, the invariant is the ≤-composed transitivity of `ctMreach` — a *relational* property
of the tail structure, not a single per-segment field. The `ofHead` maximal tail
`{t | QuasiPrime t ∧ boxInv H ⊆ t}` is transitively closed when `boxInv` is idempotent-upward,
which holds because `fourBox`/`fourDia` are in scope (`□B ∈ H ⇒ □□B ∈ H`, so `boxInv (boxInv H) ⊆
boxInv H`, mirroring `is4_canonical_transitive`'s `hwu.1 ∘ hwv.1`). The `diamRefutingSegment`
restricted tail must be shown transitively compatible as well (moderate risk — see §Risks).

For **CS5**, add the ≤-composed symmetry invariant. Its canonical proof mirrors
`is5_canonical_symmetric` (`IS5.lean:341`): route a box membership back through the diamond clause
via `bDia`, and a value forward through `bBox` — both positive/MP-only, no negation. The segment
adaptation must thread these through `cmreach = tail membership` rather than `canonicalR`'s two
clauses; **this is the highest-risk closure of task 501** (as task 493 §6 and task 494
Deliverable 6 both predicted).

**Then, per system:** a parametric `ckvalidFC_completeness` (segment analogue of
`ivalidFC_completeness`) taking `h_canonFC : FC (canonical extension model)` and the same axiom
dischargers `ck_completeness` already threads (`CK.lean:243–257`), instantiated at each system;
`x_consistent` via the trivial one-point infallible model (copy `ck_consistent` `CK.lean:262`,
which already checks `botForces := fun _ => False` satisfies explosion vacuously — the FC holds
trivially on a one-point reflexive/transitive/symmetric frame); `x_soundness_completeness`
biconditional.

### D3.5 Suggested phase decomposition

1. `CKExtension.lean`: `CKValidFC`, `ctFC`/`cs4FC`/`cs5FC`, parametric `ckvalidFC_completeness`
   skeleton + `axiom_mem`-analogue for segments (`axiom_mem_head : Axioms φ → φ ∈ s.head`).
2. CT axioms + soundness (`ct_axiom_sound` new cases tBox/tDia).
3. CT world subtype + `refl`-invariant discharge for ofHead/diamRefuting/cexpl + truth-lemma
   transport + `ct_completeness`/`ct_consistent`/biconditional.
4. CS4 axioms + soundness (fourBox/fourDia, ≤-composed transitivity).
5. CS4 transitivity invariant + completeness.
6. CS5 axioms + soundness (bBox/bDia, ≤-composed symmetry).
7. CS5 symmetry invariant + completeness. (Highest risk — allow a STOP/[BLOCKED] contingency.)
8. Barrel wiring (`mk_all`), full CI (`lake build`, `checkInitImports`, `lint`, `lint-style`,
   `shake`, `test`).

---

## Deliverable 4 — Reusable lemmas (tasks 493/494) and Mathlib API

### Directly reusable from task 493 (`Constructive/`), unchanged, at extension `Axioms`

- `CKForces`, all `@[simp]` unfolds, `ckforces_persistence` (no F1), `ckforces_of_exploding`,
  `CKValid` (`Forcing.lean`) — soundness scaffolding.
- `QuasiPrime` (+ `.closed`/`.disj`), `quasiPrime_univ`, `mem_of_bot_mem`, `boxInv`/`diaInv`,
  `CKSegment` (structure), `cexpl`, `CKSegment.ofHead` (+ `_head` simp), `Preorder (CKSegment)`,
  `CKSegment.le_iff`, `cmreach`, `cval`, `cbotForces`, `cval_upward_closed`,
  `cbotForces_upward_closed`, `cbotForces_val`/`_mreach`/`_mreach_wit` (`Segment.lean`).
- `quasi_prime_exclusion`, `box_mem_of_boxed_context`, `imp_refuting_theory`,
  `box_refuting_theory`, `dia_refuting_theory`, `quasi_head_realization`, `segment_realization`
  (`SegmentLindenbaum.lean`).
- `mem_of_axiom`, `mem_head_mp`, `diamRefutingSegment` (+ `_head` simp), `ck_truth_lemma`
  (`CKTruthLemma.lean`). The truth lemma takes only `implyK/implyS/orI1/orI2/orE/andI/andE1/
  andE2/k/kdia` dischargers — all available for each extension.
- `CK.lean` proof *shapes* to copy: `ck_axiom_sound` (11 shared cases verbatim), `ck_soundness`,
  `ck_soundness_derivable`, `ck_completeness`, `ck_consistent`, `ck_soundness_completeness`.

### Foundations-level (already used by 493, reuse as-is)

- `modalDerivationSystem`, `modalDeductiveClosure`, `modalDeductiveClosure_closed`,
  `modal_subset_deductive_closure`, `modal_deriv_imp_of_union`, `Metalogic.PrimeAdmissible`,
  `Metalogic.prime_exclusion`, `Metalogic.DeductivelyClosed`, `deductionTheorem`,
  `DerivationTree`/`Derivable`/`.ax`/`.assumption`/`.modus_ponens`/`.necessitation`/`.weakening`.

### Template-only from task 494 (`Intuitionistic/`) — copy structure, NOT dependency

- `Extension.lean` (`IValidFC`, `ivalidFC_completeness`, `axiom_mem`) is the STRUCTURAL blueprint
  for `CKExtension.lean` — but do not import it: it is birelational (`BForces`/`canonicalR`), and
  CK extensions are segment-based.
- `IT.lean`/`IS4.lean`/`IS5.lean` give the 6-part per-system file shape, the box-form+diamond-form
  axiom pairing, the local-FC-predicate convention (avoid deprecated Mathlib `Reflexive` etc.),
  the positive canonical-closure proof style, and the euclidean-vs-B decision. The soundness *new
  cases* differ (BForces→CKForces, F1/F2→≤-composed FC) but the *shape* copies.

### Mathlib API

**No new Mathlib API is required.** Everything is set-theoretic (`Set`, `Set.univ`,
`Set.Subset.refl/trans`, `Set.mem_singleton_iff`, `Set.subset_univ`, `List.mem_cons`) and
`Preorder` (`le_refl`, `le_trans`, `Preorder.lift` for the subtype instance) — all already used
across `Constructive/`. Avoid Mathlib `Reflexive`/`Transitive`/`Symmetric` (deprecated in the
pinned Mathlib; define local FC predicates instead, exactly as IT/IS4/IS5 do).

---

## Risks / Open Questions (for the planner)

1. **[HIGH] CS5 symmetry invariant on `cmreach`.** Porting `is5_canonical_symmetric`'s two
   positive clauses from `canonicalR` (two-clause relation) to `cmreach` (tail membership) is the
   single hardest closure. Recommend a STOP/[BLOCKED] contingency at phase 7 if the tail
   structure does not admit the ≤-composed symmetry positively. Do NOT introduce an axiom or
   `sorry` — mark [BLOCKED] with the exact goal state.
2. **[MEDIUM] CS4/CS5 transitivity/symmetry closure of the `diamRefutingSegment` restricted
   tail.** The maximal `ofHead` tail is straightforwardly FC-closed; the restricted tail
   (omitting a witness `A`) must be shown FC-compatible. If it is not, the truth lemma's
   diamond-backward case may need a frame-condition-aware refuting segment (extra construction).
3. **[MEDIUM] Truth-lemma transport to the world subtype.** Cleanest is to keep `ck_truth_lemma`
   on `CKSegment` and only wrap the *completeness* application over the subtype; verify the
   `Preorder.lift` instance's `≤` agrees definitionally with head inclusion so no rewrite friction
   arises.
4. **[LOW] Notation.** These files use `□`/`◇` and no operational-semantics arrows; the Option
   A/B/C notation question does not arise. Follow existing `Constructive/` docstring density and
   `@[expose] public section` conventions.
5. **[LOW] The task title says "euclidean R".** Recommend implementing CS5 via **B/symmetry**
   (equivalence frame class) per the task-494 finding; if a reviewer insists on the euclidean
   axiom, document that its canonical closure requires negation-completeness unavailable to
   quasi-prime theories, and that symmetry yields the same logic (both give Simpson's constructive
   S5 equivalence-frame class).

---

## Zero-Debt / Constraints Compliance

No `sorry`, no new axioms, no vacuous definitions recommended. Where a closure may not go through
(CS5 symmetry, CS4/CS5 restricted-tail closure), the recommendation is an explicit [BLOCKED]
marker with goal state, never deferral. Reuse-first honored: the entire `Axioms`-parametric
segment core is reused; new work is confined to axiom constructors, soundness new cases, the
frame-condition predicates, and the world-subtype completeness port.
