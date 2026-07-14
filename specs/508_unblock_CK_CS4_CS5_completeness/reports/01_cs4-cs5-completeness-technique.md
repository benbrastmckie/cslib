# Research Report: Unblocking CK Constructive CS4/CS5 Completeness

- **Task**: 508 — unblock_CK_CS4_CS5_completeness (follow-up to 501)
- **Date**: 2026-07-14
- **Session**: sess_1784061933_322282
- **Status**: Researched — **CS4 solved and mechanically verified**; **CS5 blocked on a newly
  mechanized obstruction** (different from 501's, and located precisely)

## Executive Summary

Task 501's obstruction is **real and confirmed** — but it is an obstruction to `cs4FC`
*as currently defined*, **not** to CS4 completeness. 501 treated the frame condition as fixed
and searched for a world type satisfying it. That search cannot succeed (proof in §2). The
frame condition is, however, a **free parameter**: any `FC` works provided it (a) still validates
the axioms in *all* models and (b) holds in the canonical model.

Replacing `cs4FC` with a weaker `cs4FC'`, **and** replacing `diamRefutingSegment`'s one-step
`A`-exclusion with a **hereditary `◇A`-exclusion**, closes CS4 completeness. This is not a
sketch: `cs4_soundness_completeness` for CS4 is **fully proved, zero `sorry`, zero new axioms**,
in `probes/cs4-completeness-verified.lean` (compiles clean; `#print axioms` → `[propext,
Classical.choice, Quot.sound]` only). The implementation task is essentially transcription.

CS5 does **not** follow. I mechanized a two-world countermodel proving `bDia` (`◇□A → A`) is
**not sound** over the natural CS5 analogue of the working CS4 condition, and showed the
frame condition that *would* validate `bDia` fails in the canonical model. CS5 needs a further
idea; §5 identifies exactly what and gives the one promising lead (also new: **CS5 ⊢ ◇⊥ → ⊥**,
mechanized).

**Recommendation**: Split the task. Implement CS4 now (low risk, code exists). Re-scope CS5 as a
separate research task; do not attempt it in the same phase.

## 1. Verification of the 501 Obstruction

501's core claim is correct and I reproduce its reasoning rather than re-derive it:

- `cs4FC`'s clause `r w u → u ≤ u' → r u' t → r w t` is a **blanket** hypothesis of
  `CKValidFC`/`ckvalidFC_completeness`, holding on the *whole* world type.
- The truth lemma's diamond-backward case needs a **restricted-tail** witness. An unrestricted
  tail contains `Set.univ`, which forces every diamond and collapses completeness.
- `diamRefutingSegment`'s `A ∉ t` is a one-step property that does not propagate.

501 concluded these are "in direct tension". They are — **given `cs4FC`**. §2 sharpens this into
a proof, which matters because it shows *no* amount of cleverness in the world type helps, and
therefore where the real degree of freedom lies.

## 2. Why No World Type Can Satisfy `cs4FC` (sharpening 501)

This is a short argument 501 did not state in this form, and it is what redirects the search.

1. Any segment `e` with `⊥ ∈ e.head` has `e.head = Set.univ` (deductive closure + `efq`).
2. `box_reflect` then forces **every** `t ∈ e.tail` to contain every formula, so `t = Set.univ`;
   `diam_witness` forces `e.tail` nonempty. Hence the exploding segment is **unique**: `cexpl`,
   with `tail = {Set.univ}`.
3. `cexpl` is unavoidable in the world type: `bf_r_wit` demands an exploding successor of an
   exploding world, and `ofHead`'s `diam_witness` produces `Set.univ` tail members.
4. `≤` is head inclusion, so **`u ≤ cexpl` for every world `u`**.
5. Instantiate `cs4FC` at `u' := cexpl`, `t := cexpl`: for any `w` with *any* realized tail
   member `u`, `cs4FC` forces `Set.univ ∈ w.tail`.

**Conclusion**: `cs4FC` forces every world with a nonempty realized tail to contain `Set.univ` in
its tail — i.e. to be diamond-degenerate. This is exactly the property the truth lemma's
diamond-backward case must violate. **`cs4FC` is unsatisfiable together with the truth lemma on
any world type.** 501's hunt for a "maximal-tail invariant" was therefore searching a provably
empty space; the `Set.univ` counterexample 501 found for `diamRefutingSegment` is an instance of
this general fact, not an artifact of that particular construction.

The degree of freedom 501 did not use: **`FC` itself**.

## 3. Recommended Technique for CS4 (verified)

Two independent changes; both are required.

### 3.1 Change 1 — weaken the frame condition

```lean
def cs4FC' {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)                                                        -- reflexivity (as before)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)    -- for `fourBox`
    ∧ (∀ {w u}, r w u → ∃ u', u ≤ u' ∧ ∀ t, r u' t → r w t)           -- for `fourDia`
```

Why each is still **sound** (this is the half that could have failed, and does not):

- **`fourBox`** (`□A → □□A`): the goal `A@t` is discharged from `□A@w'` at the *re-based* world
  `v ≥ w''`, since `□A@w'` quantifies over all `z ≥ w'`. Conclusion `r v t` instead of `r w'' t`
  is enough. This is where `cs4FC`'s strength was being wasted.
- **`fourDia`** (`◇◇A → ◇A`): the goal `∃ v, r w'' v ∧ A@v` genuinely needs an `r`-successor of
  `w''` itself — persistence cannot rescue it (I checked: a `t ≤ v` variant fails canonically).
  But `◇A@u` may be unfolded at **any** `u' ≥ u`, so the FC supplies a *good* `u'` whose entire
  successor set is already reachable from `w''`.

`cs4FC → cs4FC'` (take `v := w`, `u' := u`), so `cs4FC'` is a genuine weakening: validity over
`cs4FC'` is a **stronger** statement, making soundness harder and completeness easier — exactly
the right direction. Soundness of **all 15 `CS4ModalAxiom` constructors** over `cs4FC'` is proved
in the probe (`cs4_axiom_sound'`).

### 3.2 Change 2 — hereditary `◇A`-exclusion (the key idea)

`diamRefutingSegment` excludes `A` from tail members. `A ∉ t` does not propagate. **`◇A ∉ t`
does.** Both directions work only because of the CS4 axioms:

- **Constructible**: the witness tail needs `dia_refuting_theory` to exclude `◇A`, which requires
  `◇◇A ∉ H`. `fourDia` (`◇◇A → ◇A`) gives exactly this by contraposition from `◇A ∉ H`.
- **Still refutes `◇A`**: the truth lemma gets `Q` with `◇A ∉ Q.head` and `A ∈ Q.head`; `tDia`
  (`A → ◇A`) closes the contradiction.
- **Hereditary**: `◇A ∉ u.head` is precisely the hypothesis needed to re-run the construction at
  `u.head`. This is what fails for `A ∉ u.head`.

`dia_refuting_theory` is reused **unchanged** — instantiated at `A := ◇A₀`. No new Lindenbaum
machinery. 501 predicted "new Lindenbaum-style machinery beyond `SegmentLindenbaum.lean`" would
be needed; it is not.

### 3.3 Definitions (all verified)

```lean
/-- Tail determined by head `H` and an optional excluded diamond `E`. -/
def cs4Tail (H : Set (Proposition Atom)) (E : Option (Proposition Atom)) :
    Set (Set (Proposition Atom)) :=
  {t | QuasiPrime CS4ModalAxiom t ∧ boxInv H ⊆ t ∧ ∀ A, E = some A → (◇A) ∉ t}

/-- Segment at head `H` excluding diamond `E`. `E = none` recovers `ofHead`'s maximal tail. -/
def cs4Seg {H : Set (Proposition Atom)} (hH : QuasiPrime CS4ModalAxiom H)
    (E : Option (Proposition Atom)) (hE : ∀ A, E = some A → (◇A) ∉ H) :
    CKSegment (@CS4ModalAxiom Atom)

/-- CS4 canonical worlds. Note `excl` is DATA, not an existential — this keeps
    `tail_eq` usable by `rw` and avoids unpacking in every FC proof. -/
structure CS4Segment (Atom : Type u) where
  seg : CKSegment (@CS4ModalAxiom Atom)
  excl : Option (Proposition Atom)
  excl_head : ∀ A, excl = some A → (◇A) ∉ seg.head
  tail_eq : seg.tail = cs4Tail seg.head excl

instance : Preorder (CS4Segment Atom) := Preorder.lift (fun s : CS4Segment Atom => s.seg)
```

Note the invariant is *shape*, not the frame condition. Unlike `CTSegment`'s `refl` field,
reflexivity is **derived**: `head ∈ tail` needs `boxInv H ⊆ H` (`tBox`) and `∀A ∈ excl, ◇A ∉ head`
— which is `excl_head`. The T-invariant comes for free, so `CS4Segment` does not need it.

### 3.4 Key lemmas (all proved in the probe)

| Lemma | Statement | Depends on |
|---|---|---|
| `cs4_box_four` | `□B ∈ H → □□B ∈ H` | `fourBox` |
| `cs4_not_dia_dia` | `◇A ∉ H → ◇◇A ∉ H` | `fourDia` — **the hereditary step** |
| `cs4_dia_of_mem` | `A ∈ H → ◇A ∈ H` | `tDia` |
| `cs4_boxInv_subset` | `boxInv H ⊆ H` | `tBox` |
| `cs4_boxInv_trans` | `boxInv H ⊆ K → boxInv K ⊆ t → boxInv H ⊆ t` | `cs4_box_four` |
| `cs4_refl` / `cs4_fc4` / `cs4_fcdia` | the three `cs4FC'` conjuncts, canonically | above |
| `cs4FC'_cs4Mreach` | `cs4FC' (@cs4Mreach Atom)` | above |
| `cs4_axiom_sound'` | all 15 axioms valid over `cs4FC'` | — |
| `cs4_truth_lemma` | `CKForces … s φ ↔ φ ∈ s.seg.head` | above |
| `cs4_completeness` | `CKValidFC cs4FC' φ → Derivable CS4ModalAxiom φ` | above |
| `cs4_soundness_completeness` | `Derivable CS4ModalAxiom φ ↔ CKValidFC cs4FC' φ` | above |

`cs4_boxInv_trans` is the workhorse: it is the axiom-4 argument
`□B ∈ H → □□B ∈ H → □B ∈ boxInv H ⊆ K → B ∈ boxInv K ⊆ t`, and it discharges the `boxInv`
obligation in **both** non-trivial FC conjuncts.

**Verification**: `specs/508_unblock_CK_CS4_CS5_completeness/probes/cs4-completeness-verified.lean`
compiles with zero errors, zero `sorry`, zero new axioms, zero vacuous definitions.
`#print axioms cs4_completeness` → `[propext, Classical.choice, Quot.sound]`.

## 4. Evaluation of the Task's Candidate Approaches

| Approach | Verdict |
|---|---|
| **(a) hereditary/maximal diamond-refuting construction** | **Correct, and now verified** — but *only* in the hereditary (`◇A`-exclusion) form, and *only* combined with weakening `FC`. The "maximal" variant is impossible (§2). 501 scoped this as "research-scale"; it is ~200 lines reusing `dia_refuting_theory` as-is. |
| **(b) filtration over the CK segment model** | **Rejected — wrong tool.** Filtration collapses a model to a *finite* one; it addresses FMP/decidability, not the tail-restriction tension, which is orthogonal to model size. Nothing in the obstruction is about cardinality. CSLib's only filtration infrastructure (`Cslib.Logic.Bimodal.Metalogic.Decidability.FMP.filtration_*`, `Cslib/Logics/Bimodal/Metalogic/Decidability/FMP/TruthPreservation.lean`) is for the **classical bimodal** FMP over a different world type — not reusable, and not needed. |
| **(c) Zorn/Lindenbaum maximalization of the tail-exclusion set** | **Rejected — provably impossible.** Excluding *all* refuted diamonds simultaneously breaks `diam_witness`: take `◇(p∨q) ∈ H`, `◇p ∉ H`, `◇q ∉ H` (consistent in CK — `◇(p∨q) → ◇p ∨ ◇q` is not derivable). A witness `t ∋ p∨q` is quasi-prime, so `p ∈ t` or `q ∈ t`; both are excluded. Contradiction. This is precisely why the `∀∃` diamond clause and per-`A` tails exist. No Zorn variant helps. |
| **(d) [new] weaken `FC` + hereditary `◇A`-exclusion** | **Recommended. Verified.** |

## 5. CS5: Blocked, with the Obstruction Newly Located

CS5 does **not** inherit the CS4 fix. Findings, in order of confidence:

### 5.1 `bBox` is fine

The weakened symmetry `FCsym_box : r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t` validates `bBox`
(`A → □◇A`) by persistence. I have a paper proof that it holds canonically via `bBox` + `4` +
`Kd`: if `w.head, boxInv(u'.head) ⊢ ◇A'`, take `C := ⋀Γ ∈ w.head`; `bBox` puts `◇C` in
`boxInv(w.head) ⊆ u.head ⊆ u'.head`; `box_mem_of_boxed_context` gives `□(C → ◇A') ∈ u'.head`;
`Kd` gives `◇◇A' ∈ u'.head`; `fourDia` gives `◇A' ∈ u'.head`, contradicting `◇A' ∉ u'.head`.
**Not mechanized** — it needs new list-splitting + finite-conjunction machinery (the existing
`modal_deriv_imp_of_union` only splits off a *singleton*, not an infinite second set).

### 5.2 `bDia` is the blocker — **mechanized negative result**

`bDia` (`◇□A → A`) must conclude `A@w'`. Forcing at `w'` is only obtainable by persistence from
some `t ≤ w'`, so any adequate FC must produce a `t ≤ w'` with `r u' t` — call it
`FCbdia : r w u → ∃ u', u ≤ u' ∧ ∃ t, r u' t ∧ t ≤ w`.

**Two mechanized facts** (`probes/cs5-obstruction-verified.lean`, compiles clean):

1. `bDia_not_valid_over_cs5FCweak` — a two-world countermodel (`Bool`; `false` consistent, `true`
   exploding) satisfying reflexivity + both `cs4FC'` clauses + `FCsym_box`, in which `◇□p → p`
   **fails**. So the naive CS4-technique extension is **unsound** for CS5; `FCsym_box` is not
   enough and no amount of canonical-model work fixes it.
2. `cs5_dia_bot_imp_bot` — **CS5 ⊢ ◇⊥ → ⊥** (via `efq`, necessitation, `Kd`, `bDia` at `⊥`).
   CK/CT/CS4 do **not** prove this. This is new information about the system.

**Why `FCbdia` fails canonically**: take `w := ofHead(H)` with `H` consistent and `u := cexpl`
(`Set.univ ∈ w.tail`). Any `u' ≥ cexpl` has head `Set.univ`, so `u'.tail = {Set.univ}`, forcing
`t = cexpl`; then `t ≤ w` means `Set.univ ⊆ H` — false. So `FCbdia` fails at every consistent
world whose tail contains `Set.univ`.

### 5.3 The one lead

Fact (2) is the escape hatch: because CS5 ⊢ `◇⊥ → ⊥`, no *consistent* CS5 head contains `◇⊥`, so
the CS5 canonical model can plausibly be built with **`Set.univ`-free tails** for consistent
heads (exclude `⊥`; note `◇A`-exclusion already implies `⊥`-exclusion, since `⊥ ∈ t → t = univ ∋
◇A`, and `⊥`-exclusion is free for `box_refuting_theory` because `A ∉ T → ⊥ ∉ T`). That removes
the §5.2 counterexample's `u := cexpl`. It does **not** finish the job: `FCbdia` then still
requires `boxInv(u.head) ⊆ w.head` — genuine canonical symmetry — whose classical proof needs
`B ∉ w.head ⇒ ¬B ∈ w.head` (maximality), **unavailable** for quasi-prime (intuitionistic) heads.
This is the known-hard core of constructive S5 canonical completeness.

**Honest verdict on CS5**: not achievable by an extension of the CS4 technique. It requires
either a new canonical-symmetry argument for prime (non-maximal) theories, or a change to the
CK model itself. It should **not** be attempted as part of the CS4 implementation.

## 6. Reuse Check (CSLib/Mathlib)

Reuse-first: **no new foundational abstraction is needed**. Every name below is verified — the
strongest available check, since the probe *compiles against them*.

| Name | Location | Use |
|---|---|---|
| `Cslib.Logic.Metalogic.prime_exclusion` | `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean:226` | via `quasi_prime_exclusion` |
| `quasi_prime_exclusion` | `Constructive/SegmentLindenbaum.lean:64` | Lindenbaum |
| `dia_refuting_theory` | `Constructive/SegmentLindenbaum.lean:194` | **reused unchanged at `A := ◇A₀`** |
| `box_refuting_theory` / `imp_refuting_theory` | `Constructive/SegmentLindenbaum.lean:168` / `:142` | truth lemma |
| `quasi_head_realization` | `Constructive/SegmentLindenbaum.lean:242` | `realize` |
| `ckvalidFC_completeness` | `Constructive/CKExtension.lean:156` | already abstract over `World` — **no change needed** |
| `axiom_mem_head` | `Constructive/CKExtension.lean:186` | axiom→head |
| `mem_head_mp` / `mem_of_axiom` | `Constructive/CKTruthLemma.lean:64` / `:57` | closure |
| `CKSegment`, `cmreach`, `cval`, `cbotForces`, `quasiPrime_univ`, `boxInv` | `Constructive/Segment.lean` | model |
| `cbotForces_val` / `_mreach` / `_mreach_wit`, `cval_upward_closed` | `Constructive/Segment.lean` | explosion — reused as-is |
| `ckforces_persistence`, `ckforces_of_exploding` | `Constructive/Forcing.lean` | soundness |
| `deductionTheorem` | `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean:64` | CS5 probe only |
| `Preorder.lift` | Mathlib `Mathlib/Order/Basic.lean` | subtype preorder |

**Not applicable**: Zorn variants (§4c — impossible, not missing); Mathlib filtration
(`MeasureTheory.filtrationOfSet` etc. — unrelated); `Cslib.Logic.Bimodal.…FMP.filtration_*`
(§4b — wrong world type and wrong problem).

**501 assets preserved**: `CKExtension.lean` needs **no** change; `CS4.lean`'s axioms and the
whole soundness section are reused (only `cs4FC` → `cs4FC'` in the statements). `CT.lean`,
`CK.lean`, `Segment.lean`, `SegmentLindenbaum.lean`, `CKTruthLemma.lean` are untouched.

## 7. Recommendation

1. **Implement CS4 now.** Lift `probes/cs4-completeness-verified.lean` into
   `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean`. Work needed: docstrings (docBlame),
   `cs4FC'` relocated to `CKExtension.lean` beside `ctFC`/`cs4FC`, module-docstring rewrite
   replacing the blocker note, `lake lint`/`lint-style`/`shake` pass. **Risk: low** — the maths
   is verified; the remaining work is CSLib house style.
2. **Decide on `cs4FC` vs `cs4FC'` naming.** `cs4FC` is currently public and used only by
   `cs4_soundness*`. Options: (i) replace it (cleanest; nothing downstream depends on it, and
   §2 shows it cuts out an empty frame class for canonical purposes), or (ii) keep both and
   prove `cs4FC → cs4FC'`. Recommend (i), with `cs5FC` left alone.
3. **Re-scope CS5 as a separate research task.** Deliverables for it: the §5.1 conjunction/
   splitting machinery, the `Set.univ`-free tail redesign enabled by `cs5_dia_bot_imp_bot`, and
   the open canonical-symmetry problem for prime theories. Flag as genuinely open.
4. **Do not** mark CS5 achievable in the CS4 plan. §5.2 is a mechanized *negative* result.

## 8. Zero-Debt Compliance

No `sorry`, no new axioms, no vacuous definitions are proposed anywhere. The CS4 recommendation
is not a plan to *attempt* a proof — the proof exists and compiles. The CS5 recommendation is to
**not** implement rather than to defer with placeholders, per the escalation protocol.

## References

- `specs/501_CK_constructive_modal_extensions_CT_CS4_CS5/summaries/01_ct-cs4-cs5-extensions-summary.md`
- ianshil/CK, `Completeness_seg/general_seg_completeness.v`
- [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990] — fallible worlds, `∀∃` diamond
- [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Ch. 3 — birelational `IS4`/`IS5` frame classes (the `≤`-composed conditions `cs4FC`/`cs5FC`
  mirror these; §2 shows why the segment model cannot take them literally)

## Artifacts

- `specs/508_unblock_CK_CS4_CS5_completeness/probes/cs4-completeness-verified.lean` — complete,
  compiling CS4 soundness+completeness. **This is the implementation.**
- `specs/508_unblock_CK_CS4_CS5_completeness/probes/cs5-obstruction-verified.lean` — mechanized
  `bDia` countermodel + `CS5 ⊢ ◇⊥ → ⊥`.

Reproduce: `lake env lean specs/508_unblock_CK_CS4_CS5_completeness/probes/<file>.lean`
