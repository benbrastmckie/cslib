# Research Report: CK Constructive CS5 Completeness — the Symmetric-Tail Construction

- **Task**: 509 — rescope_CK_CS5_constructive_completeness (owns CS5 completeness for the CK column)
- **Date**: 2026-07-14
- **Session**: sess_1784065982_0f4e12
- **Status**: Researched — **task 508's negative verdict is refuted (mechanized)**; a concrete
  construction path is established, with one genuinely new step precisely located and its naive
  route mechanically ruled out.

## Executive Summary

**Task 508's CS5 obstruction is not real.** Its countermodel `bDia_not_valid_over_cs5FCweak` is
sound, but `cs5FCweak` is the wrong candidate frame condition: it contains only the *weakened*
symmetry `FCsym_box` and **never plain symmetry** `r w u → r u w`. The countermodel relation
`wr` is in fact **not symmetric** (`wr false true` holds, `wr true false` does not —
mechanized as `wr'_not_symm`). So the countermodel says nothing about a frame condition that
retains plain symmetry, and 508's inference "no amount of canonical-model work can fix this" does
not apply.

Restoring the two plain clauses 508 dropped gives `cs5FC''`:

```lean
def cs5FC'' {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)                                                     -- refl      (tBox, tDia)
    ∧ (∀ {w u t}, r w u → r u t → r w t)                           -- plain trans  (fourDia)
    ∧ (∀ {w u}, r w u → r u w)                                     -- plain symm   (bDia)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t) -- cs4FC' clause (fourBox)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)           -- FCsym_box    (bBox)
```

**All 17 CS5 axioms are sound over `cs5FC''`** — `cs5_axiom_sound''`, fully proved, **zero
`sorry`, zero axioms whatsoever** (`#print axioms` → *does not depend on any axioms*). This is
exactly the half 508 declared impossible. `cs5FC → cs5FC''` (`cs5FC_implies_cs5FC''`), so it is a
genuine weakening: validity over `cs5FC''` is *stronger*, making completeness easier — the same
direction that made CS4 work.

On the canonical side, the correct world type is the **symmetric tail**

```lean
def cs5Tail (H : Set (Proposition Atom)) : Set (Set (Proposition Atom)) :=
  {t | QuasiPrime CS5ModalAxiom t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}
```

and this is **not a design choice — it is forced**: `fcbdia_forces_symmetry` (mechanized) shows
that on *any* segment-based world type, any frame condition adequate for `bDia` implies
`boxInv u.head ⊆ w.head` whenever `r w u`. 508 read this implication as the obstruction; it is
in fact the specification. With it: symmetry is free (§3.1), reflexivity comes from `T`,
transitivity from `4`, and `Set.univ`-free tails for consistent heads are **automatic** (§3.2) —
no appeal to `cs5_dia_bot_imp_bot` is needed, and 508's canonical failure of `FCbdia` at
`u := cexpl` evaporates.

Two further findings redirect the work:

- **`prime_set_exclusion` already exists** (`Foundations/Logic/Metalogic/PrimeExclusion.lean:558`,
  built for task 480): Lindenbaum against an entire *set* `E`, with precondition `DerivExcludes`
  ("no finite disjunction of `E` is derivable"). 501 predicted new Lindenbaum machinery would be
  needed and 508 repeated that it was not; both were looking at the single-formula lemma. The
  set version is the machinery this construction needs, and it is already in the library.
- **508 §4(c)'s rejection of simultaneous exclusion does not apply.** It rejected it because
  `◇(A ∨ B) → ◇A ∨ ◇B` is underivable in CK. True, but irrelevant: the exclusion set here is a
  set of **boxes**, `E := {□B | B ∉ H}`, and `⊢ (□B ∨ □B') → □(B ∨ B')` **is** derivable
  (`or_box_imp_box_or`, pure CK). Chained with `Kd` and `bDia` this gives
  `⊢ ◇(□B ∨ □B') → (B ∨ B')` (`dia_or_box_imp_or`), which collapses every n-ary `DerivExcludes`
  obligation to primality of `H`. Both mechanized.

**The one remaining gap is not `bDia` — it is the truth lemma's box-backward case**, and the
naive route to it is mechanically ruled out (§4). Verdict and recommendation in §6.

## 1. What 508 Got Right, and the Single Line Where It Went Wrong

508's positive results stand and are reused: `cs4FC'`-style weakening is the right move, the
frame condition is the free parameter (not the tail), and `CS4` completeness is closed. Its CS5
reasoning has one defect, in the definition of the candidate:

```lean
-- task 508, probes/cs5-obstruction-verified.lean
def cs5FCweak {World : Type*} [Preorder World] (r : World → World → Prop) : Prop :=
  (∀ w, r w w)
    ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t)
    ∧ (∀ {w u}, r w u → ∃ u', u ≤ u' ∧ ∀ t, r u' t → r w t)
    ∧ (∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t)     -- FCsym_box: the ONLY symmetry
```

`cs5FCweak` is `cs4FC'` (three clauses) plus `FCsym_box`. `FCsym_box` is the clause that
validates **`bBox`**. The clause that validates **`bDia`** is *plain symmetry* — and it is
simply absent. 508's own `CS5.lean` proof of `bDia` uses `hsymm hru (le_refl u)`, i.e. the
`u' := u` specialization of `cs5FC`'s symmetry, which `FCsym_box` does not deliver
(`FCsym_box` concludes `∃ t, r u' t ∧ w ≤ t`, never `r u' w`).

So `bDia_not_valid_over_cs5FCweak` shows only that `bBox`'s frame clause does not incidentally
imply `bDia`'s. Mechanized confirmation that the countermodel is outside the intended class:

```lean
theorem wr'_not_symm : ¬ (∀ {a b : Bool}, wr' a b → wr' b a)
```

508 then generalized this into "this is a *soundness* failure of the weakened frame condition,
which no amount of canonical-model work on the completeness side can fix" and propagated it into
`CS5.lean`'s module docstring. That sentence is false for `cs5FC''`, and the docstring must be
corrected (§6, item 4).

## 2. Soundness over `cs5FC''` (verified)

`cs5_axiom_sound''` proves `CKValidFC cs5FC'' φ` for every `CS5ModalAxiom φ` — all 17
constructors. It is `cs5_axiom_sound`'s proof with four cases changed:

| Axiom | `cs5FC` clause used | `cs5FC''` replacement |
|---|---|---|
| `fourDia` (`◇◇A → ◇A`) | `htrans hru (le_refl u) hut` | plain transitivity `htrans hru hut` |
| `fourBox` (`□A → □□A`) | `htrans hru hu' hrt` (≤-composed) | `hfour hru hu' hrt` → `⟨v, hwv, hrvt⟩`; discharge `□A` at the re-based `v` (the CS4 trick) |
| `bDia` (`◇□A → A`) | `hsymm hru (le_refl u)` | plain symmetry `hsymm hru` |
| `bBox` (`A → □◇A`) | `hsymm hru hu'` (≤-composed) | `hsymbox hru hu'` → `⟨t, hru't, hw''t⟩`; `A@t` by persistence from `A@w'` |

The remaining 13 cases are verbatim. `#print axioms cs5_axiom_sound''` reports **no axiom
dependencies at all** (not even `propext`/`Classical.choice`).

## 3. The Canonical Model: the Symmetric Tail

### 3.1 Symmetry is forced, then free

```lean
theorem fcbdia_forces_symmetry {Axioms} {w u : CKSegment Axioms} (hru : cmreach w u)
    (hfc : ∀ {w u : CKSegment Axioms}, cmreach w u →
      ∃ u', u ≤ u' ∧ ∃ t, cmreach u' t ∧ t ≤ w) :
    boxInv u.head ⊆ w.head
```

`FCbdia` is the minimal requirement for `bDia`: `◇□A → A` must conclude `A@w'`, and forcing at
`w'` is obtainable only by persistence from some `t ≤ w'`. The proof is three lines: `box_reflect`
gives `boxInv u'.head ⊆ t.head`, and `t ≤ w` gives `t.head ⊆ w.head`. Since `u ≤ u'` only
*enlarges* `boxInv u'.head`, the choice `u' := u` is optimal and there is no freedom — **every**
adequate CS5 tail satisfies `t ∈ w.tail → boxInv t ⊆ w.head`. Combined with `box_reflect`'s
`boxInv H ⊆ t`, the tail must be a subset of `cs5Tail H`. Taking it to be exactly `cs5Tail H`
makes `r` symmetric *definitionally*:

`r w u ↔ u.head ∈ w.tail ↔ QuasiPrime u.head ∧ boxInv w.head ⊆ u.head ∧ boxInv u.head ⊆ w.head`

which is visibly symmetric in `(w.head, u.head)` — and `r u w` unfolds to the same conjunction
because `u` carries the same `tail_eq` invariant.

### 3.2 `Set.univ`-free tails are automatic

`boxInv Set.univ = Set.univ`, so `Set.univ ∈ cs5Tail H` forces `H = Set.univ`. Hence **for every
consistent head, the symmetric tail contains no exploding member** — with no appeal to
`cs5_dia_bot_imp_bot`, which 508 nominated as "the one lead". 508's canonical refutation of
`FCbdia` (take `w := ofHead(H)` consistent and `u := cexpl ∈ w.tail`) is thereby void: `cexpl`
is not in a consistent head's tail. The `cexpl` world survives with `cs5Tail Set.univ = {Set.univ}`,
exactly as before.

`cs5_dia_bot_imp_bot` is still true and still worth keeping as a CS5 fact, but it is **not** on
the critical path.

### 3.3 What each frame clause needs canonically

Writing `r w u ↔ boxInv w ⊆ u ∧ boxInv u ⊆ w` (heads elided):

| Clause | Canonical proof | Status |
|---|---|---|
| refl `r w w` | `boxInv H ⊆ H` — `tBox` | routine |
| plain symm | definitional (§3.1) | **free** |
| plain trans | `□B ∈ w →(4) □□B ∈ w → □B ∈ u → B ∈ t`; and `□B ∈ t →(4) □□B ∈ t → □B ∈ u → B ∈ w` | routine, uses `4` **twice** |
| `FC4'` (`fourBox`) | `prime_set_exclusion` (§3.4) | new work |
| `FCsym_box` (`bBox`) | `prime_set_exclusion` (§3.4) | new work |
| `diam_witness` | `prime_set_exclusion` (§3.4) | new work |

Note that `r` becomes a genuine **equivalence relation** on CS5 segments — reflexive, symmetric,
transitive — which is Simpson's constructive S5 frame class, as `CS5.lean`'s docstring already
anticipated.

### 3.4 The `prime_set_exclusion` pattern

`Cslib.Logic.Metalogic.prime_set_exclusion` (`PrimeExclusion.lean:558`):

> given an admissible `S` deriving no finite disjunction of `E` (`DerivExcludes D E S`), there is
> a prime admissible `T ⊇ S` still deriving no finite disjunction of `E`.

All three obligations instantiate it at `E := {□B | B ∉ X}` for the appropriate `X`, and each
discharges `DerivExcludes` by the **same four-step argument**:

1. Suppose `S ⊢ bigOr l` for `l` drawn from `E`. Set `D := ⋁Bᵢ`; each `Bᵢ ∉ X`, so `D ∉ X`
   (primality of `X`).
2. `or_box_imp_box_or` (verified): `⊢ ⋁□Bᵢ → □D`. So `S ⊢ □D`.
3. `box_mem_of_boxed_context` (`SegmentLindenbaum.lean:100`) + `Kd` place `◇□D` in `X`.
4. `bDia` gives `D ∈ X` — contradiction.

The per-obligation differences are only in how step 3 gets `◇C` into the right head:

- **`diam_witness`** (`◇A ∈ H` ⟹ witness in `cs5Tail H`): `S := boxInv H ∪ {A}`. Step 3 is
  direct: `□(A → □D) ∈ H` then `Kd` on `◇A ∈ H`.
- **`FCsym_box`**: `S := boxInv u'.head ∪ w.head`, exclusion at `X := u'.head`. Needs
  `◇C ∈ u'.head` for `C := ⋀Δ ∈ w.head`: `bBox` gives `□◇C ∈ w.head`, so
  `◇C ∈ boxInv w.head ⊆ u.head ⊆ u'.head`. (This is 508 §5.1's paper sketch, which is correct.)
- **`FC4'`**: `S := w.head ∪ boxInv t.head`, exclusion at `X := t.head`. Needs `◇C ∈ t.head`:
  `bBox` gives `□◇C ∈ w.head`, then `4` gives `□□◇C ∈ w.head`, so
  `□◇C ∈ boxInv w.head ⊆ u.head ⊆ u'.head`, so `◇C ∈ boxInv u'.head ⊆ t.head`.

508 §5.1 judged this "not mechanized — it needs new list-splitting + finite-conjunction machinery
(`modal_deriv_imp_of_union` only splits off a *singleton*)". That is the one real piece of
supporting infrastructure still to build (§5), but it is finite-conjunction bookkeeping, not
mathematics.

## 4. The Real Gap: the Truth Lemma's Box-Backward Case

The truth lemma's box-backward case needs: `□A ∉ s.head` ⟹ `∃ s' ≥ s, ∃ Q, r s' Q ∧ A ∉ Q.head`.
With head-determined tails this means: a prime `H' ⊇ s.head` with `□A ∉ H'`, and a prime `T` with
`boxInv H' ⊆ T`, `boxInv T ⊆ H'`, `A ∉ T`.

The `prime_set_exclusion` obligation is `boxInv H' ⊬ A ∨ ⋁□Bᵢ` for `Bᵢ ∉ H'` — equivalently, via
`or_box_imp_box_or`, **`∀ D ∉ H', boxInv H' ⊬ A ∨ □D`**. The §3.4 argument does *not* apply: it
would need `□(A ∨ □D) ∈ H' → □A ∈ H' ∨ D ∈ H'`, and that principle is **not valid over `cs5FC''`**
— mechanized in `probes/cs5-boxgap-countermodel.lean`. Three worlds `{w, wp, u}`, `w ≤ wp` only,
`r`-classes `{w}` and `{wp, u}`, atom `p` at `w, wp`, atom `q` at `wp, u`:

| Fact | Lemma |
|---|---|
| all five `cs5FC''` clauses hold | `w3r_fc` |
| `□(p ∨ □q)` at `w` | `w3_box_p_or_box_q_at_w` |
| `□p` fails at `w` | `w3_not_box_p_at_w` |
| `q` fails at `w` | `w3_not_q_at_w` |

The naive route is therefore ruled out, and mechanically so:

```lean
theorem cs5_symmetric_tail_box_gap {H T : Set (Proposition Atom)}
    (hT : QuasiPrime (@CS5ModalAxiom Atom) T) {p q : Proposition Atom}
    (hbox : Proposition.box (p.or (Proposition.box q)) ∈ H)
    (hsub : boxInv H ⊆ T) (hsym : boxInv T ⊆ H) (hq : q ∉ H) : p ∈ T := by
  rcases hT.disj (hsub hbox) with h | h
  · exact h
  · exact absurd (hsym h) hq
```

If `□(p ∨ □q) ∈ H` and `q ∉ H`, then **every** member of `H`'s symmetric tail contains `p`. So
when `□p ∉ H` the box-backward case has **no witness at `H` itself**. The proof is three lines and
uses *no CS5 axiom* — it is structural, hence applies to every symmetric-tail design, and by §3.1
the tail must be symmetric. This is a genuine mechanized negative result about the sequential
route.

**But it is not an obstruction to completeness** — it is a specification for the fix. Crucially,
`cs5_symmetric_tail_box_gap` is **not vacuous**: the countermodel above realizes exactly its
hypotheses at `w`, so `H := Th(w)` is a genuine CS5-consistent quasi-prime theory with
`□(p ∨ □q) ∈ H`, `□p ∉ H`, `q ∉ H`. (`Th(w)` is quasi-prime: deductively closed by soundness over
`cs5FC''` — item 2 — and prime because `∨` is local in `CKForces`.) And that same countermodel
shows what the canonical model must do: move to the strictly larger head
`H' = Th(w') ∋ q`, where `□p ∉ H'` still holds and `T = Th(u)` works. Enlarging `H'` also enlarges
`boxInv H'`, so `H'` and `T` cannot be built sequentially — **they must be built as a simultaneous
maximal pair**. Concretely, the requirement on `H'` is a saturation condition:

> prime `H' ⊇ H` with `□A ∉ H'` and `∀ D, □(A ∨ □D) ∈ H' → D ∈ H'`.

This is the one place where CS5 needs mathematics that CK/CT/CS4 did not. `SegmentLindenbaum.lean`'s
module docstring states "the plan's feared *two-level tail-assembly fixpoint* does not arise" —
true for CK, and **false for CS5**. That sentence is the precise boundary between what is done and
what is open.

## 5. Work Items, in Dependency Order

| # | Item | Risk | Notes |
|---|---|---|---|
| 1 | `cs5FC''` in `CKExtension.lean` beside `cs4FC'`; `cs5FC_implies_cs5FC''` | none | verified |
| 2 | `cs5_axiom_sound''`/`cs5_soundness''`/`cs5_soundness_derivable''` in `CS5.lean` | none | **verified**; `cs5_soundness''` is a mechanical re-thread of `cs5_soundness` |
| 3 | Correct `CS5.lean`'s module docstring (§6.4) | none | it currently asserts a false negative result |
| 4 | `or_box_imp_box_or`, `dia_or_box_imp_or` | none | verified |
| 5 | Finite-conjunction + list-splitting helpers (generalize `modal_deriv_imp_of_union` from a singleton to a set) | low-med | 508 §5.1 flagged this; pure bookkeeping |
| 6 | `cs5Tail`, `CS5Segment`, `Preorder` instance; refl/symm/trans | low | symm free; refl `tBox`; trans `4` twice |
| 7 | `diam_witness` via `prime_set_exclusion` | medium | needs 5 |
| 8 | `FCsym_box`, `FC4'` canonically | medium | needs 5, 7 |
| 9 | **Box-backward pair construction** (§4) | **high — genuinely open** | needs a simultaneous `(H', T)` Zorn argument |
| 10 | `cs5_truth_lemma`, `cs5_completeness`, `cs5_soundness_completeness` | low | assembly, given 6–9 |

The diamond-backward case is **free** and needs no exclusion parameter (unlike CS4): if
`A ∈ t` and `t ∈ cs5Tail H`, then `bBox` gives `□◇A ∈ t`, so `◇A ∈ boxInv t ⊆ H`. So
`◇A ∉ H` immediately refutes `◇A` at `H` itself with `s' := s`. CS4's `excl` field, `cs4Tail`'s
`E` parameter, and `dia_refuting_theory` are all **not needed** for CS5.

**Recommendation on sequencing**: items 1–4 are verified and can land immediately as a
self-contained increment (CS5 soundness over the weakened condition + the corrected docstring +
the two derivability lemmas). That alone retires the false negative currently published in
`CS5.lean`. Items 5–8 are ordinary work. Item 9 should be a **separate task** with an explicit
research budget; if it does not close, CS5 completeness stays open — but it stays open at item 9,
not where 508 left it.

**Zero-debt**: no `sorry`, no new axiom, no vacuous definition is proposed. Item 9 is scoped as
research to be *completed or escalated*, never deferred with a placeholder. If item 9 fails,
`CS5.lean` gets items 1–8 plus an honest, correctly-located blocker note — not a stub.

## 6. Corrections to the Record

1. **`CS5.lean:34-41`** asserts `bDia` is "not sound over `cs5FCweak`, the natural CS5 analogue of
   the weakened frame condition that makes CS4 work" and that this "cannot be fixed by
   canonical-model work". `cs5FCweak` is not the natural analogue — it omits plain symmetry.
   `cs5_axiom_sound''` refutes the inference.
2. **`CS5.lean:43-47`** ("`FCbdia` fails on the canonical model … `u := cexpl`") holds only for
   `ofHead`'s maximal tail. Under `cs5Tail`, `cexpl` is not in any consistent head's tail (§3.2).
3. **`CS5.lean:48-54`** nominates `cs5_dia_bot_imp_bot` as "one lead" and calls canonical symmetry
   "the known-hard core … whose classical proof needs negation-completeness". Both are off:
   `Set.univ`-freeness follows from the symmetry clause directly, and canonical symmetry is
   obtained **by construction**, not proved — the maximality objection never arises because
   symmetry is never *derived*. What *is* hard is the box-backward case (§4), which 508 did not
   identify.
4. **508 report §4(c)** ("Zorn/Lindenbaum maximalization … Rejected — provably impossible") is
   correct *for exclusion sets of diamonds* and does not transfer to exclusion sets of boxes (§3.4).
5. **501 / 508 both** state that new Lindenbaum machinery beyond `SegmentLindenbaum.lean` is
   needed / not needed. The relevant lemma, `prime_set_exclusion`, has existed since task 480 in
   `Foundations/Logic/Metalogic/PrimeExclusion.lean`.

## 7. Reuse Check (CSLib/Mathlib)

Reuse-first: **no new foundational abstraction is needed**. Every name below is verified — the
probes compile against them.

| Name | Location | Use |
|---|---|---|
| `Cslib.Logic.Metalogic.prime_set_exclusion` | `Foundations/Logic/Metalogic/PrimeExclusion.lean:558` | **the key reuse** — Lindenbaum against a set |
| `Metalogic.DerivExcludes` / `bigOr` / `SetExcludingSupersets` | same file | `prime_set_exclusion`'s precondition + Zorn domain |
| `Cslib.Logic.Metalogic.prime_exclusion` | same file:226 | via `quasi_prime_exclusion` (still used) |
| `box_mem_of_boxed_context` | `Constructive/SegmentLindenbaum.lean:100` | steps 3 of §3.4, reused unchanged |
| `quasi_prime_exclusion`, `quasi_head_realization` | `Constructive/SegmentLindenbaum.lean:64`, `:242` | Lindenbaum, `realize` |
| `modal_deriv_imp_of_union` | `Constructive/*` (via `SegmentLindenbaum`) | **must be generalized** (item 5) |
| `ckvalidFC_completeness` | `Constructive/CKExtension.lean:187` | already abstract over `World` — **no change needed** |
| `axiom_mem_head` | `Constructive/CKExtension.lean:217` | axiom → head |
| `mem_head_mp` / `mem_of_axiom` | `Constructive/CKTruthLemma.lean:64` / `:57` | closure |
| `CKSegment`, `cmreach`, `cval`, `cbotForces`, `boxInv`, `quasiPrime_univ`, `cexpl` | `Constructive/Segment.lean` | model |
| `cbotForces_val` / `_mreach` / `_mreach_wit` | `Constructive/Segment.lean` | explosion, reused as-is |
| `ckforces_persistence`, `ckforces_of_exploding` | `Constructive/Forcing.lean` | soundness |
| `deductionTheorem` | `Logics/Modal/Metalogic/DeductionTheorem.lean:64` | `dia_or_box_imp_or` |
| `Preorder.lift` | Mathlib `Mathlib/Order/Basic.lean` | subtype preorder |

**Not needed for CS5** (unlike CS4): `dia_refuting_theory`, `diamRefutingSegment`, and any `excl`
parameter — the diamond-backward case is free (§5).

**501/508 assets preserved**: `CKExtension.lean` gains `cs5FC''` only; `CS4.lean`, `CT.lean`,
`CK.lean`, `Segment.lean`, `CKTruthLemma.lean` are untouched. `SegmentLindenbaum.lean` gains
item 5's helpers and one docstring correction (§4). `CS5.lean`'s existing `cs5FC` soundness
theorems are retained as corollaries via `cs5FC_implies_cs5FC''`.

## 8. Verdict

**Outcome (a): a specific Lean-level construction path.** The exact frame condition being varied
is `cs5FC` → `cs5FC''` (§ Executive Summary), the world type is `CS5Segment` over
`cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}`, and the target is

```lean
theorem cs5_soundness_completeness {φ : Proposition Atom} :
    Derivable CS5ModalAxiom φ ↔ CKValidFC.{u, u} cs5FC'' φ
```

Soundness (the direction 508 claimed was impossible) is **already proved**. Of the completeness
direction, the frame conditions and the diamond-backward case have complete paths; the
box-backward case (§4) is one genuinely open sub-problem, precisely stated, with its naive route
mechanically excluded.

CS5 completeness should **not** be marked BLOCKED. It should be re-planned around §5, with item 9
as the single research risk.

## References

- `specs/508_unblock_CK_CS4_CS5_completeness/reports/01_cs4-cs5-completeness-technique.md` §5
- `specs/508_unblock_CK_CS4_CS5_completeness/probes/cs5-obstruction-verified.lean` — `cs5FCweak`
- `specs/501_CK_constructive_modal_extensions_CT_CS4_CS5/reports/01_ct-cs4-cs5-segment-extensions.md`
- ianshil/CK, `Completeness_th/general_th_completeness.v` — `Lindenbaum_pair`/`pair_extCKH_prv`,
  the reference mechanization of `prime_set_exclusion`
- [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990] — fallible worlds, `∀∃` diamond
- [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Ch. 3 — the `IS5` frame class (reflexive + symmetric + transitive `r`), which §3.3's canonical
  `r` realizes

## Artifacts

- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-symmetry-probe.lean` —
  `wr'_not_symm`, `cs5FC''`, `cs5FC_implies_cs5FC''`, **`cs5_axiom_sound''`** (17/17 axioms).
  Compiles clean; `cs5_axiom_sound''` depends on **no axioms**.
- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-canonical-probe.lean` —
  `or_box_imp_box_or`, `dia_or_box_imp_or`, `fcbdia_forces_symmetry`,
  `cs5_symmetric_tail_box_gap`. Compiles clean.
- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-boxgap-countermodel.lean` —
  `w3r_fc`, `w3_box_p_or_box_q_at_w`, `w3_not_box_p_at_w`, `w3_not_q_at_w`, `w3val_uc`. The
  three-world model showing §4's gap is real and its naive route unrecoverable. Compiles clean.

Reproduce: `lake env lean specs/509_rescope_CK_CS5_constructive_completeness/probes/<file>.lean`
