# Research Report 01: IK Soundness + Completeness — Concrete Instantiation Map over the Task-480 Framework

- **Task**: 492 — IK (intuitionistic modal K) soundness + completeness over birelational semantics
- **Mode**: `--hard --lit` (H2 anti-analysis, H3 BibKey grounding, H4 adversarial verification)
- **Reference grounding tier**: Tier 1 (literature-backed; ground truth = [Simpson1994] + ianshil/CK Coq mechanization)
- **Verdict (one line)**: 492 is **instantiation + one new soundness proof**. The 480 framework's five modal hypotheses `{h_K, h_Kdia, h_Idb, h_Cd, h_dbot}` map **exactly** onto Simpson's IK five modal axioms `{k1,k2,k3,k4,k5}`. **`h_dbot` IS Nd (◇⊥→⊥) — there is no separate/extra Nd axiom.** **No IK axiom needs a frame condition beyond F1/F2 already in `BFrame`.** No new canonical-model machinery is required.

---

## Source-to-Implementation Mapping (H3, Tier 1)

| Source claim | BibKey | Lean target | Translation notes |
|--------------|--------|-------------|-------------------|
| Simpson's IK = 5 modal axioms k1–k5 over birelational frames | `Simpson1994` (references.bib:86) Ch.3 Def 3.1.x | `IKModalAxiom` (new datatype, 492) | k1=Kb, k2=Kd, k3=Cd, k4=Idb, k5=Nd |
| IK completeness via prime-theory birelational canonical model | `Simpson1994` Ch.3; `ChagrovZakharyaschev1997` (references.bib:75) Thm 2.43 / Lemma 5.5 | `ivalid_completeness` (480, reuse) | Instantiate `Axioms := IKModalAxiom`; no new model |
| IK axiom set `AdAx = AdAxCdIdb ∪ is_Nd` (= Cd+Idb+Nd; Kb,Kd in base) | ianshil/CK `IK_th_completeness.v`, `theories/GHC/CKH.v` (`Nd := ◊⊥→⊥`) | five `h_*` dischargers | ianshil `Nd` ≡ our `h_dbot`, verbatim |
| Intuitionistic (`IValid`) vs minimal (`MValid`) via `botForces` | `Simpson1994` Ch.3 (`IValid`/`MValid`) | `IValid` (`botForces := fun _ => False`) | IK uses IValid; Nd is only IValid-sound |
| Birelational soundness by structural induction on derivations | `Simpson1994` Lemma 2.2.1 (monotonicity) | `ik_soundness_derivable` (new, 492) | mirrors `PL.int_soundness_derivable` exactly |
| Bare CK contrast (segment/fallible model, no Cd/Idb) | `Wijesekera1990` (references.bib:885) | out of scope for 492 | flagged only; concerns task 493 |

**BibKey verification** (against `references.bib`): `Simpson1994` ✅ (line 86), `ChagrovZakharyaschev1997` ✅ (line 75), `Wijesekera1990` ✅ (line 885). No new BibKey needed — the Fischer-Servi axioms Idb/Cd are attributed to Simpson's IK.

---

## Findings

### Deliverable 1 — The IK axiom datatype + the five-hypothesis discharge map

Define a new inductive `IKModalAxiom : Proposition Atom → Prop`, mirroring `IntPropAxiom`
(`Cslib/Logics/Propositional/ProofSystem/Axioms.lean:89`) for the intuitionistic base and
`ModalAxiom` (`DerivationTree.lean:64`) for the modal constructors. Use the `Cslib.Logic.Axioms.*`
abbrev shapes for and/or (so the 480 hypotheses discharge by `rfl`) and the direct
`Proposition`-shapes for imp/efq/modal (matching the exact signatures in `Completeness.lean`).

```lean
namespace Cslib.Logic.Modal
open Cslib.Logic
variable {Atom : Type*}

/-- Axiom schemata for intuitionistic modal logic IK (Simpson's IK, [Simpson1994] Ch.3):
the 9 intuitionistic propositional schemata plus the 5 modal schemata k1–k5. -/
inductive IKModalAxiom : Proposition Atom → Prop where
  -- Intuitionistic propositional base (mirrors IntPropAxiom)
  | implyK (φ ψ : Proposition Atom)   : IKModalAxiom (φ.imp (ψ.imp φ))
  | implyS (φ ψ χ : Proposition Atom) : IKModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | efq    (φ : Proposition Atom)     : IKModalAxiom (Proposition.bot.imp φ)
  | andI   (φ ψ : Proposition Atom)   : IKModalAxiom (Axioms.AndI φ ψ)
  | andE1  (φ ψ : Proposition Atom)   : IKModalAxiom (Axioms.AndE1 φ ψ)
  | andE2  (φ ψ : Proposition Atom)   : IKModalAxiom (Axioms.AndE2 φ ψ)
  | orI1   (φ ψ : Proposition Atom)   : IKModalAxiom (Axioms.OrI1 φ ψ)
  | orI2   (φ ψ : Proposition Atom)   : IKModalAxiom (Axioms.OrI2 φ ψ)
  | orE    (φ ψ χ : Proposition Atom) : IKModalAxiom (Axioms.OrE φ ψ χ)
  -- IK modal axioms k1–k5 (exactly the 480 framework's five modal hypotheses)
  | k    (φ ψ : Proposition Atom) :  -- k1 = Kb = h_K
      IKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  | kdia (φ ψ : Proposition Atom) :  -- k2 = Kd = h_Kdia
      IKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  | cd   (φ ψ : Proposition Atom) :  -- k3 = Cd = h_Cd  (Fischer-Servi ◇-over-∨)
      IKModalAxiom ((◇(φ.or ψ)).imp ((◇φ).or (◇ψ)))
  | idb  (φ ψ : Proposition Atom) :  -- k4 = Idb = h_Idb (Fischer-Servi box)
      IKModalAxiom (((◇φ).imp (Proposition.box ψ)).imp (Proposition.box (φ.imp ψ)))
  | dbot :                            -- k5 = Nd = h_dbot  (◇⊥ → ⊥)
      IKModalAxiom ((◇Proposition.bot).imp Proposition.bot)
```

**Axiom-to-hypothesis map** (each 480 hypothesis of `ivalid_completeness`/`mvalid_completeness`
discharged by exactly one IK constructor, all `fun … => IKModalAxiom.<c> …`):

| 480 framework hypothesis (exact type from `Completeness.lean`) | IK axiom (Simpson) | ianshil name | Discharger |
|---|---|---|---|
| `h_implyK : Axioms (φ.imp (ψ.imp φ))` | IA (implyK) | IA1 | `IKModalAxiom.implyK` |
| `h_implyS : Axioms ((φ.imp (ψ.imp χ)).imp …)` | IA (implyS) | IA2 | `IKModalAxiom.implyS` |
| `h_efq : Axioms (⊥.imp φ)` | EFQ | IA9 | `IKModalAxiom.efq` |
| `h_orI1/h_orI2/h_orE : Axioms (Axioms.Or… )` | ∨-axioms | IA6–8 | `IKModalAxiom.orI1/orI2/orE` |
| `h_andI/h_andE1/h_andE2 : Axioms (Axioms.And…)` | ∧-axioms | IA3–5 | `IKModalAxiom.andI/andE1/andE2` |
| `h_K : Axioms (□(φ→ψ)→□φ→□ψ)` | **k1** | **Kb** | `IKModalAxiom.k` |
| `h_Kdia : Axioms (□(φ→ψ)→◇φ→◇ψ)` | **k2** | **Kd** | `IKModalAxiom.kdia` |
| `h_Cd : Axioms (◇(φ∨ψ)→◇φ∨◇ψ)` | **k3** | **Cd** | `IKModalAxiom.cd` |
| `h_Idb : Axioms ((◇φ→□ψ)→□(φ→ψ))` | **k4** | **Idb** | `IKModalAxiom.idb` |
| `h_dbot : Axioms (◇⊥→⊥)` | **k5** | **Nd** | `IKModalAxiom.dbot` |

**Key correction to the delegation framing.** The delegation lists "`h_dbot(◇⊥→⊥)` — plus IK's
extra Nd axiom." **These are the same axiom.** ◇⊥→⊥ is Nd (ianshil `CKH.v`: `Nd := ◊⊥ → ⊥`;
480 report 03 line 70–71: `h_Nd : Axioms ((◇⊥).imp ⊥)`; delivered 480: `h_dbot : Axioms
((◇⊥).imp ⊥)` — byte-identical). **`h_dbot ≡ Nd`.** There is **no sixth/extra axiom** to add:
the five 480 modal hypotheses already ARE Simpson's complete IK modal axiom set (k1–k5). IK adds
nothing to the 480 axiom interface.

### Deliverable 2 — Soundness (`Derivable IKModalAxiom φ → IValid φ`), genuinely new work

Target `IValid` (not `MValid`): IK is intuitionistic, and Nd/k5 is only `IValid`-sound (it fails
for arbitrary `botForces`). Mirror `PL.IntSoundness.lean` structurally:

1. `ik_axiom_sound : IKModalAxiom φ → IValid φ` — one `cases` per constructor. Frame-condition needs:

| IK axiom | Soundness argument | Frame condition needed |
|---|---|---|
| implyK/implyS/efq/and*/or* | identical to `PL.int_axiom_sound` (`BForces` non-modal cases = `PL.IForces`) | none (uses `≤`-refl/trans + `bforces_persistence`) |
| **k1 (K)** | box quantifies `≤∘r`; apply `□(φ→ψ)` at `w'`-refl and the same `r`-successor | none (reflexivity of `≤`) |
| **k2 (Kdia)** | `◇φ` gives `u` with `r w u ∧ φ@u`; `□(φ→ψ)` at `w`-refl, successor `u` yields `ψ@u`; repackage `◇ψ` | none (reflexivity) |
| **k3 (Cd)** | `◇(φ∨ψ)` gives `u`, `r w u`, `(φ∨ψ)@u`; case-split into `◇φ`/`◇ψ` at same `u` | none |
| **k4 (Idb)** | goal `□(φ→ψ)`: take `w'≥w`, `r w' v`, `v'≥v`, `φ@v'`; **use F2** on `r w' v`, `v≤v'` to get `w''≥w'` with `r w'' v'`; then `◇φ@w''`, so hyp gives `□ψ@w''`, whose `w''`-refl/`v'`-successor yields `ψ@v'` | **F2 (down-confluence)** — already a `BFrame` field |
| **k5 (Nd)** | under `IValid`, `botForces = fun _ => False`, so `BForces w' (◇⊥) = ∃u, r w' u ∧ False = False`; `◇⊥→⊥` holds **vacuously** at every world | **none** (vacuous; see verdict) |

2. `ik_soundness (d : DerivationTree IKModalAxiom Γ φ) … → BForces r val (fun _ => False) w φ`
   — induction on `d` mirroring `int_soundness` (`IntSoundness.lean:93`), with the **necessitation**
   case handled exactly as classical `Soundness.lean:168–170`: the premise `d'` has empty context,
   so the box goal `∀ w'≥w, ∀ u, r w' u → BForces … u ψ` closes by recursing into `d'` at `u`
   with the vacuous empty-context hypothesis (`fun _ h => nomatch h`).

3. `ik_soundness_derivable : Derivable IKModalAxiom φ → IValid φ` — unfold `Derivable`, apply
   `ik_soundness` at empty context (mirrors `int_soundness_derivable`, `IntSoundness.lean:120`).

Estimated size: ~130–170 lines, one file `Cslib/Logics/Modal/Metalogic/Intuitionistic/IKSoundness.lean`.
This is the **only substantial new proof** in 492.

### Deliverable 3 — Completeness (pure instantiation of 480)

```lean
theorem ik_completeness {φ : Proposition Atom} (h_valid : IValid.{u, u} φ) :
    Derivable IKModalAxiom φ :=
  ivalid_completeness
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) (fun φ => .efq φ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .idb φ ψ)
    (fun φ ψ => .cd φ ψ) .dbot h_valid
```

Each discharger is the matching constructor; the `Axioms.*` abbrev shapes make the and/or cases
`rfl`-clean. **No consistency proof is needed for `ik_completeness`** — `ivalid_completeness`
already `by_cases` on consistency of the deductive closure internally and handles the inconsistent
branch via `h_efq`. The exposed **consistency hook** `canonical_prime_world_nonempty_of_consistent`
is only needed if a downstream lemma wants `Nonempty (CanonicalPrimeWorld IKModalAxiom)`; discharge
its `¬ Derivable IKModalAxiom ⊥` obligation as a **corollary of soundness** (deliverable 2):

```lean
theorem ik_consistent : ¬ Derivable IKModalAxiom (Proposition.bot : Proposition Atom) :=
  fun h => -- ik_soundness_derivable h : IValid ⊥, contradicted by any inhabited model
    absurd (ik_soundness_derivable h PUnit _ (fun _ _ => False) (fun _ _ h => h) PUnit.unit) id
```

Biconditional payoff: `ik_soundness_completeness : IValid φ ↔ Derivable IKModalAxiom φ :=
⟨ik_completeness, ik_soundness_derivable⟩` (mirrors `PL.int_soundness_completeness`).

### Deliverable 4 — Reuse-first gate (zero new canonical machinery)

Confirmed **NO new canonical-model machinery** is needed. 480 supplies, all `Axioms`-parametric:
`canonicalBModel`, `canonical_f1`/`canonical_f2`, `canonicalR`/`canonicalVal`,
`canonical_truth_lemma`, `modal_prime_exclusion`, `diaOr_of_diaDisj`, the consistency hook, and
`ivalid_completeness`/`mvalid_completeness`. Genuinely new 492 work is **only**:
(1) the `IKModalAxiom` datatype (mechanical, mirrors `IntPropAxiom`+`ModalAxiom`);
(2) `ik_soundness_derivable` (the birelational soundness proof — new but templated on
`IntSoundness.lean` + classical `Soundness.lean`);
(3) thin instantiations `ik_completeness`, `ik_consistent`, `ik_soundness_completeness`.
Reuse Check Protocol (all 5 steps): `Cslib.Foundations.*` (Axioms abbrevs reused), typeclass
hierarchy (`HasBox`/`HasDia`/`Bot` reused via `Modal.Proposition`), notation (`□`/`◇` scoped,
reused), Mathlib (`Preorder`/`le_trans`/`le_refl` reused), `Logics/*` namespace
(`IValid`/`BForces`/`bforces_persistence`/all 480 lemmas reused). No new abstraction warranted.

---

## Adversarial Self-Verification (H4)

The delegation's core adversarial question: *is there any IK axiom whose soundness needs a frame
condition NOT already in `BFrame` (F1/F2)? Nd is the likely candidate — pin it down.*

**Verdict: NO. No IK axiom needs any frame condition beyond F1/F2 already in `BFrame`.** Pinned down:

1. **Nd (◇⊥→⊥) needs NO frame condition** (challenged hardest). Under `IValid`, `BModel.botForces`
   is fixed to `fun _ => False` (baked into `IValid`'s definition, `Birelational.lean:193–199`).
   Then `BForces r val (fun _ => False) w' (◇⊥) = ∃u, r w' u ∧ False`, which is `False` for every
   `w'`, so `◇⊥→⊥` is **vacuously valid in every birelational frame**. The only "frame condition"
   for Nd is the intuitionistic convention `botForces = ⊥-never-forced`, which `IValid` supplies for
   free. **The "separate Nd frame lemma" report 03 §5 flagged is therefore unnecessary for the
   IValid soundness direction.** (Confidence: HIGH — direct from the `BForces .bot`/`.diamond`
   defining equations, verified against `Birelational.lean:117,124`.)
   Corollary: Nd is precisely the axiom that fails for `MValid` (arbitrary `botForces`), which is
   exactly why IK targets `IValid` and minimal logic (task 495) drops Nd. Semantic role of Nd =
   `botForces = False`, mirroring ianshil's `_th` model restricting to **consistent** prime theories
   (no fallible `cexpl` world) — same content, no dedicated frame relation.

2. **k4/Idb needs F2, which is already in `BFrame`.** Challenged: could Idb need a *new* condition?
   Traced the proof (deliverable 2 table): it consumes `F.f2` (down-confluence, `BFrame.f2`,
   `Birelational.lean:74–76`) once, to relocate the `A`-witness world upward so `◇A` becomes
   available at a `≥`-successor. F2 is a `BFrame` field (present since task 490, comment line 45–46
   notes it was added precisely "to validate the IK interaction axioms"). **Confirmed: no new
   condition.** (Confidence: HIGH.)

3. **"h_dbot is vestigial / not really consumed" — refuted.** Challenged whether `h_dbot` is a
   carried-but-unused hypothesis. `grep` of `CanonicalModel.lean` shows `h_dbot` is the **base case
   of `diaOr_of_diaDisj`** (`bigOr [] = ⊥`, line ~785–796: `exact .ax [] _ h_dbot`), consumed by
   `canonical_f1` and the diamond truth case (lines 905, 1124, 1161). So Nd is **genuinely required
   by the delivered 480 framework**, not merely conservatively threaded. (Confidence: HIGH.)

4. **Correction to report 03 (recorded, not hidden).** Report 03 §4 predicted "Nd is NOT required
   anywhere in the framework … layered on in task 492." The **delivered** framework contradicts
   this: `h_dbot` (=Nd) is one of the five core hypotheses of `ivalid_completeness`/
   `mvalid_completeness` and is consumed in `diaOr_of_diaDisj`. The implementation evolved past the
   report's prediction (likely: folding Nd in let the prime-pair diamond distribution close without a
   fallible-world case split — see `CanonicalModel.lean:746–773`). **Consequence for 492 is
   favorable**: IK's axiom set exactly equals the framework's five modal hypotheses; there is nothing
   extra to thread. Net effect on the delegation's plan: *simpler*, not harder.

5. **Shape-match discharge risk — checked.** The 480 and/or hypotheses want `Axioms (Axioms.OrI1 φ
   ψ)` etc.; `Axioms.OrI1` is a `protected abbrev` (`Foundations/Logic/Axioms.lean:122`), hence
   reducible, so `IKModalAxiom.orI1 φ ψ : IKModalAxiom (Axioms.OrI1 φ ψ)` discharges `h_orI1` by
   `rfl`. `ModalAxiom` already uses this convention (`DerivationTree.lean:96–112`). imp/efq/modal
   hypotheses use direct `Proposition` shapes matching `Completeness.lean:81–98` verbatim.
   (Confidence: HIGH.)

**Zero-debt**: every axiom is a `DerivationTree`-carried schema or a parametric discharge; no
`sorry`/`admit`/global `axiom`. **No forbidden analysis-only output**: this report ends in concrete
Lean datatype, discharge lambdas, a per-axiom soundness table, and a file plan.

**Confidence summary**: Nd needs no frame condition HIGH; Idb needs F2 (in BFrame) HIGH;
h_dbot≡Nd≡k5 HIGH; five-hypothesis map exact HIGH; completeness = pure instantiation HIGH;
soundness is the only new proof HIGH.

---

## Next Steps

`/plan 492` — plan is small and near-deterministic: Phase 1 `IKModalAxiom` datatype (+ discharge
lemmas), Phase 2 `ik_soundness_derivable` (new proof, the only real work), Phase 3
`ik_completeness`/`ik_consistent`/`ik_soundness_completeness` instantiations. Single new file
`Cslib/Logics/Modal/Metalogic/Intuitionistic/IK.lean` (or split `IKSoundness.lean` +
`IK.lean`), import `Intuitionistic/Completeness.lean`.
