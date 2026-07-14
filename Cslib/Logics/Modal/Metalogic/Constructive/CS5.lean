/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CKExtension

/-! # CS5: Constructive Modal Logic S5 (Soundness, and the Symmetric-Tail Completeness Route)

This module instantiates the task-501 frame-condition-parametrized segment scaffold
(`CKExtension.lean`) at the constructive analogue of `S5`: `CS5` = `CS4` (`CS4.lean`) plus the two
`B` schemata `bBox : A → □◇A` and `bDia : ◇□A → A`.

**Adversarial finding (research report, Deliverable 3.1; carried over from task 494
Deliverable 6): `CS5` is axiomatized here via `B` (symmetry), NOT via the classical euclidean/`5`
axiom `◇A → □◇A`.** The classical canonical-euclideanness route needs negation-completeness,
unavailable to quasi-prime theories (which are *further* from negation-complete than task 494's
prime theories — they additionally admit the exploding theory `Set.univ`). Symmetry closure is
fully positive (MP-closure only); reflexivity (`T`) + transitivity (`4`) + symmetry (`B`) give an
equivalence relation, Simpson's constructive `S5` frame class.

`CS5` is sound for `CKValidFC cs5FC` — Wijesekera-style fallible-world validity restricted to
frames whose modal relation `r` is reflexive, ≤-composed-transitive, and ≤-composed-symmetric
(`cs5FC`, `CKExtension.lean`). `CS5` is **also** sound for the weakened frame condition `cs5FC''`
(`cs5_axiom_sound''`, all 17 axioms, axiom-free) — see below.

**Task 508's published negative verdict is refuted (task 509).** Task 508 claimed `bDia` is
"not sound over `cs5FCweak`, the natural `CS5` analogue of the weakened frame condition that
makes `CS4` work" and that this was "a soundness failure which no amount of canonical-model work
on the completeness side can fix." Both claims are corrected:

- `cs5FCweak` is **not** the natural analogue of the frame condition that makes `CS4`
  completeness work. It omits **plain symmetry** (`r w u → r u w`, exactly the clause `bDia`
  needs) and **plain transitivity**; that omission, not a real obstruction, is why `bDia` was
  unsound over it. Its countermodel relation `wr'` is itself not plainly symmetric
  (`Cslib.Logic.Modal.wr'_not_symm`, `probes/cs5-symmetry-probe.lean`), so it refutes nothing
  about the correctly-shaped frame condition below; 508's countermodel remains *sound*, it simply
  does not bear on `cs5FC''`.
- The correctly-shaped weakened frame condition, `cs5FC''` (`CKExtension.lean`) — reflexivity,
  *plain* transitivity, *plain* symmetry, the `cs4FC'` re-basing clause, and the weakened
  ≤-composed symmetry `FCsym_box` — validates **all 17** `CS5` axioms
  (`cs5_axiom_sound''`, this module, axiom-free) and genuinely weakens `cs5FC`
  (`cs5FC_implies_cs5FC''`, `CKExtension.lean`).

Task 508 also read the canonical failure of `FCbdia` (its strong, ≤-saturated symmetry clause) at
`u := cexpl`, the exploding tail world, as evidence that constructive `S5` canonical completeness
needs negation-completeness. This does not survive the symmetric-tail design (Phase 5, below):
`boxInv Set.univ = Set.univ`, so **no consistent head has an exploding member in its symmetric
tail** — `Set.univ`-freeness follows directly from the tail's `boxInv t ⊆ H` clause, with **no**
appeal to `cs5_dia_bot_imp_bot` (508's nominated "one lead", which turned out to be unnecessary).
And canonical symmetry is obtained **by construction** (`cs5Tail_symm`: the tail's two clauses
simply swap), **never derived** from maximality — so the negation-completeness objection 508
raised (`B ∉ w.head ⇒ ¬B ∈ w.head`, unavailable for quasi-prime heads) never arises. This is the
step 508 called "the known-hard core of constructive `S5` canonical completeness"; here it is
free.

**The actual remaining open sub-problem is narrower and different from 508's**: the truth
lemma's *box-backward* case (`□A ∉ H` ⟹ some symmetric-tail member of a *possibly-larger* head
omits `A`). `cs5_symmetric_tail_box_gap` mechanizes why the naive route — finding the witness
tail member at `H` itself, or building the enlarged head sequentially before its tail — fails:
if `□(p ∨ □q) ∈ H` and `q ∉ H`, every symmetric-tail member of `H` contains `p`, so the
box-backward witness (when `□p ∉ H` too) must come from a *strictly larger* head `H' ⊇ H`, whose
own tail must be built *simultaneously* with `H'`, not sequentially. This is genuinely a
different, better-understood obstruction than 508's — soundness is not in question, and the
canonical frame conditions are fully established (see `## Main Definitions`).

**`CS5` is theorem-for-theorem Simpson's `IS5`** (Pacheco, `Pacheco2024`, Theorem 13; his
Conclusion states the constructive and intuitionistic variants of `DB`/`TB`/`KB5`/`S5` coincide).
This is unlike `CK`/`CT`/`CS4`, which genuinely differ from their intuitionistic counterparts —
`B` re-derives the two axioms bare `CK` deliberately drops: `k3` (`◇(A ∨ B) → ◇A ∨ ◇B`, this
module's `cs5_dia_or`) and `k5` (`◇⊥ → ⊥`, task 508's `cs5_dia_bot_imp_bot`)
(`ArisakaDasStrassburger2015` reports both facts for the general `B`-extension). So `CS5` is
**not** a constructively distinct logic from `IS5`, and this module does not present it as one.
The completeness theorem proved here is still worth having: it targets the fallible-world
*segment* semantics (`CKForces`/`CKValid`), not `IS5`'s birelational one — a genuinely different
model theory even though the theorem sets coincide. Relatedly: prime-theory canonical
completeness works for `CS5` **precisely because** `B` collapses it out of the fallible-world
regime that makes `CS4`'s `excl`-parametrized tail necessary (Pacheco's own diagnosis, chunk
`01990319adea2569`) — a `CS5` success is **not** a template for other `CK` extensions still
inside that regime.

**`Pacheco2024` is cited as the source of the pair-construction *technique*, not as an
established result.** His Lemma 18 (the two-sided Lindenbaum pair construction the box-backward
case needs) delegates its primeness step to Lemma 16, whose proof contains an unlabelled
negation-completeness move (`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`) that a poset-maximal, quasi-prime `Θ` does not
license; wherever this module or its probes cite `Pacheco2024`, this distinction is made
explicit — see `probes/cs5-pair-primeness.lean` for the confirmation-against-the-paper and the
sound replacement.

For the full mechanized analysis (refutation of 508's verdict, the symmetric-tail design, the
box-backward gap, and the Pacheco cross-check), see
`specs/509_rescope_CK_CS5_constructive_completeness/reports/01_cs5-symmetric-tail-construction.md`
and the `probes/` directory in that task's spec folder.

## Main Definitions

- `CS5ModalAxiom`: `CS4ModalAxiom`'s constructors verbatim plus `bBox`/`bDia` (B, not
  euclidean-5).
- `cs5_axiom_sound`/`cs5_soundness`/`cs5_soundness_derivable`: soundness for `CKValidFC cs5FC`.
- `cs5_axiom_sound''`/`cs5_soundness''`/`cs5_soundness_derivable''`: soundness for
  `CKValidFC cs5FC''` (the weakened, genuinely-more-general frame condition; the half task 508
  declared impossible), axiom-free for `cs5_axiom_sound''`.
- `or_box_imp_box_or`/`dia_or_box_imp_or`: the disjunction-of-boxes identity that discharges the
  `prime_set_exclusion` side conditions against exclusion sets of *boxes* (not diamonds).
- `cs5_dia_or`: `CS5 ⊢ ◇(A ∨ B) → ◇A ∨ ◇B` (`k3`), corroborating the `CS5 ≡ IS5` collapse.
- `cs5_boxInv_subset_iff`: `boxInv T ⊆ H ↔ T ⊆ diaInv H` — the box-inverse tail clause and
  Pacheco's diamond-inverse canonical relation `∼c` coincide over `CS5`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2 and Definition 1.1.4.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the birelational `IS5`, the structural template for the `B`-via-symmetry decision).
* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024] — source
  of the pair-construction technique for the box-backward case (Lemma 18's *skeleton* only; its
  primeness step, Lemma 16, is unsound as written — see above).
* [R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
  Logics*][ArisakaDasStrassburger2015] — source of the `B ⊢ k3, k5` fact corroborating
  `CS5 ≡ IS5`.

**Note**: this docstring states the status as of task 509 Phase 3. If the box-backward case
closes (Phase 11 Branch A), this docstring is revised to final status (completeness established)
and the "actual remaining open sub-problem" paragraph above is removed. If it does not close
(Phase 11 Branch B), the obstruction is restated as the precisely-located mechanized theorem
Phase 10 produces, and this module does **not** claim `CS5` completeness is blocked at the
library level — only that this specific sub-problem is open.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The `CS5` Axiom Schemata -/

/-- Axiom schemata for constructive modal logic `CS5`: the 15 `CS4ModalAxiom` constructors
verbatim, plus the two `B` schemata `bBox`/`bDia`. Both box and diamond forms are required since
`◇` is primitive (not `□`-definable) in this framework's `Proposition` datatype (mirroring
`IS5.lean`'s `IS5` extension of `IS4`). Deliberately **not** the classical euclidean/`5` axiom
`◇A → □◇A` (see module docstring). -/
inductive CS5ModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CS5ModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CS5ModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CS5ModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CS5ModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CS5ModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CS5ModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))
  /-- `T` box form: `□A → A`. -/
  | tBox (φ : Proposition Atom) :
      CS5ModalAxiom ((Proposition.box φ).imp φ)
  /-- `T` diamond form: `A → ◇A`. -/
  | tDia (φ : Proposition Atom) :
      CS5ModalAxiom (φ.imp (◇φ))
  /-- `4` box form: `□A → □□A`. -/
  | fourBox (φ : Proposition Atom) :
      CS5ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))
  /-- `4` diamond form: `◇◇A → ◇A`. -/
  | fourDia (φ : Proposition Atom) :
      CS5ModalAxiom ((◇◇φ).imp (◇φ))
  /-- `B` box form: `A → □◇A`. -/
  | bBox (φ : Proposition Atom) :
      CS5ModalAxiom (φ.imp (Proposition.box (◇φ)))
  /-- `B` diamond form: `◇□A → A`. -/
  | bDia (φ : Proposition Atom) :
      CS5ModalAxiom ((◇(Proposition.box φ)).imp φ)

/-! ## Soundness -/

/-- Every `CS5ModalAxiom` instance is `CKValidFC cs5FC` (Wijesekera-style fallible-world validity
over reflexive, ≤-composed-transitive, ≤-composed-symmetric frames). The 15 non-`B` cases are
`cs4_axiom_sound`'s cases verbatim (`CS4.lean`), with the symmetry component of `hfc` threaded
through unused. The two new cases:
- `bDia` (`◇□A → A`): at `w'` (`le_refl`) get `u` with `r w' u ∧ □A@u`; instantiate `□A@u` at `u`
  (`le_refl`) and `w'` via **plain** symmetry (`hsymm hru (le_refl u)`, the `u' := u`
  specialization of the ≤-composed clause).
- `bBox` (`A → □◇A`): the nested box goal introduces `w'' ≥ w'`, `u` with `r w'' u`; unfolding
  `◇A@u` introduces `u' ≥ u`; witness `w''` via **≤-composed** symmetry
  (`r w'' u → u ≤ u' → r u' w''`), with `A@w''` by persistence from `A@w'` (`w' ≤ w''`). -/
theorem cs5_axiom_sound {φ : Proposition Atom} (h_ax : CS5ModalAxiom φ) :
    CKValidFC.{u, v} cs5FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, htrans, hsymm⟩ := hfc
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact ckforces_persistence v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro w' _ hbot
    exact ckforces_of_exploding bf_uc bf_val bf_r bf_r_wit hbot φ
  | andI φ ψ =>
    intro w₁ _ hφ w₂ hw₂ hψ
    exact ⟨ckforces_persistence v_uc bf_uc hw₂ hφ, hψ⟩
  | andE1 φ ψ =>
    intro _ _ h; exact h.1
  | andE2 φ ψ =>
    intro _ _ h; exact h.2
  | orI1 φ ψ =>
    intro _ _ h; exact Or.inl h
  | orI2 φ ψ =>
    intro _ _ h; exact Or.inr h
  | orE φ ψ χ =>
    intro w₁ _ h_pq w₂ hw₂ h_rq w₃ hw₃ h_pr
    have hw₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pr.elim (fun hp => h_pq w₃ hw₁₃ hp) (fun hr => h_rq w₃ hw₃ hr)
  | k φ ψ =>
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    intro w' _ hbox_imp w'' hw' hdia_phi w₃ hw₃
    obtain ⟨u, hru, hφu⟩ := hdia_phi w₃ hw₃
    exact ⟨u, hru, hbox_imp w₃ (le_trans hw' hw₃) u hru u (le_refl u) hφu⟩
  | tBox φ =>
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    intro w' _ hφ w'' hw''
    exact ⟨w'', hrefl w'', ckforces_persistence v_uc bf_uc hw'' hφ⟩
  | fourDia φ =>
    intro w' _ hdidia w'' hw''
    obtain ⟨u, hru, hdia_u⟩ := hdidia w'' hw''
    obtain ⟨t, hut, hφt⟩ := hdia_u u (le_refl u)
    exact ⟨t, htrans hru (le_refl u) hut, hφt⟩
  | fourBox φ =>
    intro w' _ hbox w'' hw'' u hru u' hu' t hrt
    exact hbox w'' hw'' t (htrans hru hu' hrt)
  | bDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, hboxA⟩ := hdia w' (le_refl w')
    exact hboxA u (le_refl u) w' (hsymm hru (le_refl u))
  | bBox φ =>
    intro w' _ hφ w'' hw'' u hru u' hu'
    exact ⟨w'', hsymm hru hu', ckforces_persistence v_uc bf_uc hw'' hφ⟩

/-- **Soundness**: if `DerivationTree CS5ModalAxiom Γ φ`, then in any fallible-world model whose
modal relation is reflexive, ≤-composed-transitive, and ≤-composed-symmetric (`cs5FC`), at any
world `w` where all formulas in `Γ` are forced, `φ` is also forced. Structural analogue of
`cs4_soundness` (`CS4.lean`), threading `hfc` through unused except at the `.ax` case. -/
theorem cs5_soundness
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS5ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs5FC r)
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → CKForces r val botForces w ψ) :
    CKForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact cs5_axiom_sound h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact cs5_soundness d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (cs5_soundness d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact cs5_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact cs5_soundness d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas**: if `Derivable CS5ModalAxiom φ`, then `φ` is
`CKValidFC cs5FC`. -/
theorem cs5_soundness_derivable {φ : Proposition Atom}
    (h : Derivable CS5ModalAxiom φ) : CKValidFC.{u, v} cs5FC φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact cs5_soundness d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

/-! ## Soundness over `cs5FC''` -/

/-- **Every `CS5ModalAxiom` instance is `CKValidFC cs5FC''`** (the weakened frame condition:
reflexivity, plain transitivity, plain symmetry, the `cs4FC'` re-basing clause, and the
weakened ≤-composed symmetry `FCsym_box`). This is the half task 508 declared impossible. It is
`cs5_axiom_sound`'s proof with exactly four cases changed relative to the `cs5FC` version above:
- `fourDia` (`◇◇A → ◇A`): uses **plain** transitivity `htrans hru hut` directly (no `≤`-chaining
  needed, since `cs5FC''`'s transitivity clause is already the plain `u' := u` form).
- `fourBox` (`□A → □□A`): uses `hfour hru hu' hrt`, the `cs4FC'` re-basing clause, to obtain a
  witness `v ≥ w''` at which `□A@w'` (quantified over all `z ≥ w'`) still discharges `A@t`.
- `bDia` (`◇□A → A`): uses **plain** symmetry `hsymm hru` directly (no `le_refl` padding needed).
- `bBox` (`A → □◇A`): uses `hsymbox hru hu'`, the weakened ≤-composed symmetry, to obtain a
  witness `t` with `w'' ≤ t`; `A@t` follows from `A@w'` by persistence along `w'' ≤ t`.
The other 13 cases are verbatim from `cs5_axiom_sound`. Transcribed from
`probes/cs5-symmetry-probe.lean` (verified, axiom-free). -/
theorem cs5_axiom_sound'' {φ : Proposition Atom} (h_ax : CS5ModalAxiom φ) :
    CKValidFC.{u, v} cs5FC'' φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨hrefl, htrans, hsymm, hfour, hsymbox⟩ := hfc
  cases h_ax with
  | implyK φ ψ =>
    intro w' _ hφ w'' hw' _
    exact ckforces_persistence v_uc bf_uc hw' hφ
  | implyS φ ψ χ =>
    intro w₁ hw₁ h_pqr w₂ hw₂ h_pq w₃ hw₃ h_p
    have h₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pqr w₃ h₁₃ h_p w₃ (le_refl w₃) (h_pq w₃ hw₃ h_p)
  | efq φ =>
    intro w' _ hbot
    exact ckforces_of_exploding bf_uc bf_val bf_r bf_r_wit hbot φ
  | andI φ ψ =>
    intro w₁ _ hφ w₂ hw₂ hψ
    exact ⟨ckforces_persistence v_uc bf_uc hw₂ hφ, hψ⟩
  | andE1 φ ψ => intro _ _ h; exact h.1
  | andE2 φ ψ => intro _ _ h; exact h.2
  | orI1 φ ψ => intro _ _ h; exact Or.inl h
  | orI2 φ ψ => intro _ _ h; exact Or.inr h
  | orE φ ψ χ =>
    intro w₁ _ h_pq w₂ hw₂ h_rq w₃ hw₃ h_pr
    have hw₁₃ : w₁ ≤ w₃ := le_trans hw₂ hw₃
    exact h_pr.elim (fun hp => h_pq w₃ hw₁₃ hp) (fun hr => h_rq w₃ hw₃ hr)
  | k φ ψ =>
    intro w' _ hbox_imp w'' hw' hbox_phi w1 hw1 u hru
    exact hbox_imp w1 (le_trans hw' hw1) u hru u (le_refl u) (hbox_phi w1 hw1 u hru)
  | kdia φ ψ =>
    intro w' _ hbox_imp w'' hw' hdia_phi w₃ hw₃
    obtain ⟨u, hru, hφu⟩ := hdia_phi w₃ hw₃
    exact ⟨u, hru, hbox_imp w₃ (le_trans hw' hw₃) u hru u (le_refl u) hφu⟩
  | tBox φ =>
    intro w' _ hbox
    exact hbox w' (le_refl w') w' (hrefl w')
  | tDia φ =>
    intro w' _ hφ w'' hw''
    exact ⟨w'', hrefl w'', ckforces_persistence v_uc bf_uc hw'' hφ⟩
  | fourDia φ =>
    intro w' _ hdidia w'' hw''
    obtain ⟨u, hru, hdia_u⟩ := hdidia w'' hw''
    obtain ⟨t, hut, hφt⟩ := hdia_u u (le_refl u)
    exact ⟨t, htrans hru hut, hφt⟩
  | fourBox φ =>
    intro w' _ hbox w'' hw'' u hru u' hu' t hrt
    obtain ⟨v, hwv, hrvt⟩ := hfour hru hu' hrt
    exact hbox v (le_trans hw'' hwv) t hrvt
  | bDia φ =>
    intro w' _ hdia
    obtain ⟨u, hru, hboxA⟩ := hdia w' (le_refl w')
    exact hboxA u (le_refl u) w' (hsymm hru)
  | bBox φ =>
    intro w' _ hφ w'' hw'' u hru u' hu'
    obtain ⟨t, hru't, hw''t⟩ := hsymbox hru hu'
    exact ⟨t, hru't, ckforces_persistence v_uc bf_uc (le_trans hw'' hw''t) hφ⟩

/-- **Soundness over `cs5FC''`**: if `DerivationTree CS5ModalAxiom Γ φ`, then in any
fallible-world model whose modal relation satisfies `cs5FC''`, at any world `w` where all
formulas in `Γ` are forced, `φ` is also forced. Structural analogue of `cs5_soundness`,
threading `hfc` through unused except at the `.ax` case. -/
theorem cs5_soundness''
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree CS5ModalAxiom Γ φ)
    {World : Type v} [Preorder World]
    (r : World → World → Prop) (hfc : cs5FC'' r)
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    (w : World)
    (h_ctx : ∀ ψ, ψ ∈ Γ → CKForces r val botForces w ψ) :
    CKForces r val botForces w φ := by
  match d with
  | .ax _ ψ h_ax =>
    exact cs5_axiom_sound'' h_ax World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  | .assumption _ ψ h_mem =>
    exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    exact cs5_soundness'' d₁ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx
      w (le_refl w)
      (cs5_soundness'' d₂ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w h_ctx)
  | .necessitation ψ d' =>
    intro w' _hle u _hru
    exact cs5_soundness'' d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit u
      (fun _ h => nomatch h)
  | .weakening Γ' Δ ψ d' h_sub =>
    exact cs5_soundness'' d' r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Soundness for derivable formulas over `cs5FC''`**: if `Derivable CS5ModalAxiom φ`, then
`φ` is `CKValidFC cs5FC''`. -/
theorem cs5_soundness_derivable'' {φ : Proposition Atom}
    (h : Derivable CS5ModalAxiom φ) : CKValidFC.{u, v} cs5FC'' φ := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨d⟩ := h
  exact cs5_soundness'' d r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
    (fun _ h => nomatch h)

/-! ## The Disjunction-of-Boxes Identity -/

/-- `⊢ □B → □(B ∨ B')` — necessitation + `Kb` on `orI1`. Private helper for
`or_box_imp_box_or`. -/
private def box_mono_or_left (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box B).imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _ (.ax [] _ (.k B (B.or B')))
    (.necessitation _ (.ax [] _ (.orI1 B B')))

/-- `⊢ □B' → □(B ∨ B')` — necessitation + `Kb` on `orI2`. Private helper for
`or_box_imp_box_or`. -/
private def box_mono_or_right (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      ((Proposition.box B').imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _ (.ax [] _ (.k B' (B.or B')))
    (.necessitation _ (.ax [] _ (.orI2 B B')))

/-- **`⊢ (□B ∨ □B') → □(B ∨ B')`** — a *disjunction of boxes* implies the *box of the
disjunction*. Pure `CK` (necessitation + `Kb` + `orI`/`orE`); no `T`/`4`/`B`. This is the
identity that lets an n-ary `DerivExcludes` side condition against an exclusion set of *boxes*
`E := {□B | B ∉ H}` be collapsed to the single formula `□(⋁Bᵢ)` for `prime_set_exclusion`
(Phase 6). It is exactly the step task 508 §4(c) believed was unavailable: that section rejected
simultaneous exclusion because `◇(A ∨ B) → ◇A ∨ ◇B` is underivable — true in bare `CK`, but
irrelevant here, since the exclusion set in this construction is a set of **boxes**, not
diamonds, and boxes distribute the right way. Transcribed from `probes/cs5-canonical-probe.lean`
(verified, axiom-free). -/
private def or_box_box_or (B B' : Proposition Atom) :
    DerivationTree (@CS5ModalAxiom Atom) []
      (((Proposition.box B).or (Proposition.box B')).imp (Proposition.box (B.or B'))) :=
  .modus_ponens _ _ _
    (.modus_ponens _ _ _ (.ax [] _ (.orE (Proposition.box B) (Proposition.box B')
      (Proposition.box (B.or B')))) (box_mono_or_left B B'))
    (box_mono_or_right B B')

theorem or_box_imp_box_or (B B' : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      (((Proposition.box B).or (Proposition.box B')).imp (Proposition.box (B.or B'))) :=
  ⟨or_box_box_or B B'⟩

/-- **`⊢ ◇(□B ∨ □B') → (B ∨ B')`** in `CS5`. Chain: `or_box_imp_box_or` under `◇` (necessitation
+ `Kd`), then `bDia` at `B ∨ B'`. Together with primality of a head `H`, this discharges the
`DerivExcludes` precondition of `prime_set_exclusion` against `E := {□B | B ∉ H}` (Phase 6): if
`◇(⋁□Bᵢ) ∈ H` then `⋁Bᵢ ∈ H`, so some `Bᵢ ∈ H` — contradicting `Bᵢ ∉ H`. Transcribed from
`probes/cs5-canonical-probe.lean` (verified, axiom-free). -/
theorem dia_or_box_imp_or (B B' : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom)
      ((◇((Proposition.box B).or (Proposition.box B'))).imp (B.or B')) := by
  obtain ⟨d4⟩ := or_box_imp_box_or B B'
  have hkd : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇((Proposition.box B).or (Proposition.box B'))).imp
        (◇(Proposition.box (B.or B')))) :=
    .modus_ponens _ _ _
      (.ax [] _ (.kdia ((Proposition.box B).or (Proposition.box B'))
        (Proposition.box (B.or B'))))
      (.necessitation _ d4)
  have hbd : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇(Proposition.box (B.or B'))).imp (B.or B')) := .ax [] _ (.bDia (B.or B'))
  let X := ◇((Proposition.box B).or (Proposition.box B'))
  have hctx : DerivationTree (@CS5ModalAxiom Atom) [X] (B.or B') := by
    have a0 : DerivationTree (@CS5ModalAxiom Atom) [X] X :=
      .assumption _ _ (List.mem_cons.mpr (Or.inl rfl))
    exact .modus_ponens _ _ _ (.weakening [] [X] _ hbd (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [X] _ hkd (fun _ h => nomatch h)) a0)
  exact ⟨deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) []
    X (B.or B') hctx⟩

/-! ## `k3`: CS5 Derives Diamond-Distributes-over-Disjunction -/

/-- Chain two empty-context implications. Private helper for `cs5_dia_or`. -/
private noncomputable def cs5_impTrans {a b c : Proposition Atom}
    (h1 : DerivationTree (@CS5ModalAxiom Atom) [] (a.imp b))
    (h2 : DerivationTree (@CS5ModalAxiom Atom) [] (b.imp c)) :
    DerivationTree (@CS5ModalAxiom Atom) [] (a.imp c) :=
  deductionTheorem (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ) [] a c
    (.modus_ponens _ _ _ (.weakening [] [a] _ h2 (fun _ h => nomatch h))
      (.modus_ponens _ _ _ (.weakening [] [a] _ h1 (fun _ h => nomatch h))
        (.assumption _ _ (List.mem_cons.mpr (Or.inl rfl)))))

/-- **`CS5 ⊢ ◇(A ∨ B) → ◇A ∨ ◇B`** — the `k3`/`Cd` axiom that bare `CK` deliberately lacks.
Arisaka–Das–Straßburger (`ArisakaDasStrassburger2015`) report that the `B` axioms entail `k3`
and `k5` (`◇⊥ → ⊥`, task 508's `cs5_dia_bot_imp_bot`) — the very two axioms `CK` drops. This
matters beyond the derivation itself: task 508 §4(c) rejected simultaneous Lindenbaum exclusion
on the ground that `◇(A ∨ B) → ◇A ∨ ◇B` is underivable — true in `CK`/`CT`/`CS4`, **false in
`CS5`**, so that impossibility argument never applied to `CS5` at all.

Derivation: `bBox` on each disjunct, then `or_box_imp_box_or`, then necessitation + `Kd`, then
`bDia`. Transcribed from `probes/cs5-k3-probe.lean` (verified, axiom-free). -/
theorem cs5_dia_or (A B : Proposition Atom) :
    Derivable (@CS5ModalAxiom Atom) ((◇(A.or B)).imp ((◇A).or (◇B))) := by
  have hA : DerivationTree (@CS5ModalAxiom Atom) []
      (A.imp ((Proposition.box (◇A)).or (Proposition.box (◇B)))) :=
    cs5_impTrans (.ax [] _ (.bBox A)) (.ax [] _ (.orI1 (Proposition.box (◇A))
      (Proposition.box (◇B))))
  have hB : DerivationTree (@CS5ModalAxiom Atom) []
      (B.imp ((Proposition.box (◇A)).or (Proposition.box (◇B)))) :=
    cs5_impTrans (.ax [] _ (.bBox B)) (.ax [] _ (.orI2 (Proposition.box (◇A))
      (Proposition.box (◇B))))
  have h1 : DerivationTree (@CS5ModalAxiom Atom) []
      ((A.or B).imp ((Proposition.box (◇A)).or (Proposition.box (◇B)))) :=
    .modus_ponens _ _ _ (.modus_ponens _ _ _
      (.ax [] _ (.orE A B ((Proposition.box (◇A)).or (Proposition.box (◇B))))) hA) hB
  have h2 : DerivationTree (@CS5ModalAxiom Atom) []
      ((A.or B).imp (Proposition.box ((◇A).or (◇B)))) :=
    cs5_impTrans h1 (or_box_box_or (◇A) (◇B))
  have h3 : DerivationTree (@CS5ModalAxiom Atom) []
      ((◇(A.or B)).imp (◇(Proposition.box ((◇A).or (◇B))))) :=
    .modus_ponens _ _ _
      (.ax [] _ (.kdia (A.or B) (Proposition.box ((◇A).or (◇B)))))
      (.necessitation _ h2)
  exact ⟨cs5_impTrans h3 (.ax [] _ (.bDia ((◇A).or (◇B))))⟩

/-! ## The Box-Inverse / Diamond-Inverse Identity -/

/-- **`boxInv T ⊆ H ↔ T ⊆ diaInv H`** for quasi-prime `H`, `T`. `→` is `bBox`; `←` is `bDia`.
Pacheco (`Pacheco2024`, chunk `01990319adea2569`) defines the `CKB` canonical relation as
`Γ ∼c ∆ iff Γ□ ⊆ ∆ and ∆ ⊆ Γ♦` — a **diamond**-inverse containment on the right, where the
symmetric tail (Phase 5) uses a **box**-inverse containment (`boxInv t ⊆ H`). This lemma shows
the two are the *same relation* over `CS5`: `cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧
boxInv t ⊆ H}` and Pacheco's `∼c` coincide, and his Lemma 15 ("`∼c` is symmetric") is `cs5Tail`'s
definitional symmetry with the equivalence inlined. Transcribed from `probes/cs5-tail-probe.lean`
(verified, axiom-free). `diaInv` is defined at `Segment.lean:106`. -/
theorem cs5_boxInv_subset_iff {H T : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) (hT : QuasiPrime (@CS5ModalAxiom Atom) T) :
    boxInv T ⊆ H ↔ T ⊆ diaInv H := by
  constructor
  · intro h A hA
    exact h (mem_head_mp hT.closed (mem_of_axiom hT.closed (CS5ModalAxiom.bBox A)) hA)
  · intro h B hB
    exact mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.bDia B)) (h hB)

/-! ## The Symmetric Tail

**Plan-ordering note (task 509 Phase 5)**: the plan's Phase 5 task list additionally includes
`cs5Seg`/`CS5Segment`/`cs5Mreach`/`CS5Segment.ofHead`/`cs5Val`/`cs5Bot` and the upward-closure
lemmas. Building those requires a proof of `cs5Seg`'s `CKSegment.diam_witness` field
(`∀ A, ◇A ∈ head → ∃ t ∈ tail, A ∈ t`), which is exactly `cs5_diam_witness` — the deliverable of
Phase 6, not yet available at this point. (Unlike `CS4.lean`'s `cs4Seg`, which discharges
`diam_witness` inline from the *pre-existing* `dia_refuting_theory`, `CS5` has no such
pre-existing ingredient; `cs5_diam_witness` is exactly what Phase 6 builds.) This is a genuine
dependency-ordering correction relative to the plan's literal Phase 5 task list (whose own
dependency table has Phase 6 depending on Phase 5, not vice versa): the segment-type
declarations below are landed immediately after `cs5_diam_witness` (Phase 6), not in this
section. Everything in this section is independent of `CS5Segment` and is fully landed now. -/

/-- `□B ∈ H → □□B ∈ H` — axiom `4` (box form). Transcribed from `probes/cs5-tail-probe.lean`
(verified, axiom-free). -/
theorem cs5_box_four {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    {B : Proposition Atom} (h : Proposition.box B ∈ H) :
    Proposition.box (Proposition.box B) ∈ H :=
  mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.fourBox B)) h

/-- `boxInv H ⊆ H` — axiom `T` (box form). Transcribed from `probes/cs5-tail-probe.lean`
(verified, axiom-free). -/
theorem cs5_boxInv_subset {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) : boxInv H ⊆ H :=
  fun B hB => mem_head_mp hH.closed (mem_of_axiom hH.closed (CS5ModalAxiom.tBox B)) hB

/-- **The `CS5` symmetric tail.** `boxInv H ⊆ t` is the ordinary tail-membership clause
(`cs4Tail`'s analogue); `boxInv t ⊆ H` is the clause that makes symmetry *definitional*
(`cs5Tail_symm`, below) rather than derived. This clause is **not** a design choice:
`fcbdia_forces_symmetry` (below) shows every `bDia`-adequate frame condition forces it on any
segment-based world type. Note `CS5` needs **no** `E`/exclusion parameter, unlike `cs4Tail` —
the tail is determined by the head alone. Transcribed from `probes/cs5-tail-probe.lean`
(verified). -/
def cs5Tail (H : Set (Proposition Atom)) : Set (Set (Proposition Atom)) :=
  {t | QuasiPrime (@CS5ModalAxiom Atom) t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}

/-- **Reflexivity**: `H ∈ cs5Tail H`, from `tBox` on both clauses. Transcribed from
`probes/cs5-tail-probe.lean` (verified, axiom-free). -/
theorem cs5Tail_refl {H : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H) :
    H ∈ cs5Tail H :=
  ⟨hH, cs5_boxInv_subset hH, cs5_boxInv_subset hH⟩

/-- **Symmetry, definitional.** The two tail clauses simply swap. No axiom, no maximality,
nothing derived — this is the step task 508 called "the known-hard core of constructive `S5`
canonical completeness". Hard gate (task 509): must report **no axiom dependencies at all**.
Transcribed from `probes/cs5-tail-probe.lean` (verified, axiom-free). -/
theorem cs5Tail_symm {H T : Set (Proposition Atom)} (hH : QuasiPrime (@CS5ModalAxiom Atom) H)
    (h : T ∈ cs5Tail H) : H ∈ cs5Tail T :=
  ⟨hH, h.2.2, h.2.1⟩

/-- **Transitivity.** Uses `cs5_box_four` on each side: forward, `□B ∈ H → □□B ∈ H → □B ∈ U →
B ∈ T`; backward, `□B ∈ T → □□B ∈ T → □B ∈ U → B ∈ H`. Transcribed from
`probes/cs5-tail-probe.lean` (verified, axiom-free). -/
theorem cs5Tail_trans {H U T : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) (hT : QuasiPrime (@CS5ModalAxiom Atom) T)
    (h1 : U ∈ cs5Tail H) (h2 : T ∈ cs5Tail U) : T ∈ cs5Tail H :=
  ⟨hT,
   fun _B hB => h2.2.1 (h1.2.1 (cs5_box_four hH hB)),
   fun _B hB => h1.2.2 (h2.2.2 (cs5_box_four hT hB))⟩

/-- **`Set.univ`-freeness is free.** `boxInv Set.univ = Set.univ`, so an exploding tail member
forces an exploding head. Hence for every consistent head the symmetric tail contains no
exploding member — with **no** appeal to `cs5_dia_bot_imp_bot` (task 508's nominated "one
lead", which turned out to be unnecessary). This is what voids 508's canonical refutation of
`FCbdia` (which took `u := cexpl ∈ w.tail` for consistent `w`). Transcribed from
`probes/cs5-tail-probe.lean` (verified, axiom-free). -/
theorem cs5Tail_univ_free {H : Set (Proposition Atom)}
    (h : (Set.univ : Set (Proposition Atom)) ∈ cs5Tail H) : H = Set.univ :=
  Set.eq_univ_of_univ_subset (fun _B _ => h.2.2 (Set.mem_univ _))

/-- **The truth lemma's diamond-backward case is free.** If any member of `H`'s symmetric tail
contains `A`, then `◇A ∈ H` — by `bBox` (`A → □◇A`) and the `boxInv t ⊆ H` clause. So `◇A ∉ H`
refutes `◇A` at `H` *itself* (take the witness world `:= H`, no separate refuting segment
needed). Consequence: `CS5` needs **no** exclusion parameter, no `cs5Tail` `E` argument, no
`dia_refuting_theory`, no `diamRefutingSegment` — all of which `CS4` required. The tail is
determined by the head alone, which is exactly what makes symmetry definitional. Transcribed
from `probes/cs5-tail-probe.lean` (verified, axiom-free). -/
theorem cs5Tail_dia_of_mem {H T : Set (Proposition Atom)}
    (hT : QuasiPrime (@CS5ModalAxiom Atom) T) (h : T ∈ cs5Tail H)
    {A : Proposition Atom} (hA : A ∈ T) : (◇A) ∈ H :=
  h.2.2 (mem_head_mp hT.closed (mem_of_axiom hT.closed (CS5ModalAxiom.bBox A)) hA)

/-- **Any frame condition adequate for `bDia` forces the canonical tail to be symmetric.**
`FCbdia` (`r w u → ∃ u' ≥ u, ∃ t, r u' t ∧ t ≤ w`) is the *minimal* requirement for `bDia`
(`◇□A → A`): forcing `A` at `w` is only obtainable by persistence from some `t ≤ w`. On any
segment-based world type, `FCbdia` implies `boxInv u.head ⊆ w.head` whenever `r w u` — because
`box_reflect` gives `boxInv u'.head ⊆ t.head` and `t ≤ w` gives `t.head ⊆ w.head`. So the
symmetric tail is not one design among many: it is *forced*. Task 508 read this as an
obstruction; it is in fact a specification. Transcribed from `probes/cs5-canonical-probe.lean`
(verified, axiom-free). -/
theorem fcbdia_forces_symmetry {Axioms : Proposition Atom → Prop}
    {w u : CKSegment Axioms} (hru : cmreach w u)
    (hfc : ∀ {w u : CKSegment Axioms}, cmreach w u →
      ∃ u', u ≤ u' ∧ ∃ t, cmreach u' t ∧ t ≤ w) :
    boxInv u.head ⊆ w.head := by
  obtain ⟨u', hle, t, hrt, htw⟩ := hfc hru
  intro B hB
  exact htw (u'.box_reflect B (hle hB) t.head hrt)

/-- **The remaining gap, mechanized.** In the symmetric tail
`cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}`, if `□(p ∨ □q) ∈ H` and `q ∉ H`,
then **every** tail member `T` of `H` contains `p`.

Consequence: for `H` prime with `□(p ∨ □q) ∈ H`, `□p ∉ H`, `q ∉ H`, the truth lemma's
box-backward case has **no** witness at `H` itself — no `T` in `H`'s symmetric tail omits `p`.
The box-backward case must therefore move to a strictly larger head `H' ⊇ H` (here: one
containing `q`), which enlarges `boxInv H'` in turn. That circularity is the real open problem:
`H'` and `T` must be built as a simultaneous maximal pair, not sequentially (Phases 8-10).

This argument is purely structural — it uses only primality of `T` and the two tail clauses, no
`CS5` axiom. It therefore applies to every symmetric-tail design, and by `fcbdia_forces_symmetry`
the tail must be symmetric. Transcribed from `probes/cs5-canonical-probe.lean` (verified,
axiom-free). -/
theorem cs5_symmetric_tail_box_gap {H T : Set (Proposition Atom)}
    (hT : QuasiPrime (@CS5ModalAxiom Atom) T) {p q : Proposition Atom}
    (hbox : Proposition.box (p.or (Proposition.box q)) ∈ H)
    (hsub : boxInv H ⊆ T) (hsym : boxInv T ⊆ H) (hq : q ∉ H) : p ∈ T := by
  rcases hT.disj (hsub hbox) with h | h
  · exact h
  · exact absurd (hsym h) hq

end Cslib.Logic.Modal
