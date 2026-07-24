/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic K

This module proves completeness for modal logic K via the canonical Kripke model
construction, following Blackburn, de Rijke, Venema "Modal Logic" (2002), Theorem 4.23.

The K-specific Existence Lemma (BRV Lemma 4.20) and Truth Lemma (BRV Lemma 4.21) are supplied
generically by `Metalogic.Completeness`'s single `SchemaUnion`-parametric route (every classical
system's axiom predicate is `SchemaUnion sysTags` with `kCore ⊆ sysTags`); this module wires that
generic route to `KAxiom` via `k_truth_lemma_applied` below and derives K's soundness,
completeness, and compactness theorems from it.

## Main Results

- `k_truth_lemma_applied`: the generic truth lemma applied to `KAxiom`.
- `k_strong_soundness`, `k_strong_completeness`, `k_strong_completeness_iff`: strong
  soundness/completeness for K.
- `k_compactness`: compactness for K semantics.
- `k_completeness`: the weak completeness theorem, derived as a corollary of strong
  completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.20-4.23)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-- Pre-applied K truth lemma: satisfaction at world `S` iff membership in `S.val`.

Used by K-family systems (B, K4, K5, K45, KB5) to delegate completeness proofs to
the parametric `strong_completeness` via this shared pre-applied truth lemma.

The generic box-witness machinery and truth lemma body live in `Metalogic.Completeness` as THE
single generic `truth_lemma` route: every one of the 15 classical systems' axiom predicates is
`SchemaUnion sysTags` with `kCore ⊆ sysTags`, so one generic route serves all of them; this file
only wires that generic lemma to `KAxiom`. -/
theorem k_truth_lemma_applied (S : CanonicalWorld (@KAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@KAxiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ kTags`: K's tag set is `kCore` alone. Feeds the `holds*` helpers so every
`*_strong_completeness`/`*_compactness`/`*_completeness` call site below shares this single
subset fact instead of repeating 4 `by decide` witnesses each. -/
private theorem coreSubset : kCore ⊆ kTags := by decide

/-- K soundness adapter matching the `strong_soundness` callback shape.
The frame condition for K is trivial (`fun _ => True`), so the hypothesis is discarded. -/
private theorem k_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (_ : (fun (_ : Model World Atom) => True) m)
    (d : DerivationTree (@KAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  k_soundness d m w h_ctx

/-! ## K Strong Soundness -/

/-- **Strong Soundness for K**: If `phi` is set-derivable from `Gamma` using `KAxiom`,
then `phi` is a semantic consequence of `Gamma` over all frames.

Delegates to the parametric `strong_soundness` with `k_sound_cb`. -/
theorem k_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@KAxiom Atom) Gamma phi) :
    ModalSemanticEntails (fun _ => True) Gamma phi :=
  (strong_completeness_iff (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k_truth_lemma_applied
    trivial).mpr h

/-! ## K Strong Completeness -/

/-- **Strong Completeness for K**: If `phi` is a semantic consequence of `Gamma`
over all frames, then `phi` is set-derivable from `Gamma` using `KAxiom`.

Delegates to the parametric `strong_completeness` with K-specific callbacks. -/
theorem k_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails (fun _ => True) Gamma phi) :
    ModalSetDerivable (@KAxiom Atom) Gamma phi :=
  (strong_completeness_iff (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k_truth_lemma_applied
    trivial).mp h

/-! ## K Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K**:
`phi` is a semantic consequence of `Gamma` over all frames iff `phi` is
set-derivable from `Gamma` using `KAxiom`.

Delegates to the parametric `strong_completeness_iff`. -/
theorem k_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    ModalSemanticEntails (fun _ => True) Gamma phi ↔
    ModalSetDerivable (@KAxiom Atom) Gamma phi :=
  strong_completeness_iff (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k_truth_lemma_applied
    trivial

/-! ## K Compactness -/

/-- **Compactness for K Semantics**: If `phi` is a semantic consequence of `Gamma`
over all frames, there exists a finite list `L ⊆ Gamma` such that `phi` is a
semantic consequence of (members of) `L` over all frames.

Delegates to the parametric `compactness`. -/
theorem k_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails (fun _ => True) Gamma phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ModalSemanticEntails (fun _ => True) {ψ | ψ ∈ L} phi :=
  compactness (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k_truth_lemma_applied
    trivial
    h

/-! ## K Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic K** (corollary of strong completeness):

If `phi` is valid over all frames (no frame conditions), then `phi`
is K-derivable from the empty context.

Delegates to the parametric `weak_completeness`. -/
theorem k_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      ∀ w, Satisfies m w φ) :
    Derivable (@KAxiom Atom) φ :=
  weak_completeness (Axioms := @KAxiom Atom) (FC := fun _ => True)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k_truth_lemma_applied
    trivial
    (fun W m _ w => h_valid W m w)

end Cslib.Logic.Modal
