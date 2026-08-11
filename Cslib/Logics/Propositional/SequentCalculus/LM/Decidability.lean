/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LM.Completeness
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Decidability
public import Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure

/-! # Decidability of Minimal Propositional Logic via LM

This module proves that LM derivability of sequents `Γ ⊢ A` is decidable for finite contexts
`Γ` of propositions over a decidable, hashable atom type, matching the LJ decidability surface
(`LJ/Decidability.lean`).

## Strategy

Structural template: `instDecidableLJDerivable`. The same deduction-theorem route is used,
reusing the generic `seqListDeductionFwd`/`seqListDeductionBwd`/`listToImp`/`ctxToImp`
machinery from `LJ/Decidability.lean` (generalised over an arbitrary theory `T` there) rather
than duplicating it, and instantiating at `T = MPL` (`SeqProofMinimal := SeqProof MPL`):

1. Reduce `Nonempty (SeqProofMinimal (Γ ⊢ A))` to `Nonempty (SeqProofMinimal (∅ ⊢ ctxToImp Γ A))`
   via the generic deduction lemmas at `T = MPL`.
2. Combine with `lm_iff_mvalid` to reduce to `MValid (ctxToImp Γ A)`, which is decidable via
   `instDecidableMValid` from the minimal tableau (routed through `mvalid_universe_invariant` to
   bridge `instDecidableMValid`'s `Type 0` pin to the unpinned universe `lm_iff_mvalid` needs).
3. As with the LJ instance, make the resulting `Decidable` instance computable by sidestepping
   `ctxToImp` at the instance level: `lmListDerivableDecidable` proves the same equivalence at
   the *list* level (computable), and `instDecidableLMDerivable` eliminates `Γ`'s underlying
   `Multiset` into it via `Quotient.recOnSubsingleton`.

## Main Results

- `lmListDerivableDecidable`: List-level decidability helper, computable, used to build
  `instDecidableLMDerivable` via `Quotient.recOnSubsingleton`.
- `instDecidableLMDerivable`: `Decidable (Nonempty (SeqProofMinimal (Γ ⊢ A)))`.
- `instDecidableDerivableInMPL`:
  `Decidable (DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ A))`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition InferenceSystem

variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]

/-! ## Decidability Instances -/

/-- List-level decidability of LM derivability from a `Nodup` list context.

Given a `Nodup` list `l` and the proof `h` that its coercion to a `Multiset` is `Nodup`, decides
`Nonempty (SeqProofMinimal ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ A))` by routing through
`MValid (listToImp l A)`, mirroring `ljListDerivableDecidable`: `listToImp` applied to a
concrete list needs no choice of representative, so this helper is computable.
`instDecidableLMDerivable` builds on this helper via `Quotient.recOnSubsingleton`, applying it
to an arbitrary representative of `Γ`'s underlying `Multiset`; the resulting *decision* is
representative-independent because `Decidable p` is a `Subsingleton`.

**Universe note.** `instDecidableMValid` (from `Minimal/DecisionProcedure.lean`) is pinned to
`MValid.{_, 0}`, while `lm_iff_mvalid` needs `MValid.{u, u}` (`u` = `Atom`'s own universe). The
local `letI` below routes through `mvalid_universe_invariant` -- the same bridge
`instDecidableDerivableMinPropAxiom` uses -- to recover an unpinned `Decidable (MValid _)`
instance before `decidable_of_iff` is applied, exactly mirroring
`LJ/Decidability.lean`'s `ljListDerivableDecidable` pattern. -/
def lmListDerivableDecidable (l : List (Proposition Atom))
    (h : (↑l : Multiset (Proposition Atom)).Nodup) (A : Proposition Atom) :
    Decidable (Nonempty (SeqProofMinimal ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ A))) :=
  letI : Decidable (MValid (listToImp l A)) :=
    decidable_of_iff (MValid.{_, 0} (listToImp l A)) (mvalid_universe_invariant _).symm
  decidable_of_iff (MValid (listToImp l A)) <| by
    have hset : (⟨(↑l : Multiset (Proposition Atom)), h⟩ : Finset (Proposition Atom))
        = l.toFinset := List.toFinset_eq h
    rw [hset]
    constructor
    · -- MValid (listToImp l A) → Nonempty (SeqProofMinimal (l.toFinset ⊢ A))
      intro hv
      obtain ⟨d⟩ := lm_iff_mvalid.mp hv
      have hd := seqListDeductionBwd l ∅ A d
      rw [Finset.union_empty] at hd
      exact ⟨hd⟩
    · -- Nonempty (SeqProofMinimal (l.toFinset ⊢ A)) → MValid (listToImp l A)
      rintro ⟨d⟩
      refine lm_iff_mvalid.mpr ⟨seqListDeductionFwd l ∅ A ?_⟩
      rw [Finset.union_empty]
      exact d

/-- `Nonempty (SeqProofMinimal (Γ ⊢ A))` is decidable for finite contexts over decidable,
hashable atoms.

The instance eliminates `Γ`'s underlying `Multiset` via `Quotient.recOnSubsingleton` into
`lmListDerivableDecidable`, applied to an arbitrary list representative `l` of `Γ.val` with
`Γ.nodup` as the `Nodup` witness. Since `Decidable p` is a `Subsingleton`, the elimination is
sound, and, because `lmListDerivableDecidable` is itself computable, so is this instance. -/
instance instDecidableLMDerivable {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (Nonempty (SeqProofMinimal (Γ ⊢ A))) :=
  Quotient.recOnSubsingleton (motive := fun (s : Multiset (Proposition Atom)) =>
      (h : s.Nodup) →
        Decidable (Nonempty (SeqProofMinimal ((⟨s, h⟩ : Finset (Proposition Atom)) ⊢ A))))
    Γ.val (fun l h => lmListDerivableDecidable l h A) Γ.nodup

/-- `DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ A)` is decidable for finite contexts
over decidable, hashable atoms.

Obtained by combining `instDecidableLMDerivable` with the ND–LM bridge `nd_iff_lm`. -/
instance instDecidableDerivableInMPL {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (SeqProofMinimal (Γ ⊢ A))) nd_iff_lm.symm

end Cslib.Logic.PL

end
