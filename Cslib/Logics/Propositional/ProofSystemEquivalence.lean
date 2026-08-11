/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness
public import Cslib.Logics.Propositional.SequentCalculus.LM.Completeness
public import Mathlib.Data.List.TFAE
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure
public import Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure
public import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
import Mathlib.Tactic.TFAE

/-! # Proof System Equivalences for Propositional Logic

This module collects equivalences between the Hilbert-style proof system, natural deduction
(ND), sequent calculus, and (at the empty context) the tableau decision procedure and
algebraic semantics, for classical (CPL), intuitionistic (IPL), and minimal (MPL)
propositional logic, stated as `List.TFAE` theorems. All three logic strengths have a
three-way equivalence at both the context-based and closed-formula levels, and the
closed-formula equivalences additionally carry two independent fourth nodes — the tableau
decision procedure and algebraic (Boolean/Heyting/generalized-Heyting-algebra) validity —
making the proof-system × logic matrix structurally symmetric.

## Main Results

- `cplProofSystemsTfae`: CPL three-way equivalence (Hilbert, ND, LK), context-based.
- `cplProofSystemsTfaeClosed`: CPL three-way equivalence at the empty context.
- `iplProofSystemsTfae`: IPL three-way equivalence (Hilbert, ND, LJ), context-based.
- `iplProofSystemsTfaeClosed`: IPL three-way equivalence at the empty context.
- `mplProofSystemsTfae`: MPL three-way equivalence (Hilbert, ND, LM), context-based.
- `mplProofSystemsTfaeClosed`: MPL three-way equivalence at the empty context.
- `mplHilbertIffNd`: MPL two-way equivalence (Hilbert ↔ ND), context-based (retained for
  backward compatibility; superseded but not replaced by `mplProofSystemsTfae`).
- `cplProofSystemsWithTableauTfae`: CPL four-way equivalence (Hilbert, ND, LK, tableau) at the
  empty context.
- `iplProofSystemsWithTableauTfae`: IPL four-way equivalence (Hilbert, ND, LJ, tableau) at the
  empty context.
- `mplProofSystemsWithTableauTfae`: MPL four-way equivalence (Hilbert, ND, LM, tableau) at the
  empty context.
- `cplProofSystemsWithAlgebraTfae`: CPL four-way equivalence (Hilbert, ND, LK, Boolean-algebra
  validity) at the empty context.
- `iplProofSystemsWithAlgebraTfae`: IPL four-way equivalence (Hilbert, ND, LJ, Heyting-algebra
  validity) at the empty context.
- `mplProofSystemsWithAlgebraTfae`: MPL four-way equivalence (Hilbert, ND, LM,
  generalized-Heyting-algebra validity) at the empty context.

## Dependencies

The proofs are purely compositional, relying on existing bridge theorems:
- `hilbert_iff_nd_ctx_cl`, `nd_iff_lk` (LK completeness)
- `hilbert_iff_nd_ctx_int`, `nd_iff_lj` (LJ completeness)
- `hilbert_iff_nd_ctx_min`, `nd_iff_lm` (LM completeness)
- `prop_completeness_iff_tautology`, `classicalTableau_decides` (CPL tableau fold)
- `int_soundness_completeness`, `ivalid_universe_invariant`, `intuitionisticTableau_decides`
  (IPL tableau fold)
- `min_soundness_completeness`, `mvalid_universe_invariant`, `minimalTableau_decides`
  (MPL tableau fold)
- `CPL.hilbert_alg_completeness`, `IPL.hilbert_alg_completeness`, `MPL.hilbert_alg_completeness`
  (algebraic folds)
-/

@[expose] public section

namespace Cslib.Logic.PL

open InferenceSystem Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom]

universe u

/-! ## Classical Propositional Logic (CPL) -/

/-- **CPL Three-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
the following are equivalent:
1. Hilbert derivability: `Deriv PropositionalAxiom Γ.toList φ`
2. ND derivability: `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ φ)`
3. LK provability: `Nonempty (LKProof (Γ ⊢ₛ {φ}))`

Proved by composing `hilbert_iff_nd_ctx_cl` (1 ↔ 2) and `nd_iff_lk` (2 ↔ 3). -/
theorem cplProofSystemsTfae (Γ : Ctx Atom) (φ : PL.Proposition Atom) :
    [Deriv PropositionalAxiom Γ.toList φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom) (Γ ⊢ φ),
     Nonempty (LKProof (Γ ⊢ₛ ({φ} : Finset _)))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_cl
  tfae_have 2 ↔ 3 := nd_iff_lk
  tfae_finish

/-- **CPL Three-Way Equivalence** (closed): At the empty context, the following are equivalent:
1. Hilbert derivability: `Derivable PropositionalAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)`
3. LK provability: `Nonempty (LKProof (∅ ⊢ₛ {φ}))`

Obtained from `cplProofSystemsTfae` at `Γ = ∅` via `Finset.toList_empty`. -/
theorem cplProofSystemsTfaeClosed (φ : PL.Proposition Atom) :
    [Derivable PropositionalAxiom φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LKProof ((∅ : Ctx Atom) ⊢ₛ ({φ} : Finset _)))].TFAE := by
  have h := cplProofSystemsTfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h

/-! ## Intuitionistic Propositional Logic (IPL) -/

/-- **IPL Three-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
the following are equivalent:
1. Hilbert derivability: `Deriv IntPropAxiom Γ.toList φ`
2. ND derivability: `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ φ)`
3. LJ provability: `Nonempty (LJProof (Γ ⊢ φ))`

Proved by composing `hilbert_iff_nd_ctx_int` (1 ↔ 2) and `nd_iff_lj` (2 ↔ 3). -/
theorem iplProofSystemsTfae (Γ : Ctx Atom) (φ : PL.Proposition Atom) :
    [Deriv IntPropAxiom Γ.toList φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ φ),
     Nonempty (LJProof (Γ ⊢ φ))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_int
  tfae_have 2 ↔ 3 := nd_iff_lj
  tfae_finish

/-- **IPL Three-Way Equivalence** (closed): At the empty context, the following are equivalent:
1. Hilbert derivability: `Derivable IntPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)`
3. LJ provability: `Nonempty (LJProof (∅ ⊢ φ))`

Obtained from `iplProofSystemsTfae` at `Γ = ∅` via `Finset.toList_empty`. -/
theorem iplProofSystemsTfaeClosed (φ : PL.Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ))].TFAE := by
  have h := iplProofSystemsTfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h

/-! ## Minimal Propositional Logic (MPL) -/

/-- **MPL Three-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
the following are equivalent:
1. Hilbert derivability: `Deriv MinPropAxiom Γ.toList φ`
2. ND derivability: `DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ φ)`
3. LM provability: `Nonempty (SeqProofMinimal (Γ ⊢ φ))`

Proved by composing `hilbert_iff_nd_ctx_min` (1 ↔ 2) and `nd_iff_lm` (2 ↔ 3). This makes the
MPL row structurally symmetric with the CPL (`LK`) and IPL (`LJ`) rows. -/
theorem mplProofSystemsTfae (Γ : Ctx Atom) (φ : PL.Proposition Atom) :
    [Deriv MinPropAxiom Γ.toList φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ φ),
     Nonempty (SeqProofMinimal (Γ ⊢ φ))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_min
  tfae_have 2 ↔ 3 := nd_iff_lm
  tfae_finish

/-- **MPL Three-Way Equivalence** (closed): At the empty context, the following are equivalent:
1. Hilbert derivability: `Derivable MinPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)`
3. LM provability: `Nonempty (SeqProofMinimal (∅ ⊢ φ))`

Obtained from `mplProofSystemsTfae` at `Γ = ∅` via `Finset.toList_empty`. -/
theorem mplProofSystemsTfaeClosed (φ : PL.Proposition Atom) :
    [Derivable MinPropAxiom φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (SeqProofMinimal ((∅ : Ctx Atom) ⊢ φ))].TFAE := by
  have h := mplProofSystemsTfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h

/-- **MPL Two-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
Hilbert derivability with `MinPropAxiom` from `Γ.toList` is equivalent to ND derivability
under `AxiomTheory MinPropAxiom` from `Γ`.

Retained for backward compatibility; re-exports `hilbert_iff_nd_ctx_min` for discoverability.
Superseded by the three-way `mplProofSystemsTfae`, which additionally includes LM provability. -/
theorem mplHilbertIffNd {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv MinPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx_min

/-! ## Tableau Folds (closed formulas only)

The tableau decision procedures (`classicalTableau`, `intuitionisticTableau`,
`minimalTableau`) take a single closed formula and no context argument, so each fold below
extends the corresponding `...Closed` three-way equivalence with a fourth node rather than
extending the context-based equivalence. These theorems additionally require
`[Hashable Atom]`, which the tableau algorithms need for their internal branch bookkeeping;
that constraint is scoped to this section alone so the six equivalences above, which are pure
proof-theoretic statements, are not forced to carry it. -/

section WithTableau

variable [Hashable Atom]

omit [Hashable Atom] in
/-- **CPL Four-Way Equivalence** (closed, with tableau): At the empty context, the following
are equivalent:
1. Hilbert derivability: `Derivable PropositionalAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)`
3. LK provability: `Nonempty (LKProof (∅ ⊢ₛ {φ}))`
4. Tableau closure: `classicalTableau φ = .closed`

Nodes 1-3 are `cplProofSystemsTfaeClosed`. Node 1 ↔ 4 composes
`prop_completeness_iff_tautology` (`Tautology φ ↔ Derivable PropositionalAxiom φ`) with
`classicalTableau_decides` (`classicalTableau φ = .closed ↔ Tautology φ`); CPL has no universe
parameter, so this composition closes by `rw`. Unlike the IPL/MPL folds below,
`classicalTableau` only requires `[DecidableEq Atom]`, not `[Hashable Atom]`, so this theorem
omits the section's `[Hashable Atom]` variable. -/
theorem cplProofSystemsWithTableauTfae (φ : PL.Proposition Atom) :
    [Derivable PropositionalAxiom φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LKProof ((∅ : Ctx Atom) ⊢ₛ ({φ} : Finset _))),
     classicalTableau φ = .closed].TFAE := by
  have h := cplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := by
    rw [← prop_completeness_iff_tautology, ← classicalTableau_decides]
  tfae_finish

/-- **IPL Four-Way Equivalence** (closed, with tableau): At the empty context, the following
are equivalent:
1. Hilbert derivability: `Derivable IntPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)`
3. LJ provability: `Nonempty (LJProof (∅ ⊢ φ))`
4. Tableau closure: `intuitionisticTableau φ = .closed`

Nodes 1-3 are `iplProofSystemsTfaeClosed`. Node 1 ↔ 4 composes `int_soundness_completeness`
(`IValid.{u,u} φ ↔ Derivable IntPropAxiom φ`) with `ivalid_universe_invariant`
(`IValid.{_,v} φ ↔ IValid.{_,0} φ`) and `intuitionisticTableau_decides`
(`intuitionisticTableau φ = .closed ↔ IValid.{_,0} φ`). The universe-invariance step cannot be
discharged by `rw` — it leaves an unsolvable universe metavariable — so the composition is
built in term mode via `Iff.trans`. -/
theorem iplProofSystemsWithTableauTfae (φ : PL.Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ)),
     intuitionisticTableau φ = .closed].TFAE := by
  have h := iplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := by
    exact int_soundness_completeness.symm.trans
      ((ivalid_universe_invariant φ).trans (intuitionisticTableau_decides φ).symm)
  tfae_finish

/-- **MPL Four-Way Equivalence** (closed, with tableau): At the empty context, the following
are equivalent:
1. Hilbert derivability: `Derivable MinPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)`
3. LM provability: `Nonempty (SeqProofMinimal (∅ ⊢ φ))`
4. Tableau closure: `minimalTableau φ = .closed`

Nodes 1-3 are `mplProofSystemsTfaeClosed`. Node 1 ↔ 4 composes `min_soundness_completeness`
with `mvalid_universe_invariant` and `minimalTableau_decides`, the exact MPL analogue of the
IPL fold above (same `rw`-vs-`Iff.trans` gotcha, same reason). -/
theorem mplProofSystemsWithTableauTfae (φ : PL.Proposition Atom) :
    [Derivable MinPropAxiom φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (SeqProofMinimal ((∅ : Ctx Atom) ⊢ φ)),
     minimalTableau φ = .closed].TFAE := by
  have h := mplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := by
    exact min_soundness_completeness.symm.trans
      ((mvalid_universe_invariant φ).trans (minimalTableau_decides φ).symm)
  tfae_finish

end WithTableau

/-! ## Algebraic Semantics Folds (closed formulas only)

The algebraic validity predicates `GHAValid`, `HAValid`, and `BAValid`
(`Semantics/Algebra.lean`) are weak — empty-context — notions of validity, so each fold below
extends the corresponding `...Closed` three-way equivalence rather than the context-based one.

A context-based algebraic node was considered and deliberately not added. Strong algebraic
completeness exists (`hilbert_alg_strong_complete_theory`), but it quantifies over
*generalized* Heyting algebras for all three logics, distinguishing them only by the axiom
theory the valuation models; the tier-matched form (Boolean algebras for CPL, Heyting algebras
for IPL) would need `HeytingAlgebra`/`BooleanAlgebra` instances on `RelLindenbaumAlgebra`,
which carries only a `GeneralizedHeytingAlgebra` instance. A non-tier-matched context node
would break the parallel with the closed nodes below, so the algebraic node lives on the closed
families alone.

Unlike `section WithTableau`, these theorems need no extra typeclass; the constraint is a
universe pin. `GHAValid`/`HAValid`/`BAValid` carry a second universe for the algebra carrier,
and the Hilbert Lindenbaum construction pins it to `Atom`'s universe, so each theorem binds
`{Atom : Type u}` explicitly instead of using the file-level `Type*` variable. There is no
universe-invariance lemma for algebraic validity (contrast `ivalid_universe_invariant`), so the
`.{u, u}` pin is part of the statement. -/

section WithAlgebra

/-- **CPL Four-Way Equivalence** (closed, with algebraic semantics): At the empty context, the
following are equivalent:
1. Hilbert derivability: `Derivable PropositionalAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)`
3. LK provability: `Nonempty (LKProof (∅ ⊢ₛ {φ}))`
4. Boolean-algebra validity: `BAValid.{u, u} φ`

Nodes 1-3 are `cplProofSystemsTfaeClosed`. Node 1 ↔ 4 is `CPL.hilbert_alg_completeness`. -/
theorem cplProofSystemsWithAlgebraTfae {Atom : Type u} [DecidableEq Atom]
    (φ : PL.Proposition Atom) :
    [Derivable PropositionalAxiom φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LKProof ((∅ : Ctx Atom) ⊢ₛ ({φ} : Finset _))),
     BAValid.{u, u} φ].TFAE := by
  have h := cplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := CPL.hilbert_alg_completeness
  tfae_finish

/-- **IPL Four-Way Equivalence** (closed, with algebraic semantics): At the empty context, the
following are equivalent:
1. Hilbert derivability: `Derivable IntPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)`
3. LJ provability: `Nonempty (LJProof (∅ ⊢ φ))`
4. Heyting-algebra validity: `HAValid.{u, u} φ`

Nodes 1-3 are `iplProofSystemsTfaeClosed`. Node 1 ↔ 4 is `IPL.hilbert_alg_completeness`. -/
theorem iplProofSystemsWithAlgebraTfae {Atom : Type u} [DecidableEq Atom]
    (φ : PL.Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ)),
     HAValid.{u, u} φ].TFAE := by
  have h := iplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := IPL.hilbert_alg_completeness
  tfae_finish

/-- **MPL Four-Way Equivalence** (closed, with algebraic semantics): At the empty context, the
following are equivalent:
1. Hilbert derivability: `Derivable MinPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)`
3. LM provability: `Nonempty (SeqProofMinimal (∅ ⊢ φ))`
4. Generalized-Heyting-algebra validity: `GHAValid.{u, u} φ`

Nodes 1-3 are `mplProofSystemsTfaeClosed`. Node 1 ↔ 4 is `MPL.hilbert_alg_completeness`. -/
theorem mplProofSystemsWithAlgebraTfae {Atom : Type u} [DecidableEq Atom]
    (φ : PL.Proposition Atom) :
    [Derivable MinPropAxiom φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (SeqProofMinimal ((∅ : Ctx Atom) ⊢ φ)),
     GHAValid.{u, u} φ].TFAE := by
  have h := mplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := MPL.hilbert_alg_completeness
  tfae_finish

end WithAlgebra

end Cslib.Logic.PL

end
