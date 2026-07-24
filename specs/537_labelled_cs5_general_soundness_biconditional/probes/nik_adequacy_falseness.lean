/-
SCRATCH PROBE -- NOT part of the Cslib library tree, not imported by anything.

Purpose: machine-check the claim in reports/05 that the intended
  `nik_adequacy : IsDerivationForest G → NIK TS5 G Γ (x ∶ A) → Derivable CS5ModalAxiom (nikTr G Γ hfin x A)`
is MATHEMATICALLY FALSE against the landed target-oriented `nikTr`.

Method: assume the statement as a hypothesis and derive `False` from it, using only
landed, sorry-free library facts (`cs5_consistent_incest`).
-/
import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness

open Cslib.Logic.Modal
open Cslib.Logic.Modal.Labelled

namespace Probe537

/-! ### The concrete witness data -/

/-- The trivial graph over `ℕ` atoms: `X = {var 0}`, `R = ∅`. -/
noncomputable abbrev Gt : Graph ℕ := Graph.trivial ℕ

theorem Gt_fin : (Gt).X.Finite := Set.finite_singleton _

/-- The root, which IS in `Gt.X`. -/
abbrev r : Label ℕ := Label.var 0

/-- A DISCONNECTED label: `y ∉ Gt.X`, no edges touching it. -/
abbrev yy : Label ℕ := Label.var 1

/-- Context asserting `⊥` at the (in-graph) root. -/
abbrev Ctx : List (LabelledFormula ℕ) := [(r ∶ Proposition.bot)]

/-! ### Step 1: the `NIK` derivation really exists -/

/-- `Ctx ⊢ yy ∶ ⊥` in `N(TS5)` over the trivial graph, via `assumption` + cross-label `efq`.
Note `yy ∉ Gt.X`: `NIK.efq` places NO constraint on the conclusion label. -/
theorem nik_deriv : NIK TS5 Gt Ctx (yy ∶ Proposition.bot) :=
  .efq Gt Ctx r yy Proposition.bot (.assumption Gt Ctx (r ∶ Proposition.bot) (by simp))

/-- The graph is a derivation forest (so the invariant does not exclude this instance). -/
theorem gt_forest : IsDerivationForest Gt := forest_trivial

/-! ### Step 2: the translation drops everything -/

/-- No node has an `R`-edge in the trivial graph. -/
theorem no_edges (a b : Label ℕ) : ¬ Gt.R a b := fun h => h

/-- `yy` carries no `Ctx`-facts (the only fact sits at `r ≠ yy`). -/
theorem facts_yy : factsAt Ctx yy = [] := by
  simp [factsAt, Label.var.injEq]

/-- `bigAndL []` is a CS5 theorem. -/
theorem bigAndL_nil_deriv :
    Derivable CS5ModalAxiom (bigAndL ([] : List (Proposition ℕ))) := by
  simpa [bigAndL] using cs5_deriv_imp_self (Proposition.bot : Proposition ℕ)

/-- Conjunction introduction on closed theorems. -/
theorem deriv_and {P Q : Proposition ℕ} (hP : Derivable CS5ModalAxiom P)
    (hQ : Derivable CS5ModalAxiom Q) : Derivable CS5ModalAxiom (P.and Q) := by
  obtain ⟨dP⟩ := hP
  obtain ⟨dQ⟩ := hQ
  exact ⟨.modus_ponens [] _ _ (.modus_ponens [] _ _ (.ax [] _ (.andI P Q)) dP) dQ⟩

/-- **The subtree translation at the disconnected label is a tautology**: for EVERY fuel `n`,
`sigAtFuel Gt Ctx _ n yy` is CS5-derivable, because `yy` has no children and no `Ctx`-facts. -/
theorem sigAtFuel_yy_deriv (n : ℕ) :
    Derivable CS5ModalAxiom (sigAtFuel Gt Ctx Gt_fin n yy) := by
  cases n with
  | zero => simpa [sigAtFuel, facts_yy] using bigAndL_nil_deriv
  | succ n =>
      have hempty : {c | Gt.R yy c} = (∅ : Set (Label ℕ)) := by
        ext c; simp [no_edges]
      have : sigAtFuel Gt Ctx Gt_fin (n + 1) yy
          = Proposition.and (bigAndL (factsAt Ctx yy)) (bigAndL []) := by
        rw [sigAtFuel]
        congr 1
        have hfin' : {c | Gt.R yy c}.Finite := Gt_fin.subset (fun c hc => (Gt.edge_mem yy c hc).2)
        congr 1
        simp [Set.Finite.toFinset_eq_empty.mpr hempty]
      rw [this, facts_yy]
      exact deriv_and bigAndL_nil_deriv bigAndL_nil_deriv

/-- Hence `sigAt` at the disconnected label is a CS5 theorem. -/
theorem sigAt_yy_deriv : Derivable CS5ModalAxiom (sigAt Gt Ctx Gt_fin yy) :=
  sigAtFuel_yy_deriv _

/-- **The ancestor-walk performs ZERO wraps at a disconnected label**: `nikTr` collapses to
`sigAt yy ⊃ A`, discarding `Gt` and `Ctx` entirely. -/
theorem nikTr_yy (A : Proposition ℕ) :
    nikTr Gt Ctx Gt_fin yy A = Proposition.imp (sigAt Gt Ctx Gt_fin yy) A := by
  have hroot : ¬ ∃ q, Gt.R q yy := by rintro ⟨q, hq⟩; exact hq
  simp only [nikTr, nikTrFuel, dif_neg hroot]

/-- **The exact formula the report predicts.** `nikTr` at the disconnected label is literally
`((⊥⊃⊥) ∧ (⊥⊃⊥)) ⊃ A` -- the graph `Gt` and the context `Ctx` (which asserts `r ∶ ⊥`!) have
been discarded wholesale. -/
theorem nikTr_yy_explicit (A : Proposition ℕ) :
    nikTr Gt Ctx Gt_fin yy A =
      Proposition.imp
        (Proposition.and (Proposition.imp Proposition.bot Proposition.bot)
          (Proposition.imp Proposition.bot Proposition.bot)) A := by
  have hcard : Gt_fin.toFinset.card = 1 := by
    have : Gt_fin.toFinset = {Label.var 0} := by
      ext c; simp [Gt, Graph.trivial]
    simp [this]
  have hempty : {c | Gt.R yy c} = (∅ : Set (Label ℕ)) := by ext c; simp [no_edges]
  rw [nikTr_yy, sigAt, hcard]
  congr 1
  rw [sigAtFuel, facts_yy]
  simp [bigAndL, Set.Finite.toFinset_eq_empty.mpr hempty]

/-! ### Step 3: the reductio -/

/-- **VERDICT**: the intended `nik_adequacy` statement, taken as a hypothesis in exactly the
shape plan v5 specifies (with the `IsDerivationForest` invariant available), yields `False`. -/
theorem nik_adequacy_is_false
    (nik_adequacy : ∀ (G : Graph ℕ) (Γ : List (LabelledFormula ℕ)) (hfin : G.X.Finite)
        (x : Label ℕ) (A : Proposition ℕ),
        IsDerivationForest G → NIK TS5 G Γ (x ∶ A) →
        Derivable CS5ModalAxiom (nikTr G Γ hfin x A)) : False := by
  have h := nik_adequacy Gt Ctx Gt_fin yy Proposition.bot gt_forest nik_deriv
  rw [nikTr_yy] at h
  obtain ⟨dimp⟩ := h
  obtain ⟨dsig⟩ := sigAt_yy_deriv
  exact cs5_consistent_incest ⟨.modus_ponens [] _ _ dimp dsig⟩

/-! ### Step 4: does root-connectivity rescue it?

The reductio above uses `y ∉ G.X`. Below: even a statement RESTRICTED to `x ∈ G.X`, over a
graph that is a SINGLE-ROOTED forest (`Gt` is a one-node graph, trivially rooted), is still
false -- provided the context may mention a label outside `G.X`. -/

/-- Context asserting `⊥` at an OUT-OF-GRAPH label. -/
abbrev Ctx' : List (LabelledFormula ℕ) := [(yy ∶ Proposition.bot)]

/-- `Ctx' ⊢ r ∶ ⊥` with the CONCLUSION label `r ∈ Gt.X`, on a rooted one-node forest. -/
theorem nik_deriv' : NIK TS5 Gt Ctx' (r ∶ Proposition.bot) :=
  .efq Gt Ctx' yy r Proposition.bot (.assumption Gt Ctx' (yy ∶ Proposition.bot) (by simp))

theorem facts_r' : factsAt Ctx' r = [] := by
  simp [factsAt, Label.var.injEq]

theorem sigAtFuel_r'_deriv (n : ℕ) :
    Derivable CS5ModalAxiom (sigAtFuel Gt Ctx' Gt_fin n r) := by
  cases n with
  | zero => simpa [sigAtFuel, facts_r'] using bigAndL_nil_deriv
  | succ n =>
      have hempty : {c | Gt.R r c} = (∅ : Set (Label ℕ)) := by
        ext c; simp [no_edges]
      have : sigAtFuel Gt Ctx' Gt_fin (n + 1) r
          = Proposition.and (bigAndL (factsAt Ctx' r)) (bigAndL []) := by
        rw [sigAtFuel]
        congr 1
        congr 1
        simp [Set.Finite.toFinset_eq_empty.mpr hempty]
      rw [this, facts_r']
      exact deriv_and bigAndL_nil_deriv bigAndL_nil_deriv

theorem nikTr_r' (A : Proposition ℕ) :
    nikTr Gt Ctx' Gt_fin r A = Proposition.imp (sigAt Gt Ctx' Gt_fin r) A := by
  have hroot : ¬ ∃ q, Gt.R q r := by rintro ⟨q, hq⟩; exact hq
  simp only [nikTr, nikTrFuel, dif_neg hroot]

/-- **Root-connectivity does NOT rescue it**: even with the conclusion label required to lie in
`G.X`, and `G` a single-rooted (one-node) forest, the statement is still false. The escape hatch
moved from the conclusion label to the CONTEXT label. -/
theorem rooted_restricted_adequacy_is_false
    (nik_adequacy : ∀ (G : Graph ℕ) (Γ : List (LabelledFormula ℕ)) (hfin : G.X.Finite)
        (x : Label ℕ) (A : Proposition ℕ),
        IsDerivationForest G → x ∈ G.X → NIK TS5 G Γ (x ∶ A) →
        Derivable CS5ModalAxiom (nikTr G Γ hfin x A)) : False := by
  have hr : r ∈ Gt.X := rfl
  have h := nik_adequacy Gt Ctx' Gt_fin r Proposition.bot gt_forest hr nik_deriv'
  rw [nikTr_r'] at h
  obtain ⟨dimp⟩ := h
  obtain ⟨dsig⟩ := sigAtFuel_r'_deriv (Gt_fin.toFinset.card)
  exact cs5_consistent_incest ⟨.modus_ponens [] _ _ dimp dsig⟩

/-! ### Step 5: the `x ∈ G.X`-restricted induction has a real gap at `efq` -/

/-- Every label mentioned in `Ctx` lies in `Gt.X` (so the "wellformed context" invariant holds). -/
theorem ctx_labels_in_X : ∀ φ ∈ Ctx, φ.lbl ∈ Gt.X := by
  intro φ hφ; simp at hφ; subst hφ; rfl

/-- Yet `NIK` still derives `⊥` at an OUT-OF-GRAPH label. So in the `efq` case of an
`x ∈ G.X`-restricted induction, the premise's label can be outside `G.X` and the induction
hypothesis simply does not apply -- the restriction is not merely insufficient, it is
uninductive. -/
theorem premise_escapes_graph :
    NIK TS5 Gt Ctx (yy ∶ Proposition.bot) ∧ yy ∉ Gt.X :=
  ⟨nik_deriv, by simp [Gt, Graph.trivial]⟩

/-! ### Axiom audit (must show no `sorryAx`) -/

#print axioms nik_adequacy_is_false
#print axioms rooted_restricted_adequacy_is_false
#print axioms nikTr_yy_explicit
#print axioms nik_deriv

end Probe537
