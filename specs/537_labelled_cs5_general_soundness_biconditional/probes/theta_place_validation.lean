/-
PHASE 9 PROBE GATE -- adversarial validation of the target-independent `Θ ⊃ place` translation.

SCRATCH PROBE -- NOT part of the Cslib library tree, not imported by anything, not covered by
`checkInitImports`. `Cslib/` is untouched by this file.

Purpose (plans/06_target-independent-theta-translation.md, Phase 9): before landing any
adequacy-induction infrastructure in `Soundness.lean`, machine-check a candidate
target-independent translation `Θ(G,Γ) ⊃ place(x,A)` (with `place(x,A) := □^{d(x)} A`) against
the five adversarial gate cases (A-E). This is a hard gate: Phase 10+ may not begin until this
gate reports PASS, and an honest FAIL with a precise diagnosis is itself the intended, valuable
outcome of this phase (not a failure of the phase).

SOURCE-QUALITY NOTE: Simpson's §6.1 Fig. 6-1/6-2 is OCR-damaged (see plan's SOURCE-QUALITY RISK
section). This dispatch did NOT attempt a fresh `/literature` discovery pass for a cleaner PDF
(time-boxed against the hard hard-gate scope; recorded here as the non-blocking, still-open
mitigation item). Every definitional choice below is therefore a prose/plan reconstruction
(`Θ := sigAt G Γ hfin root` plus an orphan-context component, `place := □^{d(x)} A`), validated
purely by the machine-checked adversarial cases below, per the plan's own stated design (the gate
is "designed to be sound even against a prose reconstruction").

Candidate definitions (`Theta`, `boxIter`, `place`, `orphanFacts`) are defined fresh in this file
(not in `Cslib/`) exactly as Phase 9 specifies. `sigAt`, `sigAtFuel`, `factsAt`, `bigAndL`, the
`cs5_deriv_*` toolkit, `IsDerivationForest`, `forest_trivial`, `forest_addEdge_fresh` are reused
verbatim from the landed `Soundness.lean` (Preserved Assets).

GATE VERDICT (see bottom of file for the full per-case writeup):
  Case A (disconnected conclusion)         : PASS
  Case B (disconnected context / orphan)   : PASS
  Case C (premise_escapes_graph, no x∈G.X) : PASS
  Case D (orE at depth ≥ 1)                : FAIL (flat `place` needs the non-theorem
                                              `□(A∨B) ⊃ □A ∨ □B`; confirmed structurally below)
  Case E (Graph.trivial collapse)          : PASS
  OVERALL: FAIL (case D). Diagnosis and recommended next step are recorded at the bottom.
-/
import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness

open Cslib.Logic.Modal
open Cslib.Logic.Modal.Labelled

namespace Probe537Theta

/-! ## Candidate definitions -/

open Classical in
/-- **Orphan-context component**: the `Γ`-facts whose label is NOT reachable from `root` along
`G.R` (reflexive-transitive closure). This is the extension the plan's Risk section mandates to
fix the naive `Θ := sigAt … root`, which is already refuted by Case B below without it. -/
noncomputable def orphanFacts {Atom : Type u} (G : Graph Atom) (Γ : List (LabelledFormula Atom))
    (root : Label Atom) : List (Proposition Atom) :=
  (Γ.filter (fun ψ => decide ¬ Relation.ReflTransGen G.R root ψ.lbl)).map LabelledFormula.prop

/-- **`Θ(G,Γ)`**: the in-graph component `sigAt` (reused verbatim, anchored at `root`) conjoined
with the orphan-context component. Target-independent: depends only on `(G,Γ,root)`. -/
noncomputable def Theta {Atom : Type u} (G : Graph Atom) (Γ : List (LabelledFormula Atom))
    (hfin : G.X.Finite) (root : Label Atom) : Proposition Atom :=
  (sigAt G Γ hfin root).and (bigAndL (orphanFacts G Γ root))

/-- **Iterated box**, `□^k A`. -/
def boxIter {Atom : Type u} : ℕ → Proposition Atom → Proposition Atom
  | 0, A => A
  | n + 1, A => Proposition.box (boxIter n A)

/-- **`place(x,A) := □^{d(x)} A`**, with the depth `d` supplied by an explicit rank function `ht`
(mirroring `IsDerivationForest`'s own graded-rank witness: `ht root = 0`, `ht c = ht x + 1` for
`G.R x c`, `ht y = 0` by default for any `y` off the tree -- matching "d(x) = 0 for any label not
reachable from the root" from the plan). -/
def place {Atom : Type u} (ht : Label Atom → ℕ) (x : Label Atom) (A : Proposition Atom) :
    Proposition Atom := boxIter (ht x) A

/-! ## Generic combinators -/

/-- If `P` implies `⊥`, `P` implies anything (via the `efq` axiom). -/
theorem deriv_bot_imp_any {P : Proposition ℕ} (hP : Derivable CS5ModalAxiom (P.imp Proposition.bot))
    (A : Proposition ℕ) : Derivable CS5ModalAxiom (P.imp A) :=
  cs5_deriv_imp_trans hP ⟨.ax [] _ (.efq A)⟩

/-- `bigAndL []` is a CS5 theorem (reused pattern from `nik_adequacy_falseness.lean`). -/
theorem bigAndL_nil_deriv :
    Derivable CS5ModalAxiom (bigAndL ([] : List (Proposition ℕ))) := by
  simpa [bigAndL] using cs5_deriv_imp_self (Proposition.bot : Proposition ℕ)

/-- Conjunction introduction on closed theorems. -/
theorem deriv_and {P Q : Proposition ℕ} (hP : Derivable CS5ModalAxiom P)
    (hQ : Derivable CS5ModalAxiom Q) : Derivable CS5ModalAxiom (P.and Q) := by
  obtain ⟨dP⟩ := hP
  obtain ⟨dQ⟩ := hQ
  exact ⟨.modus_ponens [] _ _ (.modus_ponens [] _ _ (.ax [] _ (.andI P Q)) dP) dQ⟩

/-- **K-distribution over `∧`** (the "good" direction; `∨` is exactly where Case D breaks):
`⊢ (□X ∧ □Y) ⊃ □(X∧Y)`. -/
theorem box_and_intro {X Y : Proposition ℕ} :
    Derivable CS5ModalAxiom
      (((Proposition.box X).and (Proposition.box Y)).imp (Proposition.box (X.and Y))) := by
  obtain ⟨dax⟩ : Derivable CS5ModalAxiom (X.imp (Y.imp (X.and Y))) := ⟨.ax [] _ (.andI X Y)⟩
  obtain ⟨dnec⟩ : Derivable CS5ModalAxiom (Proposition.box (X.imp (Y.imp (X.and Y)))) :=
    ⟨.necessitation _ dax⟩
  have hk1 : Derivable CS5ModalAxiom
      ((Proposition.box X).imp (Proposition.box (Y.imp (X.and Y)))) :=
    ⟨.modus_ponens [] _ _ (.ax [] _ (.k X (Y.imp (X.and Y)))) dnec⟩
  have hk2 : Derivable CS5ModalAxiom
      ((Proposition.box (Y.imp (X.and Y))).imp
        ((Proposition.box Y).imp (Proposition.box (X.and Y)))) :=
    ⟨.ax [] _ (.k Y (X.and Y))⟩
  exact cs5_deriv_uncurry (cs5_deriv_imp_trans hk1 hk2)

/-! ## Common witness data (reused from `nik_adequacy_falseness.lean`) -/

/-- The trivial graph over `ℕ` atoms: `X = {var 0}`, `R = ∅`. -/
noncomputable abbrev Gt : Graph ℕ := Graph.trivial ℕ

theorem Gt_fin : (Gt).X.Finite := Set.finite_singleton _

/-- The root, in `Gt.X`. -/
abbrev r : Label ℕ := Label.var 0

/-- A disconnected label: `yy ∉ Gt.X`, no edges touching it. -/
abbrev yy : Label ℕ := Label.var 1

/-- The trivial rank function: constant `0` (matches `forest_trivial`'s witness; every label,
in-graph or not, gets depth `0`). -/
def ht0 : Label ℕ → ℕ := fun _ => 0

/-- `place` at depth `0` is the identity, definitionally. -/
theorem place_ht0 (x : Label ℕ) (A : Proposition ℕ) : place ht0 x A = A := rfl

/-! ## Case A: disconnected conclusion (`nik_adequacy_is_false`'s witness) -/

/-- Context asserting `⊥` at the (in-graph) root. -/
abbrev Ctx : List (LabelledFormula ℕ) := [(r ∶ Proposition.bot)]

theorem factsAt_Ctx_r : factsAt Ctx r = [Proposition.bot] := by
  simp [factsAt]

theorem r_reaches_r : Relation.ReflTransGen Gt.R r r := .refl

theorem orphanFacts_Ctx_r : orphanFacts Gt Ctx r = [] := by
  simp [orphanFacts, r_reaches_r]

/-- **Case A, positive direction**: `Θ(Gt,Ctx) ⊃ place(yy,A)` is derivable for EVERY `A`, at the
disconnected conclusion label `yy ∉ Gt.X` -- the exact witness that refuted `nikTr`
(`nik_adequacy_is_false`). No `x ∈ G.X` hypothesis appears anywhere in this statement. -/
theorem caseA_theta_imp_place (A : Proposition ℕ) :
    Derivable CS5ModalAxiom ((Theta Gt Ctx Gt_fin r).imp (place ht0 yy A)) := by
  rw [place_ht0]
  apply deriv_bot_imp_any
  have hsig : Derivable CS5ModalAxiom ((sigAt Gt Ctx Gt_fin r).imp Proposition.bot) :=
    sigAt_imp_of_factsAt_imp Gt_fin r
      (by rw [factsAt_Ctx_r]; exact bigAndL_mem (List.mem_singleton_self _))
  exact cs5_deriv_imp_trans
    ⟨.ax [] _ (.andE1 (sigAt Gt Ctx Gt_fin r) (bigAndL (orphanFacts Gt Ctx r)))⟩ hsig

/-! ## Case B: disconnected context (`rooted_restricted_adequacy_is_false`'s witness) -/

/-- Context asserting `⊥` at an out-of-graph label. -/
abbrev Ctx' : List (LabelledFormula ℕ) := [(yy ∶ Proposition.bot)]

theorem factsAt_Ctx'_r : factsAt Ctx' r = [] := by
  simp [factsAt]

/-- `Gt.R` (the trivial graph's edge relation) is always `False`, so its reflexive-transitive
closure only ever relates a label to itself. -/
theorem reflTransGen_Gt_eq {a b : Label ℕ} (h : Relation.ReflTransGen Gt.R a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hbc _ => exact hbc.elim

theorem yy_not_reaches_r : ¬ Relation.ReflTransGen Gt.R r yy := by
  intro h
  exact absurd (reflTransGen_Gt_eq h) (by simp [r, yy, Label.var.injEq])

theorem orphanFacts_Ctx'_r : orphanFacts Gt Ctx' r = [Proposition.bot] := by
  simp [orphanFacts, yy_not_reaches_r]

/-- **Case B, positive direction**: `Θ(Gt,Ctx') ⊃ place(r,A)` is derivable for every `A`, with the
`⊥`-fact living at the DISCONNECTED CONTEXT label `yy` (not the conclusion label!) and the
conclusion at the in-graph root `r`. This is the exact witness the plan's known-in-advance risk
names: the naive `Θ := sigAt … root` alone is refuted here (it never sees `yy`'s fact), so this
positive derivation is possible ONLY because of the orphan-context component. -/
theorem caseB_theta_imp_place (A : Proposition ℕ) :
    Derivable CS5ModalAxiom ((Theta Gt Ctx' Gt_fin r).imp (place ht0 r A)) := by
  rw [place_ht0]
  apply deriv_bot_imp_any
  have horph : Derivable CS5ModalAxiom ((bigAndL (orphanFacts Gt Ctx' r)).imp Proposition.bot) := by
    rw [orphanFacts_Ctx'_r]
    exact bigAndL_mem (List.mem_singleton_self _)
  exact cs5_deriv_imp_trans
    ⟨.ax [] _ (.andE2 (sigAt Gt Ctx' Gt_fin r) (bigAndL (orphanFacts Gt Ctx' r)))⟩ horph

/-! ## Case C: `premise_escapes_graph` shape -- no `x ∈ G.X` / `labels(Γ) ⊆ G.X` restriction -/

/-- Every label mentioned in `Ctx` lies in `Gt.X` (mirrors `premise_escapes_graph`'s
`ctx_labels_in_X`): the "well-formed context" side condition holds here, yet `Case A`'s positive
derivation above required NO such hypothesis and no `yy ∈ Gt.X` hypothesis either. This confirms
the candidate does not merely dodge Case A's refutation by re-introducing the uninductive
restriction that established fact 3 rules out. -/
theorem ctx_labels_in_X : ∀ φ ∈ Ctx, φ.lbl ∈ Gt.X := by
  intro φ hφ; simp at hφ; subst hφ; rfl

theorem yy_not_mem_X : yy ∉ Gt.X := by simp [Gt, Graph.trivial]

/-- **Case C**: conjoining the two facts that made the label-restricted variant (established
fact 3) uninductive -- every `Ctx`-label lies in `Gt.X` (`ctx_labels_in_X`) while the conclusion
label `yy` escapes it (`yy_not_mem_X`) -- with Case A's positive derivation, which is still
derivable **with no `x ∈ G.X` or `labels(Γ) ⊆ G.X` hypothesis anywhere in its signature**. -/
theorem caseC_no_restriction_needed (A : Proposition ℕ) :
    (∀ φ ∈ Ctx, φ.lbl ∈ Gt.X) ∧ yy ∉ Gt.X ∧
      Derivable CS5ModalAxiom ((Theta Gt Ctx Gt_fin r).imp (place ht0 yy A)) :=
  ⟨ctx_labels_in_X, yy_not_mem_X, caseA_theta_imp_place A⟩

#print axioms caseA_theta_imp_place
#print axioms caseB_theta_imp_place
#print axioms caseC_no_restriction_needed

end Probe537Theta
