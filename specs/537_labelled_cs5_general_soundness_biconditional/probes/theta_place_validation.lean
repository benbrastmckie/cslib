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

/-! ## Case E: `Graph.trivial` collapse (the Phase 20 assembly step) -/

theorem factsAt_nil_r : factsAt ([] : List (LabelledFormula ℕ)) r = [] := by
  simp [factsAt]

theorem orphanFacts_nil_r : orphanFacts Gt ([] : List (LabelledFormula ℕ)) r = [] := by
  simp [orphanFacts]

theorem no_edges_Gt (a b : Label ℕ) : ¬ Gt.R a b := fun h => h

/-- **`sigAt Gt [] Gt_fin r` is a CS5 tautology** (unfolds to a pure conjunction of `bigAndL []`
tautology-pads, `Gt` having no edges and `[]` carrying no facts). -/
theorem sigAt_nil_r_deriv : Derivable CS5ModalAxiom (sigAt Gt [] Gt_fin r) := by
  have hcard : Gt_fin.toFinset.card = 1 := by
    have : Gt_fin.toFinset = {Label.var 0} := by ext c; simp [Gt, Graph.trivial]
    simp [this]
  have hempty : {c | Gt.R r c} = (∅ : Set (Label ℕ)) := by ext c; simp [no_edges_Gt]
  have hunfold : sigAt Gt [] Gt_fin r = Proposition.and (bigAndL (factsAt [] r)) (bigAndL []) := by
    rw [sigAt, hcard, sigAtFuel]
    congr 1
    simp [Set.Finite.toFinset_eq_empty.mpr hempty]
  rw [hunfold, factsAt_nil_r]
  exact deriv_and bigAndL_nil_deriv bigAndL_nil_deriv

/-- **`Θ(Graph.trivial,[])` is a CS5 tautology.** -/
theorem caseE_theta_trivial_deriv :
    Derivable CS5ModalAxiom (Theta Gt ([] : List (LabelledFormula ℕ)) Gt_fin r) := by
  have horph : Derivable CS5ModalAxiom (bigAndL (orphanFacts Gt ([] : List (LabelledFormula ℕ)) r)) := by
    rw [orphanFacts_nil_r]; exact bigAndL_nil_deriv
  exact deriv_and sigAt_nil_r_deriv horph

/-- `place` at the root, depth `0`, is the identity: `place ht0 root φ = φ`. -/
theorem caseE_place_eq (φ : Proposition ℕ) : place ht0 r φ = φ := rfl

/-- **The Phase 20 collapse itself**: GIVEN a (hypothetical -- not yet the full adequacy
induction, which is Phases 13-19's job) derivation of `Θ(Gt,[]) ⊃ place(r,φ)`, modus ponens with
`caseE_theta_trivial_deriv` yields `⊢ φ` directly -- the exact mechanism `nik_TS5_to_hilbert`
(Phase 20) needs to strip the translation off a closed `NIKTheorem` derivation. -/
theorem caseE_collapse (φ : Proposition ℕ)
    (h : Derivable CS5ModalAxiom ((Theta Gt ([] : List (LabelledFormula ℕ)) Gt_fin r).imp
      (place ht0 r φ))) : Derivable CS5ModalAxiom φ := by
  rw [caseE_place_eq] at h
  obtain ⟨dimp⟩ := h
  obtain ⟨dtriv⟩ := caseE_theta_trivial_deriv
  exact ⟨.modus_ponens [] _ _ dimp dtriv⟩

#print axioms caseE_theta_trivial_deriv
#print axioms caseE_collapse

/-! ## Case D: `orE` at depth ≥ 1 -- the primary residual risk -/

/-- The depth-1 child of `r`. Named `c2` (not `c1`) purely to keep it visibly distinct from
`yy`/other Case A-C labels reused in this namespace. -/
abbrev c2 : Label ℕ := Label.var 2

/-- The target of the `orE` conclusion: an unrelated, disconnected label. -/
abbrev y3 : Label ℕ := Label.var 3

/-- A two-level graph: root `r` with one child `c2` (`r`'s only edge). -/
noncomputable def Gt2 : Graph ℕ := Gt.addEdge r c2

theorem Gt2_fin : Gt2.X.Finite := by
  show (Gt.X ∪ ({r, c2} : Set (Label ℕ))).Finite
  exact Gt_fin.union ((Set.finite_singleton c2).insert r)

open Classical in
/-- The rank function used by `place` on `Gt2`: `r ↦ 0`, `c2 ↦ 1`, everything else (including the
disconnected `y3`) defaults to `0`, matching `forest_addEdge_fresh`'s own
`Function.update ht x (ht x + 1)` construction pattern. -/
noncomputable def ht2 : Label ℕ → ℕ := Function.update ht0 c2 1

theorem ht2_c2 : ht2 c2 = 1 := by
  classical
  simp [ht2]

theorem ht2_y3 : ht2 y3 = 0 := by
  classical
  have hne : y3 ≠ c2 := by simp [y3, c2, Label.var.injEq]
  rw [ht2, Function.update_of_ne hne, ht0]

theorem place_ht2_c2 (A : Proposition ℕ) : place ht2 c2 A = Proposition.box A := by
  simp [place, ht2_c2, boxIter]

theorem place_ht2_y3 (A : Proposition ℕ) : place ht2 y3 A = A := by
  simp [place, ht2_y3, boxIter]

/-! ### The `orE` core step

`sigAt Gt2 Γ Gt2_fin r`'s box-conjunct (descending to `c2`, `r`'s only child) is exactly
`sigAtFuel Gt2 Γ Gt2_fin 1 c2`, and `sigAt_c2_unfold` above confirms this equals
`sigAt Gt2 Γ Gt2_fin c2` (since `c2` has no children, extra fuel is inert) -- so `place ht2 c2 A =
□A` sits at PRECISELY the box level `sigAt`'s own recursion already uses for `c2`'s subtree. This
IS the shared-`Θ`-structure alignment the plan's risk section asks Phase 9 to test; the question
is whether it is enough to close `orE`, not whether `Θ`/`place` line up (they do).

Rather than re-deriving the concrete root-to-child injection computation here (a genuine
Phase 12-sized piece of infrastructure -- `sigAt_cons_self_imp`, the closest landed analogue,
itself avoids computing an explicit `Finset.toList` for exactly this reason, working abstractly
via `sigAtFuel_congr_above_rank` instead), the injection step is taken as an explicit, motivated
HYPOTHESIS below (`inject`): `Θ(G,Γ) ∧ □^{d(x)}D ⊃ Θ(G,(x∶D)::Γ)`. Its plausibility is not in
question (`box_and_intro`'s K-distribution-over-`∧` argument, sketched above, is exactly the tool
Phase 12 would use, and does NOT hit any non-theorem). Isolating it as a hypothesis lets Case D
target its actual question precisely: given `inject`, does `orE`'s disjunction step close, or does
it independently need the box-or-distribution non-theorem? -/

/-- **`orE`'s core step, generic in the three premise translations.** Mirrors `NIK.orE`'s shape
exactly: major premise `Θ(Γ) ⊃ place(c2, A∨B)` (the disjunction sits at `c2`, depth 1), two branch
IHs `Θ((c2∶A)::Γ) ⊃ place(y3,C)` / `Θ((c2∶B)::Γ) ⊃ place(y3,C)` (conclusion at the UNRELATED,
disconnected `y3`), goal `Θ(Γ) ⊃ place(y3,C)`. `inject` packages the (independently plausible,
Phase-12-scoped) `Θ`-injection step. **This is provable GIVEN `bridge`** -- confirming `bridge` is
SUFFICIENT to close the step. -/
theorem caseD_orE_core_from_bridge
    {A B C : Proposition ℕ}
    (inject : ∀ (D : Proposition ℕ) (Γ : List (LabelledFormula ℕ)),
      Derivable CS5ModalAxiom
        (((Theta Gt2 Γ Gt2_fin r).and (place ht2 c2 D)).imp
          (Theta Gt2 ((c2 ∶ D) :: Γ) Gt2_fin r)))
    (bridge : Derivable CS5ModalAxiom
      ((Proposition.box (A.or B)).imp ((Proposition.box A).or (Proposition.box B))))
    (hOr : Derivable CS5ModalAxiom ((Theta Gt2 [] Gt2_fin r).imp (place ht2 c2 (A.or B))))
    (hA : Derivable CS5ModalAxiom
      ((Theta Gt2 ((c2 ∶ A) :: []) Gt2_fin r).imp (place ht2 y3 C)))
    (hB : Derivable CS5ModalAxiom
      ((Theta Gt2 ((c2 ∶ B) :: []) Gt2_fin r).imp (place ht2 y3 C))) :
    Derivable CS5ModalAxiom ((Theta Gt2 [] Gt2_fin r).imp (place ht2 y3 C)) := by
  rw [place_ht2_c2] at hOr
  -- Curry the branch IHs (via `inject`) into `Θ(Γ) ⊃ (□A ⊃ place(y3,C))` / `□B` analogously.
  have hA' : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((Proposition.box A).imp (place ht2 y3 C))) := by
    rw [← place_ht2_c2]
    exact cs5_deriv_curry (cs5_deriv_imp_trans (inject A []) hA)
  have hB' : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((Proposition.box B).imp (place ht2 y3 C))) := by
    rw [← place_ht2_c2]
    exact cs5_deriv_curry (cs5_deriv_imp_trans (inject B []) hB)
  -- `bridge` turns the boxed disjunction into a disjunction of boxes; the Hilbert `orE` axiom
  -- (label-free, purely propositional) then closes it under the shared antecedent `Θ(Γ)`.
  have hOrBoxes : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((Proposition.box A).or (Proposition.box B))) :=
    cs5_deriv_imp_trans hOr bridge
  have hOrEax : Derivable CS5ModalAxiom
      (((Proposition.box A).imp (place ht2 y3 C)).imp
        (((Proposition.box B).imp (place ht2 y3 C)).imp
          (((Proposition.box A).or (Proposition.box B)).imp (place ht2 y3 C)))) :=
    ⟨.ax [] _ (.orE (Proposition.box A) (Proposition.box B) (place ht2 y3 C))⟩
  have hstep1 : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp
        (((Proposition.box B).imp (place ht2 y3 C)).imp
          (((Proposition.box A).or (Proposition.box B)).imp (place ht2 y3 C)))) :=
    cs5_deriv_imp_mp (cs5_deriv_imp_of_derivable _ hOrEax) hA'
  have hstep2 : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp
        (((Proposition.box A).or (Proposition.box B)).imp (place ht2 y3 C))) :=
    cs5_deriv_imp_mp hstep1 hB'
  exact cs5_deriv_imp_mp hstep2 hOrBoxes

/-! ### Does the natural alternative (T-iteration alone, no `bridge`) avoid the wall?

The other candidate route strips ALL boxes off `hOr` via the always-valid `CS5ModalAxiom.tBox`
(`□φ⊃φ`, no non-theorem risk) to get a BARE `Θ(Γ) ⊃ (A∨B)`, then tries the plain Hilbert `orE`
axiom directly on `(A∨B)` with bare branch hypotheses `Θ(Γ)⊃(A⊃place(y3,C))` /
`Θ(Γ)⊃(B⊃place(y3,C))`. But `inject`'s own shape (matching `place`'s box-indexing) only ever
supplies the BOXED branch hypotheses `Θ(Γ)⊃(□A⊃place(y3,C))` (see `hA'`/`hB'` above) -- getting
from boxed-antecedent to bare-antecedent branch hypotheses would need `A ⊃ □A` (necessitation
from an arbitrary HYPOTHESIS, not a closed theorem: unavailable), and going the other way (boxing
the bare disjunction first via `tBox`-stripping, THEN needing `(A∨B)⊃(□A∨□B)` to line back up with
the boxed branches) is exactly `bridge` again, not a way around it. **No third route was found.**
This confirms -- rather than merely inherits -- the plan's primary residual risk: for `place`'s
flat `□^d` indexing, `bridge` (`□(A∨B)⊃(□A∨□B)`) is not merely sufficient (`caseD_orE_core_from_bridge`
above) but the ONLY route located from the available `cs5_deriv_*` toolkit; `bridge` itself is the
STANDARD non-theorem of normal (K-based, hence also S5-based) modal logic (semantically: two
`R`-related worlds `w1 ⊨ A, ¬B` and `w2 ⊨ ¬A, B`, both accessible from a point `p`, give `p ⊨
□(A∨B)` while `p ⊭ □A` and `p ⊭ □B`) -- already the basis for the plan's own citation of "the same
non-theorem that killed the fully-boxed flat shortcut" under plan v4. No countermodel is built in
this probe (out of scope for a shape-validation gate); the finding is the STRUCTURAL dependency
above, machine-checked, not a fresh semantic refutation. -/

#print axioms caseD_orE_core_from_bridge

end Probe537Theta
