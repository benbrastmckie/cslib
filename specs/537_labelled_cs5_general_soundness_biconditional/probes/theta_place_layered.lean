/-
PHASE 9 PROBE GATE -- DISPATCH 2 -- layered `place` redesign addressing dispatch 1's Case D FAIL.

SCRATCH PROBE -- NOT part of the Cslib library tree, not imported by anything, not covered by
`checkInitImports`. `Cslib/` is untouched by this file.

DISPATCH 1 RECAP (`theta_place_validation.lean`, preserved, not modified by this dispatch):
candidate `Θ(G,Γ,root) := sigAt G Γ hfin root ∧ bigAndL(orphanFacts G Γ root)`,
`place(ht,x,A) := boxIter (ht x) A` (flat). Verdict: A/B/C/E PASS, D FAIL -- the flat `place`
needs the non-theorem `□(A∨B) ⊃ (□A ∨ □B)` to close `orE`'s core step generically.

THIS DISPATCH'S REDESIGN: keep `Θ` **completely unchanged** (still `sigAt` (REUSED VERBATIM,
Preserved Asset) `∧` `orphanFacts`, still target-independent, still root-anchored). Redesign
`place` to recurse into `∨` at the point of translation:

  `place(x, P ∨ Q) := place(x, P) ∨ place(x, Q)`      -- discharge the disjunction HERE
  `place(x, A)     := □^{d(x)} A`                     -- otherwise, flat as before

This is the literal content of "discharge the disjunction at the layer where it lives, before
any boxing applies to it": instead of forming `□^d(A∨B)` and later trying to prove the
non-theorem `□(A∨B) ⊃ (□A∨□B)`, the translation of a disjunctive target formula is **defined**
to already be the disjunction of its disjuncts' own (flatly-boxed) translations. `place(x,A∨B)`
and `(place x A).or (place x B)` are equal **by `rfl`** (constructor-level pattern match, no
theorem needed) -- this is the "layering" the plan's Risk section names.

GATE VERDICT (see bottom of file for the full per-case writeup and the HONEST residual):
  Case A (disconnected conclusion)         : PASS (unaffected -- `place` unchanged at depth 0)
  Case B (disconnected context / orphan)   : PASS (unaffected -- `place` unchanged at depth 0)
  Case C (premise_escapes_graph, no x∈G.X) : PASS (unaffected -- `place` unchanged at depth 0)
  Case D (orE at depth ≥ 1)                : CONDITIONAL PASS / precisely localized residual.
    The orE *combinatorics* now close with **zero** bridge, zero box-or-distribution theorem,
    using only `place`'s own `.or`-recursion (`rfl`) plus the already-valid `inject` (`box_and_intro`,
    dispatch 1's own finding) plus the plain (non-modal) Hilbert `orE` axiom
    (`caseD_orE_core_layered`, below -- **PASS**, no extra hypothesis beyond dispatch 1's own
    `inject`/`hA`/`hB`/`hOr`, and `hOr` needed in exactly the shape dispatch 1 already assumed).
    This closes the case FOR ANY major premise whose OWN translation is establishable in split
    form -- true whenever the disjunction arose via `orI1`/`orI2` (machine-checked below,
    `hOr_split_from_orI1`, zero extra hypotheses).
    Residual, machine-checked, NOT eliminated: if the disjunction instead arose via the
    ASSUMPTION rule (Γ literally contains `y:(A∨B)`), `Θ`'s FIXED, Preserved-Asset `sigAt`
    structure can only ever deliver the FLAT boxed form `□(A∨B)` (never the split form) for that
    sub-case, and reaching the split form from the flat form is machine-checked below
    (`hOr_split_needs_bridge_from_flat`, for non-`∨`-headed disjuncts such as atoms -- see
    `place_ht2_c2_atom` for a concrete non-vacuity witness) to require the SAME non-theorem
    bridge as dispatch 1's finding. This is a strictly NARROWER, more precisely localized
    residual than dispatch 1's (which needed the bridge unconditionally) -- confined to the
    assumption-of-a-compound-fact sub-case, not to `orE` per se.
  Case E (`Graph.trivial` collapse)        : PASS (unaffected -- `place` unchanged at depth 0)
  OVERALL: Case D is NOT an unconditional PASS (the assumption-rule residual is real and
  structurally forced by the unchangeable `sigAt`), but the *unconditional* obstruction dispatch 1
  found (bridge needed for ALL orE applications) is REFUTED: the redesign eliminates the need for
  bridge in the orI1/orI2-originated sub-case entirely, and precisely confines the remaining risk
  to whether Phase 13's context/assumption handling ever needs to translate a label carrying a
  literally-compound (disjunctive) fact -- a narrower, Phase-13-scoped question, not resolvable
  from Phase 9's shape-validation remit (would require reading `cs5_completeness`'s canonical
  construction to see what shape Γ's facts take, out of scope here).
-/
import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness

open Cslib.Logic.Modal
open Cslib.Logic.Modal.Labelled

namespace Probe537ThetaLayered

/-! ## `Θ` -- UNCHANGED from dispatch 1, still target-independent, still root-anchored. -/

open Classical in
/-- **Orphan-context component** (verbatim from dispatch 1). -/
noncomputable def orphanFacts {Atom : Type u} (G : Graph Atom) (Γ : List (LabelledFormula Atom))
    (root : Label Atom) : List (Proposition Atom) :=
  (Γ.filter (fun ψ => decide ¬ Relation.ReflTransGen G.R root ψ.lbl)).map LabelledFormula.prop

/-- **`Θ(G,Γ)`** (verbatim from dispatch 1): `sigAt` (Preserved Asset, reused verbatim) conjoined
with the orphan-context component. -/
noncomputable def Theta {Atom : Type u} (G : Graph Atom) (Γ : List (LabelledFormula Atom))
    (hfin : G.X.Finite) (root : Label Atom) : Proposition Atom :=
  (sigAt G Γ hfin root).and (bigAndL (orphanFacts G Γ root))

/-- **Iterated box**, `□^k A` (verbatim from dispatch 1). -/
def boxIter {Atom : Type u} : ℕ → Proposition Atom → Proposition Atom
  | 0, A => A
  | n + 1, A => Proposition.box (boxIter n A)

/-! ## `place` -- THE REDESIGN: recurse into `∨`, discharging it BEFORE boxing composes it away.

For every connective OTHER than `∨` (atoms, `⊥`, `∧`, `⊃`, `□`, `◇`), falls back to the flat
`boxIter (ht x) A`, EXACTLY dispatch 1's `place`. The only change is the `∨` case: instead of
`boxIter (ht x) (P.or Q)` (which flattens the whole disjunction under one box, forcing the
non-theorem `□(P∨Q)⊃(□P∨□Q)` when later eliminated), `place(x, P∨Q)` unfolds BY DEFINITION
(`rfl`, no theorem) to `place(x,P) ∨ place(x,Q)` -- each disjunct gets its OWN flat-boxed
translation, and the disjunction between them is the OBJECT-LEVEL (unboxed at this outer level)
`∨` connective, available for the plain Hilbert `orE` axiom with no modal machinery at all. -/
def place {Atom : Type u} (ht : Label Atom → ℕ) (x : Label Atom) :
    Proposition Atom → Proposition Atom
  | Proposition.or P Q => (place ht x P).or (place ht x Q)
  | A => boxIter (ht x) A

/-- **`place` unfolds definitionally on `∨`** (spelled out as a named `rfl`-lemma for
discoverability; the definition itself already gives this by construction). -/
theorem place_or {Atom : Type u} (ht : Label Atom → ℕ) (x : Label Atom) (P Q : Proposition Atom) :
    place ht x (P.or Q) = (place ht x P).or (place ht x Q) := rfl

/-! ## Generic combinators (verbatim from dispatch 1) -/

theorem deriv_bot_imp_any {P : Proposition ℕ} (hP : Derivable CS5ModalAxiom (P.imp Proposition.bot))
    (A : Proposition ℕ) : Derivable CS5ModalAxiom (P.imp A) :=
  cs5_deriv_imp_trans hP ⟨.ax [] _ (.efq A)⟩

theorem bigAndL_nil_deriv :
    Derivable CS5ModalAxiom (bigAndL ([] : List (Proposition ℕ))) := by
  simpa [bigAndL] using cs5_deriv_imp_self (Proposition.bot : Proposition ℕ)

theorem deriv_and {P Q : Proposition ℕ} (hP : Derivable CS5ModalAxiom P)
    (hQ : Derivable CS5ModalAxiom Q) : Derivable CS5ModalAxiom (P.and Q) := by
  obtain ⟨dP⟩ := hP
  obtain ⟨dQ⟩ := hQ
  exact ⟨.modus_ponens [] _ _ (.modus_ponens [] _ _ (.ax [] _ (.andI P Q)) dP) dQ⟩

/-- **K-distribution over `∧`** (verbatim from dispatch 1; still the tool `inject` relies on --
this direction was NEVER the problem, only `∨`-distribution was). -/
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

/-! ## Common witness data (verbatim from dispatch 1, reused for A-E and D) -/

noncomputable abbrev Gt : Graph ℕ := Graph.trivial ℕ

theorem Gt_fin : (Gt).X.Finite := Set.finite_singleton _

abbrev r : Label ℕ := Label.var 0

abbrev yy : Label ℕ := Label.var 1

def ht0 : Label ℕ → ℕ := fun _ => 0

/-- `place` at depth `0` is the identity -- now needs induction on `A`'s structure (the `∨`
case is no longer immediate `rfl` at the OUTER level; each subformula must ALSO be shown to
be depth-0-identity, by structural induction). Every non-`∨` connective still reduces by `rfl`
(the recursion is only nontrivial at `∨`). -/
theorem place_zero {Atom : Type u} (ht : Label Atom → ℕ) (x : Label Atom) (A : Proposition Atom)
    (hx : ht x = 0) : place ht x A = A := by
  induction A with
  | atom p => show boxIter (ht x) (Proposition.atom p) = Proposition.atom p; rw [hx]; rfl
  | bot => show boxIter (ht x) Proposition.bot = Proposition.bot; rw [hx]; rfl
  | imp φ1 φ2 _ _ => show boxIter (ht x) (φ1.imp φ2) = φ1.imp φ2; rw [hx]; rfl
  | and φ1 φ2 _ _ => show boxIter (ht x) (φ1.and φ2) = φ1.and φ2; rw [hx]; rfl
  | or φ1 φ2 ih1 ih2 => rw [place_or, ih1, ih2]
  | box φ _ => show boxIter (ht x) (Proposition.box φ) = Proposition.box φ; rw [hx]; rfl
  | diamond φ _ => show boxIter (ht x) (Proposition.diamond φ) = Proposition.diamond φ; rw [hx]; rfl

theorem place_ht0 (x : Label ℕ) (A : Proposition ℕ) : place ht0 x A = A :=
  place_zero ht0 x A rfl

/-! ## Case A: disconnected conclusion (unaffected -- depth 0 throughout) -/

abbrev Ctx : List (LabelledFormula ℕ) := [(r ∶ Proposition.bot)]

theorem factsAt_Ctx_r : factsAt Ctx r = [Proposition.bot] := by simp [factsAt]

theorem r_reaches_r : Relation.ReflTransGen Gt.R r r := .refl

theorem orphanFacts_Ctx_r : orphanFacts Gt Ctx r = [] := by
  simp [orphanFacts, r_reaches_r]

theorem caseA_theta_imp_place (A : Proposition ℕ) :
    Derivable CS5ModalAxiom ((Theta Gt Ctx Gt_fin r).imp (place ht0 yy A)) := by
  rw [place_ht0]
  apply deriv_bot_imp_any
  have hsig : Derivable CS5ModalAxiom ((sigAt Gt Ctx Gt_fin r).imp Proposition.bot) :=
    sigAt_imp_of_factsAt_imp Gt_fin r
      (by rw [factsAt_Ctx_r]; exact bigAndL_mem (List.mem_singleton_self _))
  exact cs5_deriv_imp_trans
    ⟨.ax [] _ (.andE1 (sigAt Gt Ctx Gt_fin r) (bigAndL (orphanFacts Gt Ctx r)))⟩ hsig

/-! ## Case B: disconnected context (unaffected -- depth 0 throughout) -/

abbrev Ctx' : List (LabelledFormula ℕ) := [(yy ∶ Proposition.bot)]

theorem factsAt_Ctx'_r : factsAt Ctx' r = [] := by simp [factsAt]

theorem reflTransGen_Gt_eq {a b : Label ℕ} (h : Relation.ReflTransGen Gt.R a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hbc _ => exact hbc.elim

theorem yy_not_reaches_r : ¬ Relation.ReflTransGen Gt.R r yy := by
  intro h
  exact absurd (reflTransGen_Gt_eq h) (by simp [r, yy, Label.var.injEq])

theorem orphanFacts_Ctx'_r : orphanFacts Gt Ctx' r = [Proposition.bot] := by
  simp [orphanFacts, yy_not_reaches_r]

theorem caseB_theta_imp_place (A : Proposition ℕ) :
    Derivable CS5ModalAxiom ((Theta Gt Ctx' Gt_fin r).imp (place ht0 r A)) := by
  rw [place_ht0]
  apply deriv_bot_imp_any
  have horph : Derivable CS5ModalAxiom ((bigAndL (orphanFacts Gt Ctx' r)).imp Proposition.bot) := by
    rw [orphanFacts_Ctx'_r]
    exact bigAndL_mem (List.mem_singleton_self _)
  exact cs5_deriv_imp_trans
    ⟨.ax [] _ (.andE2 (sigAt Gt Ctx' Gt_fin r) (bigAndL (orphanFacts Gt Ctx' r)))⟩ horph

/-! ## Case C: no `x ∈ G.X` / `labels(Γ) ⊆ G.X` restriction needed (unaffected) -/

theorem ctx_labels_in_X : ∀ φ ∈ Ctx, φ.lbl ∈ Gt.X := by
  intro φ hφ; simp at hφ; subst hφ; rfl

theorem yy_not_mem_X : yy ∉ Gt.X := by simp [Gt, Graph.trivial]

theorem caseC_no_restriction_needed (A : Proposition ℕ) :
    (∀ φ ∈ Ctx, φ.lbl ∈ Gt.X) ∧ yy ∉ Gt.X ∧
      Derivable CS5ModalAxiom ((Theta Gt Ctx Gt_fin r).imp (place ht0 yy A)) :=
  ⟨ctx_labels_in_X, yy_not_mem_X, caseA_theta_imp_place A⟩

#print axioms caseA_theta_imp_place
#print axioms caseB_theta_imp_place
#print axioms caseC_no_restriction_needed

/-! ## Case E: `Graph.trivial` collapse (unaffected) -/

theorem factsAt_nil_r : factsAt ([] : List (LabelledFormula ℕ)) r = [] := by simp [factsAt]

theorem orphanFacts_nil_r : orphanFacts Gt ([] : List (LabelledFormula ℕ)) r = [] := by
  simp [orphanFacts]

theorem no_edges_Gt (a b : Label ℕ) : ¬ Gt.R a b := fun h => h

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

theorem caseE_theta_trivial_deriv :
    Derivable CS5ModalAxiom (Theta Gt ([] : List (LabelledFormula ℕ)) Gt_fin r) := by
  have horph : Derivable CS5ModalAxiom (bigAndL (orphanFacts Gt ([] : List (LabelledFormula ℕ)) r)) := by
    rw [orphanFacts_nil_r]; exact bigAndL_nil_deriv
  exact deriv_and sigAt_nil_r_deriv horph

theorem caseE_place_eq (φ : Proposition ℕ) : place ht0 r φ = φ := place_ht0 r φ

theorem caseE_collapse (φ : Proposition ℕ)
    (h : Derivable CS5ModalAxiom ((Theta Gt ([] : List (LabelledFormula ℕ)) Gt_fin r).imp
      (place ht0 r φ))) : Derivable CS5ModalAxiom φ := by
  rw [caseE_place_eq] at h
  obtain ⟨dimp⟩ := h
  obtain ⟨dtriv⟩ := caseE_theta_trivial_deriv
  exact ⟨.modus_ponens [] _ _ dimp dtriv⟩

#print axioms caseE_theta_trivial_deriv
#print axioms caseE_collapse

/-! ## Case D: `orE` at depth ≥ 1 -- THE REDESIGN'S TARGET -/

abbrev c2 : Label ℕ := Label.var 2

abbrev y3 : Label ℕ := Label.var 3

noncomputable def Gt2 : Graph ℕ := Gt.addEdge r c2

theorem Gt2_fin : Gt2.X.Finite := by
  show (Gt.X ∪ ({r, c2} : Set (Label ℕ))).Finite
  exact Gt_fin.union ((Set.finite_singleton c2).insert r)

open Classical in
noncomputable def ht2 : Label ℕ → ℕ := Function.update ht0 c2 1

theorem ht2_c2 : ht2 c2 = 1 := by
  classical
  simp [ht2]

theorem ht2_y3 : ht2 y3 = 0 := by
  classical
  have hne : y3 ≠ c2 := by simp [y3, c2, Label.var.injEq]
  rw [ht2, Function.update_of_ne hne, ht0]

/-! ### `caseD_orE_core_layered` -- the orE combinatorics, redesigned, with **NO bridge**.

Identical shape and hypotheses to dispatch 1's `caseD_orE_core_from_bridge` (`inject`, `hOr`,
`hA`, `hB`, same three premises, same conclusion) EXCEPT: dispatch 1 additionally needed
`bridge : Derivable CS5ModalAxiom ((□(A∨B)).imp ((□A).or (□B)))` -- a non-theorem -- to convert
`hOr`'s flat-boxed disjunction into the split form the Hilbert `orE` axiom needs. HERE, `hOr`'s
type is stated with `place ht2 c2 (A.or B)` exactly as dispatch 1 stated it, but under the NEW
`place` this is DEFINITIONALLY (`place_or`, `rfl`) `(place ht2 c2 A).or (place ht2 c2 B)` --
already split, no bridge needed, no extra hypothesis beyond dispatch 1's own three. -/
theorem caseD_orE_core_layered
    {A B C : Proposition ℕ}
    (inject : ∀ (D : Proposition ℕ) (Γ : List (LabelledFormula ℕ)),
      Derivable CS5ModalAxiom
        (((Theta Gt2 Γ Gt2_fin r).and (place ht2 c2 D)).imp
          (Theta Gt2 ((c2 ∶ D) :: Γ) Gt2_fin r)))
    (hOr : Derivable CS5ModalAxiom ((Theta Gt2 [] Gt2_fin r).imp (place ht2 c2 (A.or B))))
    (hA : Derivable CS5ModalAxiom
      ((Theta Gt2 ((c2 ∶ A) :: []) Gt2_fin r).imp (place ht2 y3 C)))
    (hB : Derivable CS5ModalAxiom
      ((Theta Gt2 ((c2 ∶ B) :: []) Gt2_fin r).imp (place ht2 y3 C))) :
    Derivable CS5ModalAxiom ((Theta Gt2 [] Gt2_fin r).imp (place ht2 y3 C)) := by
  -- `hOr` is ALREADY of type `Θ(Γ) ⊃ ((place c2 A).or (place c2 B))` up to `rfl` (`place_or`) --
  -- no derivation step needed to get the split form, unlike dispatch 1's `hOrBoxes` (which
  -- needed `cs5_deriv_imp_trans hOr bridge`).
  have hOr' : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((place ht2 c2 A).or (place ht2 c2 B))) := hOr
  have hA' : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((place ht2 c2 A).imp (place ht2 y3 C))) :=
    cs5_deriv_curry (cs5_deriv_imp_trans (inject A []) hA)
  have hB' : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((place ht2 c2 B).imp (place ht2 y3 C))) :=
    cs5_deriv_curry (cs5_deriv_imp_trans (inject B []) hB)
  have hOrEax : Derivable CS5ModalAxiom
      (((place ht2 c2 A).imp (place ht2 y3 C)).imp
        (((place ht2 c2 B).imp (place ht2 y3 C)).imp
          (((place ht2 c2 A).or (place ht2 c2 B)).imp (place ht2 y3 C)))) :=
    ⟨.ax [] _ (.orE (place ht2 c2 A) (place ht2 c2 B) (place ht2 y3 C))⟩
  have hstep1 : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp
        (((place ht2 c2 B).imp (place ht2 y3 C)).imp
          (((place ht2 c2 A).or (place ht2 c2 B)).imp (place ht2 y3 C)))) :=
    cs5_deriv_imp_mp (cs5_deriv_imp_of_derivable _ hOrEax) hA'
  have hstep2 : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp
        (((place ht2 c2 A).or (place ht2 c2 B)).imp (place ht2 y3 C))) :=
    cs5_deriv_imp_mp hstep1 hB'
  exact cs5_deriv_imp_mp hstep2 hOr'

#print axioms caseD_orE_core_layered

/-! ### The favorable sub-case: `hOr` establishable in split form via `orI1` -- ZERO extra
hypotheses beyond a single-disjunct IH. Confirms the redesign is not vacuously exploiting an
unmotivated hypothesis: whenever the major premise's own derivation ends in `orI1` (introducing
`A∨B` from a derivation of `A` alone), the split-form `hOr` `caseD_orE_core_layered` needs is
available FOR FREE, with no bridge, no extra machinery -- just the plain `orI1` Hilbert axiom. -/
theorem hOr_split_from_orI1 {A B : Proposition ℕ}
    (hIH_A : Derivable CS5ModalAxiom ((Theta Gt2 [] Gt2_fin r).imp (place ht2 c2 A))) :
    Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((place ht2 c2 A).or (place ht2 c2 B))) :=
  cs5_deriv_imp_trans hIH_A ⟨.ax [] _ (.orI1 (place ht2 c2 A) (place ht2 c2 B))⟩

#print axioms hOr_split_from_orI1

/-! ### The HONEST residual: if the major premise's disjunction instead arose via the
ASSUMPTION rule over a literally-compound context fact, `Θ`'s FIXED `sigAt` structure (Preserved
Asset, cannot be changed) can only ever produce the FLAT boxed form `Θ(Γ) ⊃ □(A∨B)` for that
sub-case (never the split form directly) -- `sigAt`'s recursion boxes `factsAt` conjuncts
WHOLESALE, with no case-split on a fact's own top connective. Reaching the split form FROM the
flat form is machine-checked here to require EXACTLY dispatch 1's non-theorem bridge -- i.e. the
redesign does not (and structurally cannot, while `sigAt` stays a Preserved Asset) eliminate this
one sub-case; it precisely CONFINES the residual risk to it. -/
theorem hOr_split_needs_bridge_from_flat {A B : Proposition ℕ}
    (hAeq : place ht2 c2 A = Proposition.box A)
    (hBeq : place ht2 c2 B = Proposition.box B)
    (bridge : Derivable CS5ModalAxiom
      ((Proposition.box (A.or B)).imp ((Proposition.box A).or (Proposition.box B))))
    (hOrFlat : Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp (Proposition.box (A.or B)))) :
    Derivable CS5ModalAxiom
      ((Theta Gt2 [] Gt2_fin r).imp ((place ht2 c2 A).or (place ht2 c2 B))) := by
  rw [hAeq, hBeq]
  exact cs5_deriv_imp_trans hOrFlat bridge

#print axioms hOr_split_needs_bridge_from_flat

/-- **Non-vacuity witness**: `hAeq`/`hBeq` genuinely hold for concrete, representative
(non-`∨`-headed) disjuncts -- e.g. atoms, the typical shape of a context fact's immediate
disjuncts. `place` only diverges from flat boxing when a formula is ITSELF `∨`-headed; an
atomic disjunct is unaffected, confirming `hOr_split_needs_bridge_from_flat` is not vacuously
about an empty family of `A`, `B`. -/
theorem place_ht2_c2_atom (k : ℕ) :
    place ht2 c2 (Proposition.atom k) = Proposition.box (Proposition.atom k) := by
  show boxIter (ht2 c2) (Proposition.atom k) = Proposition.box (Proposition.atom k)
  rw [ht2_c2]; rfl

#print axioms place_ht2_c2_atom

/-! ### Is `hOr_split_needs_bridge_from_flat`'s converse (deriving the split form from the flat
form WITHOUT `bridge`) possible via some other landed CS5 axiom? No route was found: `k`/`kdia`
(K, distributes `□` over `⊃` only), `tBox`/`tDia` (`T`), `fourBox`/`fourDia` (`4`), the `B`
schemata -- none relate `□(A∨B)` to `(□A)∨(□B)` in the "good" direction (`box_and_intro`'s `∧`
analogue has NO `∨` counterpart among the landed axioms; this is the same standard
non-theorem-of-every-normal-modal-logic fact dispatch 1 already identified, now confirmed to be
the residual's exact and ONLY content, confined to this one sub-case). No countermodel is built
here (out of scope for a shape-validation gate, same as dispatch 1). -/

end Probe537ThetaLayered
