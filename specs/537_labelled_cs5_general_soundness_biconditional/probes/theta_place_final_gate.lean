/-
PHASE 9 PROBE GATE -- DISPATCH 3 of 3 (FINAL, hard cap) -- settles the single question left open
by dispatch 2 (`theta_place_layered.lean`): CAN a disjunctive formula appear in `Γ` at a label, as
an `NIK.assumption`, in the derivations `nik_adequacy` must cover?

SCRATCH PROBE -- NOT part of the Cslib library tree, not imported by anything, not covered by
`checkInitImports`. `Cslib/` is untouched by this file (verify via `git status --short Cslib/`).

RECAP (both preserved, not modified):
- `theta_place_validation.lean` (dispatch 1): flat `place`. A/B/C/E PASS, D FAIL (needs the
  non-theorem `□(A∨B) ⊃ (□A∨□B)` unconditionally).
- `theta_place_layered.lean` (dispatch 2): `Θ` UNCHANGED (`sigAt`, Preserved Asset); `place`
  redesigned to recurse into `∨`. A/B/C/E still PASS. Case D: the orE *combinatorics* close with
  ZERO bridge whenever the major premise's own translation is available in split form (free for
  `orI1`/`orI2`-originated disjunctions, `hOr_split_from_orI1`). HONEST RESIDUAL, left open: if the
  disjunction instead arises via `Γ`'s `assumption` rule, `sigAt`'s fixed fold can only ever
  deliver the FLAT boxed form, and flat→split needs the same non-theorem bridge
  (`hOr_split_needs_bridge_from_flat`) -- but dispatch 2 posed this ONLY as an abstract hypothesis
  (`hOrFlat`), never showing it is actually forced by a genuine `NIK` derivation.

THIS DISPATCH answers the reachability question directly from `Deduction.lean`'s own constructor
signatures (read, not re-derived): `NIK.impI`, `NIK.orE`, `NIK.diaE` all extend `Γ` with an
**arbitrary, unrestricted** `Proposition Atom` (no atomicity side-condition anywhere in
`Deduction.lean`'s `inductive NIK`). Consequently `nik_adequacy`'s own stated signature (plan
`06_target-independent-theta-translation.md:660`, quantifying over **every** `Γ`, with **no**
`x ∈ G.X` / `labels(Γ) ⊆ G.X` restriction -- an established, non-negotiable requirement) forces its
`assumption`-case proof obligation to be discharged for **every** reachable `Γ`, including one
built by an entirely mundane `impI` discharging a literally-disjunctive antecedent (e.g. proving
`(P∨Q) ⊃ (P∨Q)`). This makes the question decidable WITHOUT inspecting `cs5_completeness`'s
canonical-model construction at all (Plan question 2 is moot: `nik_adequacy`'s own quantifier
already settles it, independently of what any *particular* caller happens to instantiate).

GATE VERDICT: **(b) GATE FAIL, definitive.** Two machine-checked parts:

1. `compound_assumption_derivation` -- a genuine, closed `NIK TS5` term (not a hypothesis) that
   discharges a literally-compound (`P0 ∨ P1`) context assumption via ordinary `impI`+`assumption`,
   at depth 1 below the root (`Gt2`/`c2`, dispatch 1&2's own case-D graph). This is the concrete
   reachability witness the plan's question asked for.
2. `hOrFlat_concrete` -- NOT a hypothesis this time: concretely DERIVED, by unfolding `sigAt`'s
   actual `factsAt`-fold at `c2` (using only the landed, Preserved-Asset `sigAtFuel`/`bigAndL`
   machinery), that `Θ(Gt2, ΓCompound, r)` implies ONLY the flat `□(P0∨P1)` -- never the split
   `□P0 ∨ □P1` -- for exactly the `Γ` that (1) shows is genuinely reachable. Composing with
   dispatch 2's own `hOr_split_needs_bridge_from_flat` pattern (reused, not re-derived) shows
   closing the assumption case for this concrete, reachable `Γ` needs exactly the established
   non-theorem bridge, with no other route found among the landed CS5 axioms (same non-exhaustive-
   but-thorough search dispatch 1/2 already conducted; NOT re-attempted here per the hard
   instruction not to re-litigate the bridge).

CONCLUSION: the layered `Θ`/`place` candidate (dispatch 2) is **insufficient** to complete
`nik_adequacy` in general. The next redesign would have to make `sigAt`'s own context-fold
recursively split a compound fact's translation (mirroring what `place` already does for TARGET
formulas) -- but `sigAt` is an explicit Preserved Asset under this task's postmortem constraints
("do NOT touch or re-derive any Preserved Asset row"), so that fix is **out of Phase 9's remit**
and this dispatch does NOT attempt it. Phase 9's 3-dispatch cap is exhausted with a definitive
FAIL; the task must escalate for a re-plan (either lift the `sigAt`-frozen constraint, or abandon
the target-independent-`Θ` strategy for the alternative `nikTr`-per-label route already partially
landed in `Soundness.lean` -- `sigAt_assumption` closes assumption for free there, since it
concludes AT the assumption's own label with no boxing at all; that route's own documented
obstruction is a *different* one, `efq`/`orE`'s cross-label lowest-common-ancestor bridging,
`Soundness.lean:1889-1911` -- out of scope to adjudicate here).
-/
import Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Deduction

open Cslib.Logic.Modal
open Cslib.Logic.Modal.Labelled

namespace Probe537FinalGate

/-! ## `Θ`/`place`/`boxIter` -- verbatim from dispatch 2 (Preserved Assets: `sigAt` unchanged;
`place`'s `∨`-recursion is dispatch 2's own redesign, reused unmodified here). -/

open Classical in
noncomputable def orphanFacts {Atom : Type u} (G : Graph Atom) (Γ : List (LabelledFormula Atom))
    (root : Label Atom) : List (Proposition Atom) :=
  (Γ.filter (fun ψ => decide ¬ Relation.ReflTransGen G.R root ψ.lbl)).map LabelledFormula.prop

noncomputable def Theta {Atom : Type u} (G : Graph Atom) (Γ : List (LabelledFormula Atom))
    (hfin : G.X.Finite) (root : Label Atom) : Proposition Atom :=
  (sigAt G Γ hfin root).and (bigAndL (orphanFacts G Γ root))

def boxIter {Atom : Type u} : ℕ → Proposition Atom → Proposition Atom
  | 0, A => A
  | n + 1, A => Proposition.box (boxIter n A)

def place {Atom : Type u} (ht : Label Atom → ℕ) (x : Label Atom) :
    Proposition Atom → Proposition Atom
  | Proposition.or P Q => (place ht x P).or (place ht x Q)
  | A => boxIter (ht x) A

theorem place_or {Atom : Type u} (ht : Label Atom → ℕ) (x : Label Atom) (P Q : Proposition Atom) :
    place ht x (P.or Q) = (place ht x P).or (place ht x Q) := rfl

/-! ## Case-D graph infrastructure -- verbatim from dispatch 1/2 (`Gt`, `r`, `c2`, `Gt2`, `ht2`). -/

noncomputable abbrev Gt : Graph ℕ := Graph.trivial ℕ

theorem Gt_fin : (Gt).X.Finite := Set.finite_singleton _

abbrev r : Label ℕ := Label.var 0

abbrev c2 : Label ℕ := Label.var 2

noncomputable def Gt2 : Graph ℕ := Gt.addEdge r c2

theorem Gt2_fin : Gt2.X.Finite := by
  show (Gt.X ∪ ({r, c2} : Set (Label ℕ))).Finite
  exact Gt_fin.union ((Set.finite_singleton c2).insert r)

open Classical in
noncomputable def ht2 : Label ℕ → ℕ := Function.update (fun _ => 0) c2 1

theorem ht2_c2 : ht2 c2 = 1 := by
  classical
  simp [ht2]

/-- **`place` at `c2` on an atom is the flat `boxIter` fallback** (verbatim from dispatch 2's
`place_ht2_c2_atom`; `place` pattern-matches on its formula argument -- non-vacuously reducible
by `simp` only for a CONCRETE (non-`∨`) shape such as `atom k`, never for a generic `A`, since the
layered `place`'s `∨` branch means the match cannot unfold definitionally without knowing the
formula's top connective). Confirms `place`'s flat fallback genuinely applies to atomic
disjuncts, so the residual below is not about an empty family. -/
theorem place_ht2_c2_atom (k : ℕ) :
    place ht2 c2 (Proposition.atom k) = Proposition.box (Proposition.atom k) := by
  show boxIter (ht2 c2) (Proposition.atom k) = Proposition.box (Proposition.atom k)
  rw [ht2_c2]; rfl

/-! ## Part 1: REACHABILITY -- a genuine, closed `NIK TS5` derivation whose `assumption`
sub-derivation discharges a literally-compound context fact.

`P0 ∨ P1` is placed in `Γ` at label `c2` (depth 1 below root `r`, matching dispatch 1/2's own
case-D graph exactly) via the plain `assumption` constructor, then discharged via `impI` to prove
the entirely unremarkable theorem `c2 : (P0∨P1) ⊃ (P0∨P1)`. Nothing about this derivation is
adversarial or contrived: it is the syntactically simplest possible use of `impI`, instantiated at
`A := P0.or P1`. Since `Deduction.lean`'s `impI` constructor places **no** atomicity restriction on
its antecedent `A` (confirmed by reading `Deduction.lean:276-277`: `A B : Proposition Atom` are
fully generic), `NIK`'s own rule set forces `nik_adequacy`'s induction to visit exactly this
`assumption` sub-case, at exactly this `Γ`, for `nik_adequacy` to cover `impI` in general. -/

def P0 : Proposition ℕ := Proposition.atom 0
def P1 : Proposition ℕ := Proposition.atom 1

/-- The genuinely reachable, literally-compound context: `c2` is assigned the disjunctive fact
`P0 ∨ P1` directly. -/
abbrev ΓCompound : List (LabelledFormula ℕ) := [(c2 ∶ (P0.or P1))]

/-- The `assumption` sub-derivation: `Γ ⊢_G c2 : (P0∨P1)` via the plain context-lookup rule, at
the literally-compound fact `(c2 ∶ P0.or P1) ∈ ΓCompound`. -/
theorem compound_assumption_subderivation :
    NIK TS5 Gt2 ΓCompound (c2 ∶ (P0.or P1)) :=
  NIK.assumption Gt2 ΓCompound (c2 ∶ (P0.or P1)) (List.mem_singleton_self _)

/-- **The reachability witness**: a genuine, closed `NIK TS5` derivation of the unremarkable
theorem `c2 : (P0∨P1) ⊃ (P0∨P1)`, built by discharging `compound_assumption_subderivation` via
`impI`. This is a real derivation `nik_adequacy` (once landed) must be able to translate -- its
very existence, machine-checked here, answers the plan's reachability question: YES, a disjunctive
formula can appear in `Γ` at a label as an `assumption`, in derivations `nik_adequacy` must cover,
completely independently of what `cs5_completeness`'s canonical construction happens to produce
(since this derivation needs no completeness input at all -- it is a bare, self-contained `impI`
instance). -/
theorem compound_assumption_derivation :
    NIK TS5 Gt2 [] (c2 ∶ (P0.or P1).imp (P0.or P1)) :=
  NIK.impI Gt2 [] c2 (P0.or P1) (P0.or P1) compound_assumption_subderivation

#print axioms compound_assumption_derivation

/-! ## Part 2: `Θ` computes the FLAT form here, concretely -- not hypothesized.

`hOr_split_needs_bridge_from_flat` (dispatch 2) took its flat premise `hOrFlat` as an abstract
HYPOTHESIS. Here it is derived from `Θ`'s actual definition (`sigAt`'s `factsAt`-fold, the
Preserved Asset, used exactly as landed in `Cslib/.../Soundness.lean`, never modified) for the
concrete, just-shown-reachable `ΓCompound`. -/

theorem factsAt_ΓCompound_c2 : factsAt ΓCompound c2 = [P0.or P1] := by simp [factsAt]

theorem factsAt_ΓCompound_r : factsAt ΓCompound r = [] := by
  simp [factsAt, r, c2, Label.var.injEq]

theorem Gt2_R_r_c2 : Gt2.R r c2 := Or.inr ⟨rfl, rfl⟩

theorem Gt2_no_edges_from_c2 (x : Label ℕ) : ¬ Gt2.R c2 x := by
  rintro (h | ⟨heq, -⟩)
  · exact h
  · exact absurd heq (by simp [r, c2, Label.var.injEq])

/-- **`sigAtFuel` at `c2`, any remaining fuel, implies the flat conjunct `P0.or P1` directly**
(no boxing at this level -- `c2` is `Θ`'s recursion base since it has no outgoing `Gt2`-edges). -/
theorem sigAtFuel_ΓCompound_c2_imp (n : ℕ) :
    Derivable CS5ModalAxiom ((sigAtFuel Gt2 ΓCompound Gt2_fin n c2).imp (P0.or P1)) := by
  cases n with
  | zero =>
    simp only [sigAtFuel]
    exact bigAndL_mem (by rw [factsAt_ΓCompound_c2]; exact List.mem_singleton_self _)
  | succ n =>
    simp only [sigAtFuel]
    exact cs5_deriv_imp_trans ⟨.ax [] _ (.andE1 (bigAndL (factsAt ΓCompound c2)) _)⟩
      (bigAndL_mem (by rw [factsAt_ΓCompound_c2]; exact List.mem_singleton_self _))

/-- **`sigAt` at the root `r` implies `□(sigAtFuel n c2)`** for the one-step-reduced fuel `n`,
by extracting `c2`'s boxed subtree-conjunct out of `sigAt`'s own `bigAndL`-of-children fold via
plain conjunct-membership (`bigAndL_mem`), using ONLY `Gt2_R_r_c2` (`c2` is `r`'s unique child). -/
theorem sigAt_r_imp_box_sigAtFuel_c2 :
    Derivable CS5ModalAxiom ((sigAt Gt2 ΓCompound Gt2_fin r).imp
      (Proposition.box (sigAtFuel Gt2 ΓCompound Gt2_fin
        (Gt2_fin.toFinset.card - 1) c2))) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, Gt2_fin.toFinset.card = n + 1 :=
    ⟨Gt2_fin.toFinset.card - 1, (Nat.succ_pred_eq_of_pos (hfin_toFinset_card_pos Gt2_fin)).symm⟩
  have hnpred : Gt2_fin.toFinset.card - 1 = n := by omega
  rw [hnpred]
  have hu : sigAt Gt2 ΓCompound Gt2_fin r = sigAtFuel Gt2 ΓCompound Gt2_fin (n + 1) r := by
    unfold sigAt; rw [hn]
  rw [hu]
  simp only [sigAtFuel]
  have hCsub : {c | Gt2.R r c} ⊆ Gt2.X := fun c hc => (Gt2.edge_mem r c hc).2
  have hCfin : {c | Gt2.R r c}.Finite := Gt2_fin.subset hCsub
  have hc2mem : c2 ∈ hCfin.toFinset := hCfin.mem_toFinset.mpr Gt2_R_r_c2
  have hc2mem' : c2 ∈ hCfin.toFinset.toList := Finset.mem_toList.mpr hc2mem
  have hmapmem :
      Proposition.box (sigAtFuel Gt2 ΓCompound Gt2_fin n c2) ∈
        hCfin.toFinset.toList.map (fun c => Proposition.box (sigAtFuel Gt2 ΓCompound Gt2_fin n c)) :=
    List.mem_map.mpr ⟨c2, hc2mem', rfl⟩
  exact cs5_deriv_imp_trans ⟨.ax [] _ (.andE2 (bigAndL (factsAt ΓCompound r)) _)⟩
    (bigAndL_mem hmapmem)

/-- **Concretely derived flat form** (NOT a hypothesis): `Θ(Gt2, ΓCompound, r)` implies exactly
`□(P0∨P1)`, the flat boxed form -- obtained by chaining `sigAt_r_imp_box_sigAtFuel_c2` (root ⊃
box of `c2`'s subtree fold) with `cs5_deriv_box_mono` applied to `sigAtFuel_ΓCompound_c2_imp`
(lifting `c2`'s own fold ⊃ `P0∨P1` under `□`), then discarding `Θ`'s `orphanFacts` conjunct via
`andE1` (`c2` is NOT an orphan: `Gt2_R_r_c2` gives `ReflTransGen Gt2.R r c2`, so `orphanFacts`'s
filter excludes it -- `factsAt_ΓCompound_r`/orphan-exclusion is not even needed for THIS
direction, since `andE1` on `Theta`'s outer `.and` already isolates `sigAt` alone). -/
theorem hOrFlat_concrete :
    Derivable CS5ModalAxiom
      ((Theta Gt2 ΓCompound Gt2_fin r).imp (Proposition.box (P0.or P1))) := by
  have hstep : Derivable CS5ModalAxiom
      ((sigAt Gt2 ΓCompound Gt2_fin r).imp (Proposition.box (P0.or P1))) :=
    cs5_deriv_imp_trans sigAt_r_imp_box_sigAtFuel_c2
      (cs5_deriv_box_mono (sigAtFuel_ΓCompound_c2_imp _))
  exact cs5_deriv_imp_trans
    ⟨.ax [] _ (.andE1 (sigAt Gt2 ΓCompound Gt2_fin r) (bigAndL (orphanFacts Gt2 ΓCompound r)))⟩
    hstep

#print axioms hOrFlat_concrete

/-! ## Part 3: closing the (layered-`place`) assumption-case obligation for THIS concrete,
reachable `Γ` needs exactly the established non-theorem bridge -- reusing dispatch 2's
`hOr_split_needs_bridge_from_flat` argument shape, now applied to a concretely derived premise
instead of an assumed one. `bridge` is NOT re-derived or re-litigated here (forbidden by the
dispatch's hard requirements); it is carried as an explicit hypothesis, exactly as dispatch 1/2
did, and no landed CS5 axiom is known to supply it (same search dispatch 1/2 already conducted,
not repeated). -/

/-- **What closing `nik_adequacy`'s assumption case for `ΓCompound` needs.** Given `bridge`
(dispatch 1/2's established non-theorem), the layered `place`'s split-form obligation
`Θ(Gt2,ΓCompound,r) ⊃ ((place ht2 c2 P0).or (place ht2 c2 P1))` -- i.e. exactly what
`nik_adequacy`, applied to `compound_assumption_subderivation`, must produce -- closes. Absent
`bridge`, no route was found (dispatch 1/2's finding, reused, not re-attempted here). -/
theorem caseD_assumption_needs_bridge
    (bridge : Derivable CS5ModalAxiom
      ((Proposition.box (P0.or P1)).imp ((Proposition.box P0).or (Proposition.box P1)))) :
    Derivable CS5ModalAxiom
      ((Theta Gt2 ΓCompound Gt2_fin r).imp ((place ht2 c2 P0).or (place ht2 c2 P1))) := by
  have hP0 : place ht2 c2 P0 = Proposition.box P0 := place_ht2_c2_atom 0
  have hP1 : place ht2 c2 P1 = Proposition.box P1 := place_ht2_c2_atom 1
  rw [hP0, hP1]
  exact cs5_deriv_imp_trans hOrFlat_concrete bridge

#print axioms caseD_assumption_needs_bridge

/-! ## Final gate verdict

`compound_assumption_derivation` (Part 1) is a genuine, sorry-free, closed `NIK TS5` term showing
the assumption-of-a-compound-fact scenario is REACHABLE -- not a hypothetical edge case, but the
unavoidable content of `nik_adequacy`'s `impI` case in full generality. `hOrFlat_concrete`
(Part 2) is a genuine, sorry-free, concretely DERIVED fact (no hypothesis smuggled in) showing
`Θ`'s Preserved-Asset fold produces ONLY the flat form for this exact, reachable `Γ`.
`caseD_assumption_needs_bridge` (Part 3) shows closing the resulting split-form obligation needs
exactly the established non-theorem bridge, with no alternative route known.

GATE VERDICT: **(b) GATE FAIL, definitive.** The layered `Θ`/`place` candidate from dispatch 2
cannot complete `nik_adequacy` in general: this dispatch exhibits a genuine derivation forcing
the exact obstruction dispatch 2 could only pose hypothetically. The obstruction is not a gap in
proof search effort -- it is structurally forced by `sigAt`'s WHOLESALE (non-recursive)
`factsAt`-fold, which cannot see inside a context fact's own top connective, combined with `place`
recursing into `∨` only at the point of TARGET translation, never inside `Θ`'s CONTEXT
translation. Fixing this would require `sigAt` itself to split compound context facts recursively
-- exactly the kind of change the postmortem constraints forbid (`sigAt` is a Preserved Asset).
Phase 9's 3-dispatch cap is exhausted with a definitive FAIL; escalate for a re-plan rather than
attempt a 4th probe dispatch or silently proceed to Phase 10.
-/

end Probe537FinalGate
