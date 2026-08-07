module

import Cslib.Init
import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
import Mathlib.Tactic.Ring
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Defs
public meta import Cslib.Foundations.Logic.Tableau.Branch

/-!
# Gate A prototype: variant selection probe (V1 vs V4), scratch only

Re-runs task 574's variant-selection methodology
(`specs/archive/574_.../handoffs/01_variant-selection.md`) against the POST-Phase-6 tree
(post `a70187dd`, ancestor-directed blocking active, self-copy channel removed -- i.e. "V3"
in 574's own naming is the CURRENT unmodified library). Measures whether reinstating the
self-copy channel verbatim (**V1**) or generalizing it to copy every positive formula (**V4**)
still terminates on the complexity-9 divergence witness, and whether the propositional
conformance corpus still matches, BEFORE any change is made to `Cslib/`.

No writes to `Cslib/` or `CslibTests/`.
-/

open Cslib.Logic.PL
open Cslib.Logic.Tableau

/-! ## Witness formula and conformance corpus (copied verbatim from
`CslibTests/TableauConformance.lean`'s `PropositionalCorpus` section, same atom encoding) -/

def ia : Proposition Nat := .atom 0
def ib : Proposition Nat := .atom 1
def ic : Proposition Nat := .atom 2
def id_ : Proposition Nat := .atom 3
def ie : Proposition Nat := .atom 4
def if_ : Proposition Nat := .atom 5
def iu1 : Proposition Nat := .atom 6
def iv1 : Proposition Nat := .atom 7
def iu2 : Proposition Nat := .atom 8
def iv2 : Proposition Nat := .atom 9

/-- Divergence-witness formula φ0, complexity 9. -/
def phi0 : Proposition Nat :=
  ((((ia → ib) → ic) ∧ ((id_ → ie) → if_)) → ((iu1 → iv1) ∨ (iu2 → iv2)))

/-- The 20-row propositional conformance corpus (formula, expected verdict), copied verbatim. -/
def confCorpus : List (Proposition Nat × String) :=
  [ (ia → ia, "CLOSED"),
    (ia → (ib → ia), "CLOSED"),
    (ib → (ia → ib), "CLOSED"),
    (((ia → ib) ∧ ia) → ib, "CLOSED"),
    (¬ (ia ∧ ¬ ia), "CLOSED"),
    ((ia → (ib → ic)) → ((ia → ib) → (ia → ic)), "CLOSED"),
    ((¬ ia ∨ ib) → (ia → ib), "CLOSED"),
    ((ia → ib) → (¬ ib → ¬ ia), "CLOSED"),
    ((ia → ic) → ((ib → ic) → ((ia ∨ ib) → ic)), "CLOSED"),
    ((ia ∧ (ib ∨ ic)) → ((ia ∧ ib) ∨ (ia ∧ ic)), "CLOSED"),
    ((ia → ib) → ((ib → ic) → (ia → ic)), "CLOSED"),
    (((ia → ib) → (ia → ic)) → (ia → (ib → ic)), "CLOSED"),
    (¬ (¬ (¬ ia)) → ¬ ia, "CLOSED"),
    (((ia → ib) → ic) → (ib → ic), "CLOSED"),
    (((ia → ib) → ia) → ia, "OPEN"),
    ((ia → ib) ∨ (ib → ia), "OPEN"),
    (¬ (ia ∧ ib) → (¬ ia ∨ ¬ ib), "OPEN"),
    (¬ ia ∨ ¬ (¬ ia), "OPEN"),
    ((¬ ia → (ib ∨ ic)) → ((¬ ia → ib) ∨ (¬ ia → ic)), "OPEN"),
    (phi0, "OPEN") ]

/-! ## worldStats adapter (mirrors `Expansion.lean`'s own methodology: max label reached) -/

def branchMaxLabel (b : IBranch Nat) : Nat :=
  (b.map (·.label)).foldl max 0

def resultStats (r : IntTableauResult Nat) : String × Nat × Nat :=
  match r with
  | .closed => ("CLOSED", 0, 0)
  | .openBranch b => ("OPEN", branchMaxLabel b, b.length)

/-! ## V1: self-copy channel reinstated verbatim (as removed by `a70187dd`) -/

def applyAllTImpRulesV1 (b : IBranch Nat) (edges : IEdges) : IBranch Nat :=
  let newForms :=
    b.filterMap fun sf =>
      match sf.sign, sf.formula with
      | .pos, .imp φ ψ =>
        let toAdd := intTImpRule φ ψ sf.label edges b
        let accessibleWorlds :=
          (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
        let copies := accessibleWorlds.filterMap fun w' =>
          if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
            none
          else
            some (⟨.pos, sf.formula, w'⟩ : ISF Nat)
        let combined := toAdd ++ copies
        if combined.isEmpty then none else some combined
      | _, _ => none
  b ++ newForms.flatten

def applyPersistenceFixpointV1 (b : IBranch Nat) (edges : IEdges) (fuel : Nat) : IBranch Nat :=
  match fuel with
  | 0 => b
  | fuel' + 1 =>
    let b' := applyAllTImpRulesV1 b edges
    if b'.length == b.length then b else applyPersistenceFixpointV1 b' edges fuel'

/-! ## V4: generalized channel -- copy EVERY positive formula to accessible worlds lacking it -/

def applyAllTImpRulesV4 (b : IBranch Nat) (edges : IEdges) : IBranch Nat :=
  let newForms :=
    b.filterMap fun sf =>
      match sf.sign, sf.formula with
      | .pos, .imp φ ψ =>
        let toAdd := intTImpRule φ ψ sf.label edges b
        if toAdd.isEmpty then none else some toAdd
      | _, _ => none
  -- Generalized channel: every POSITIVE formula on the branch, copied to every accessible
  -- world lacking its own copy (not just T-implications).
  let genCopies :=
    b.filterMap fun sf =>
      match sf.sign with
      | .pos =>
        let accessibleWorlds :=
          (b.map (·.label)).eraseDups.filter (isAccessible edges sf.label ·)
        let copies := accessibleWorlds.filterMap fun w' =>
          if b.any (fun y => y.sign == .pos && y.formula == sf.formula && y.label == w') then
            none
          else
            some (⟨.pos, sf.formula, w'⟩ : ISF Nat)
        if copies.isEmpty then none else some copies
      | _ => none
  b ++ newForms.flatten ++ genCopies.flatten

def applyPersistenceFixpointV4 (b : IBranch Nat) (edges : IEdges) (fuel : Nat) : IBranch Nat :=
  match fuel with
  | 0 => b
  | fuel' + 1 =>
    let b' := applyAllTImpRulesV4 b edges
    if b'.length == b.length then b else applyPersistenceFixpointV4 b' edges fuel'

/-! ## Local expansion-loop copies (structure mirrors `intExpandBranches`/`.go` exactly;
only the persistence-fixpoint call differs). Termination helpers recreated locally since the
real ones are `private` to `Scheme.lean`. -/

private lemma sum_map_pow_const' {α : Type*} (l : List α) (c : Nat) :
    ((l.map (fun _ => c)).map (fun fl => 3 ^ fl)).sum = l.length * 3 ^ c := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

private lemma lex_lt_of_le_of_lt' {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.eq_or_lt_of_le ha with heq | hlt
  · subst heq
    exact Prod.Lex.right a' hb
  · exact Prod.Lex.left _ _ hlt

def goV1
    (closurePred : IBranch Nat → Bool)
    (pending : List (IBranch Nat))
    (pendingExp : List (List (ISF Nat)))
    (pendingNW : List Nat)
    (pendingEdges : List IEdges)
    (pendingFuels : List Nat)
    (done : List (IBranch Nat))
    (doneExp : List (List (ISF Nat)))
    (doneNW : List Nat)
    (doneEdges : List IEdges)
    (doneFuels : List Nat) :
    IntTableauResult Nat :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingFuels with
  | [], _, _, _, _ => .closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, f :: restFs =>
    let bPers := applyPersistenceFixpointV1 b edges f
    if closurePred bPers then
      goV1 closurePred restBs restEs restNW restEdges restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneFuels ++ [f])
    else
      match f with
      | 0 => .openBranch bPers
      | f' + 1 =>
        match _hstep : intStepBranch bPers e nw with
        | none => .openBranch bPers
        | some (.linearResult newForms nw' newEdge, newExp) =>
          match newEdge with
          | none =>
            goV1 closurePred
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges] ++ restEdges)
              (doneFuels ++ [f'] ++ restFs)
              [] [] [] [] []
          | some newE =>
            match intFImpReuseWitnessAnc? bPers edges newForms newE with
            | some _x =>
              goV1 closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] []
            | none =>
              goV1 closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] []
        | some (.branchingResult branches' nw', newExp) =>
          goV1 closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] []
        | some (.notApplicable, _) => .openBranch bPers
  | _ :: restBs, _pExp, _pNW, _pEdges, _pFuels =>
    goV1 closurePred restBs [] [] [] [] done doneExp doneNW doneEdges doneFuels
termination_by
  (((pendingFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum, pending.length)
decreasing_by
  · have hsum : ((restFs ++ (doneFuels ++ [f])).map (fun fl => 3 ^ fl)).sum
        = (((f :: restFs) ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega
    rw [hsum]
    exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have hlen : branches'.length = 2 := intStepBranch_branchingResult_length _hstep
    have hconst := sum_map_pow_const' branches' f'
    rw [hlen] at hconst
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.append_nil, hconst]
    omega
  · have hle : ((([] : List Nat) ++ doneFuels).map (fun fl => 3 ^ fl)).sum
        ≤ ((_pFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.nil_append, List.map_append, List.sum_append]
      omega
    exact lex_lt_of_le_of_lt' hle (by simp)

def expandV1 (φ : Proposition Nat) (fuel : Nat) : IntTableauResult Nat :=
  goV1 isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [fuel] [] [] [] [] []

-- V4 uses the identical loop shape; only the persistence step differs. Duplicated (not
-- parametrized over the persistence function) to keep each variant's termination proof
-- independent and simple, matching 574's own probe methodology.
def goV4
    (closurePred : IBranch Nat → Bool)
    (pending : List (IBranch Nat))
    (pendingExp : List (List (ISF Nat)))
    (pendingNW : List Nat)
    (pendingEdges : List IEdges)
    (pendingFuels : List Nat)
    (done : List (IBranch Nat))
    (doneExp : List (List (ISF Nat)))
    (doneNW : List Nat)
    (doneEdges : List IEdges)
    (doneFuels : List Nat) :
    IntTableauResult Nat :=
  match pending, pendingExp, pendingNW, pendingEdges, pendingFuels with
  | [], _, _, _, _ => .closed
  | b :: restBs, e :: restEs, nw :: restNW, edges :: restEdges, f :: restFs =>
    let bPers := applyPersistenceFixpointV4 b edges f
    if closurePred bPers then
      goV4 closurePred restBs restEs restNW restEdges restFs
        (done ++ [bPers]) (doneExp ++ [e]) (doneNW ++ [nw]) (doneEdges ++ [edges])
        (doneFuels ++ [f])
    else
      match f with
      | 0 => .openBranch bPers
      | f' + 1 =>
        match _hstep : intStepBranch bPers e nw with
        | none => .openBranch bPers
        | some (.linearResult newForms nw' newEdge, newExp) =>
          match newEdge with
          | none =>
            goV4 closurePred
              (done ++ [Branch.extendMany bPers newForms] ++ restBs)
              (doneExp ++ [newExp] ++ restEs)
              (doneNW ++ [nw'] ++ restNW)
              (doneEdges ++ [edges] ++ restEdges)
              (doneFuels ++ [f'] ++ restFs)
              [] [] [] [] []
          | some newE =>
            match intFImpReuseWitnessAnc? bPers edges newForms newE with
            | some _x =>
              goV4 closurePred
                (done ++ [bPers] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw] ++ restNW)
                (doneEdges ++ [edges] ++ restEdges)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] []
            | none =>
              goV4 closurePred
                (done ++ [Branch.extendMany bPers newForms] ++ restBs)
                (doneExp ++ [newExp] ++ restEs)
                (doneNW ++ [nw'] ++ restNW)
                (doneEdges ++ [edges ++ [newE]] ++ restEdges)
                (doneFuels ++ [f'] ++ restFs)
                [] [] [] [] []
        | some (.branchingResult branches' nw', newExp) =>
          goV4 closurePred
            (done ++ branches'.map (Branch.extendMany bPers ·) ++ restBs)
            (doneExp ++ branches'.map (fun _ => newExp) ++ restEs)
            (doneNW ++ branches'.map (fun _ => nw') ++ restNW)
            (doneEdges ++ branches'.map (fun _ => edges) ++ restEdges)
            (doneFuels ++ branches'.map (fun _ => f') ++ restFs)
            [] [] [] [] []
        | some (.notApplicable, _) => .openBranch bPers
  | _ :: restBs, _pExp, _pNW, _pEdges, _pFuels =>
    goV4 closurePred restBs [] [] [] [] done doneExp doneNW doneEdges doneFuels
termination_by
  (((pendingFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum, pending.length)
decreasing_by
  · have hsum : ((restFs ++ (doneFuels ++ [f])).map (fun fl => 3 ^ fl)).sum
        = (((f :: restFs) ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega
    rw [hsum]
    exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, List.append_nil]
    omega
  · apply Prod.Lex.left
    have hlen : branches'.length = 2 := intStepBranch_branchingResult_length _hstep
    have hconst := sum_map_pow_const' branches' f'
    rw [hlen] at hconst
    have h1 : 1 ≤ (3 : Nat) ^ f' := Nat.one_le_pow _ _ (by norm_num)
    simp only [List.map_append, List.map_cons, List.sum_append,
      List.sum_cons, List.append_nil, hconst]
    omega
  · have hle : ((([] : List Nat) ++ doneFuels).map (fun fl => 3 ^ fl)).sum
        ≤ ((_pFuels ++ doneFuels).map (fun fl => 3 ^ fl)).sum := by
      simp only [List.nil_append, List.map_append, List.sum_append]
      omega
    exact lex_lt_of_le_of_lt' hle (by simp)

def expandV4 (φ : Proposition Nat) (fuel : Nat) : IntTableauResult Nat :=
  goV4 isIntuitionisticallyClosed [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [fuel] [] [] [] [] []

def expandControl (φ : Proposition Nat) (fuel : Nat) : IntTableauResult Nat :=
  intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [fuel] isIntuitionisticallyClosed

/-! ## Measurements -/

-- True control fidelity check: does the REAL library's `intuitionisticTableau` on φ0 agree
-- with `expandControl` at an explicit fuel matching 574's own V3 saturation point?
#eval resultStats (expandControl phi0 120)      -- expect OPEN, maxLabel = 21 (574 Table 3, V3)
#eval resultStats (intuitionisticTableau phi0)   -- real entry point, sanity cross-check

-- V1 fuel ladder
#eval resultStats (expandV1 phi0 10)
#eval resultStats (expandV1 phi0 20)
#eval resultStats (expandV1 phi0 40)
#eval resultStats (expandV1 phi0 80)
#eval resultStats (expandV1 phi0 120)

-- V4 fuel ladder
#eval resultStats (expandV4 phi0 10)
#eval resultStats (expandV4 phi0 20)
#eval resultStats (expandV4 phi0 40)
#eval resultStats (expandV4 phi0 80)
#eval resultStats (expandV4 phi0 120)

-- Spot-check saturation stability at higher fuel (574's own methodology)
#eval resultStats (expandV1 phi0 160)
#eval resultStats (expandV1 phi0 200)
#eval resultStats (expandV4 phi0 160)
#eval resultStats (expandV4 phi0 200)

-- Conformance check: does each variant's verdict (at generous fixed fuel) match the expected
-- verdict for all 20 rows of the propositional corpus?
def checkConformance (expand : Proposition Nat → Nat → IntTableauResult Nat) (fuel : Nat) :
    List (Bool × String) :=
  confCorpus.map fun (φ, expected) =>
    let got := (resultStats (expand φ fuel)).1
    (got == expected, got)

#eval (checkConformance expandV1 400).map Prod.fst
#eval (checkConformance expandV4 400).map Prod.fst
