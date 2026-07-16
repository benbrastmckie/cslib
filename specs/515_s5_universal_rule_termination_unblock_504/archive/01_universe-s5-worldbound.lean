/-
ARCHIVE -- NOT BUILT, NOT IMPORTED.

Retired cluster 01: the S5-specific finite universe `modalUniverseS5` / world bound
`modalWorldBoundS5`, their membership lemmas, and the `modalUniverseS5`-based
outputs-subset chain that existed only to discharge `S5LoopInv`'s `bClosure` field.

This file is archival: it is not in the `Cslib/` tree, carries no `import Cslib.Init`, is
not listed in `Cslib.lean`, and is never seen by `lake build` / `checkInitImports` /
`mk_all`. The blocks below will NOT compile as lifted out of context (they depend on the
surrounding file's variables, imports, and `omit` scopes); that is expected for an archive.
Each block's provenance header carries the `git` coordinates that recover a compiling
version.

NOTE on scope: `modalSubfmls_trans_S5`, `modalSubfmls_self_mem_S5`, and
`mem_boxPositivesOf_S5` were resolved by NAME to be LIVE (consumed by the witness-rule
counting crux and `modalApplyOneS5w_outputsSubsetUniverse`) and deliberately REMAIN in the
live tree; they are not archived here despite sitting inside the retired region's original
line span.
-/

-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:72-131
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `modalUniverse` / `modalWorldBound` (`FmpMeasure.lean`), reused verbatim at K's own universe -- see `modalOps`/`mintTags` and `modalMaxWorld_lt_worldBound_of_S5w` (`S5Simplification.lean`)
-- Why retired: the linear budget arithmetic retargeted the S5 termination chain at K's OWN universe and world bound, over which `modalExpMeasure_entry_le_fuel` already applies verbatim; a separate S5 universe/bound became unnecessary rather than wrong.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

/-! ## S5 World Bound and Universe (task 515 Phase 1)

`modalWorldBound`/`modalUniverse` (`FmpMeasure.lean`) are a branching^depth *tree* bound: S5's
universal-cluster world graph is not a bounded-depth tree (the universal rule re-broadcasts
across the whole known-world set, `S5Simplification.lean`'s module docstring), so this bound
does not transfer, exactly as it does not transfer to S4 (`LoopChecking.lean`'s `modalWorldBoundS4`
correction). `modalWorldBoundS5`/`modalUniverseS5` mirror `modalWorldBoundS4`/`modalUniverseS4`
(`LoopChecking.lean:229/235/245`) verbatim: the pigeonhole bound `2 ^ (2 * |modalSubfmls φ₀|)`,
the number of possible signed-relevant-formula sets a birth-key loop-checking argument
(`S5LoopInv`, Phase 3) can inject into. -/

/-- The S5 world bound: `2 ^ (2 * |modalSubfmls φ₀|)`, the number of possible
signed-relevant-formula sets, mirroring `modalWorldBoundS4` (`LoopChecking.lean:229`). -/
def modalWorldBoundS5 (φ₀ : Proposition Atom) : Nat :=
  2 ^ (2 * (modalSubfmls φ₀).length)

/-- The fixed finite signed-formula universe `U_{S5}(φ₀)`: both signs, every subformula of
`φ₀`, at every world label `0 .. modalWorldBoundS5 φ₀`. Mirrors `modalUniverseS4`
(`LoopChecking.lean:235`) with `modalWorldBoundS5` swapped in for `modalWorldBoundS4`. -/
def modalUniverseS5 (φ₀ : Proposition Atom) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (List.range (modalWorldBoundS5 φ₀ + 1)).flatMap (fun w =>
    (modalSubfmls φ₀).flatMap (fun ψ => [⟨.pos, ψ, w⟩, ⟨.neg, ψ, w⟩]))

/-- The S5 universe has length at most
`2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS5 φ₀ + 1)`. Mirrors
`modalUniverseS4_length_le` (`LoopChecking.lean:245`) verbatim, `S4` swapped for `S5`. -/
lemma modalUniverseS5_length_le (φ₀ : Proposition Atom) :
    (modalUniverseS5 φ₀).length ≤
      2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS5 φ₀ + 1) := by
  have hinner : ∀ w : WorldIndex,
      ((modalSubfmls φ₀).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length
        ≤ 2 * (2 * modalComplexity φ₀ + 1) := by
    intro w
    rw [List.length_flatMap]
    have hb : (List.map (fun ψ =>
        ([(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex), ⟨.neg, ψ, w⟩]).length)
        (modalSubfmls φ₀)).sum ≤ (modalSubfmls φ₀).length * 2 :=
      sum_map_le_length_mul (modalSubfmls φ₀) _ 2 (fun ψ _ => by simp)
    have hlen := modalSubfmls_length_le φ₀
    omega
  unfold modalUniverseS5
  rw [List.length_flatMap]
  have houter : (List.map (fun w =>
      ((modalSubfmls φ₀).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBoundS5 φ₀ + 1))).sum
      ≤ (List.range (modalWorldBoundS5 φ₀ + 1)).length * (2 * (2 * modalComplexity φ₀ + 1)) :=
    sum_map_le_length_mul (List.range (modalWorldBoundS5 φ₀ + 1)) _
      (2 * (2 * modalComplexity φ₀ + 1)) (fun w _ => hinner w)
  rw [List.length_range] at houter
  calc (List.map (fun w =>
        ((modalSubfmls φ₀).flatMap
          (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                      ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBoundS5 φ₀ + 1))).sum
      ≤ (modalWorldBoundS5 φ₀ + 1) * (2 * (2 * modalComplexity φ₀ + 1)) := houter
    _ = 2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS5 φ₀ + 1) := by ring


-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:177-216
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `mem_modalUniverse_of`-style membership at K's universe (`FmpMeasure.lean`); the live S5w chain uses `mem_modalUniverse_of_S5w` / `modalUniverse_mem_formula_S5w` (`S5Simplification.lean`)
-- Why retired: membership lemmas for `modalUniverseS5`, which is itself retired above; `bClosure` support for the retired `S5LoopInv`.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma mem_modalUniverse_of` (unavailable
across files): a signed formula with any sign, a subformula of `φ₀`, at a world label within the
`modalWorldBoundS5` bound, is in `U_{S5}(φ₀)`. -/
private lemma mem_modalUniverseS5_of {φ₀ : Proposition Atom} {s : Sign} {φ : Proposition Atom}
    {w : WorldIndex} (hw : w ≤ modalWorldBoundS5 φ₀) (hφ : φ ∈ modalSubfmls φ₀) :
    (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverseS5 φ₀ := by
  have hlt : w < modalWorldBoundS5 φ₀ + 1 := Nat.lt_succ_of_le hw
  simp only [modalUniverseS5, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Generic form of `mem_modalUniverseS5_of`, stated for an arbitrary signed formula `z`. -/
private lemma mem_modalUniverseS5_of' {φ₀ : Proposition Atom}
    {z : SignedFormula (Proposition Atom) WorldIndex}
    (hw : z.label ≤ modalWorldBoundS5 φ₀) (hφ : z.formula ∈ modalSubfmls φ₀) :
    z ∈ modalUniverseS5 φ₀ := by
  obtain ⟨s, φ, w⟩ := z
  exact mem_modalUniverseS5_of hw hφ

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalUniverse_mem_formula`
(unavailable across files): extraction of the formula-component bound. -/
private lemma modalUniverseS5_mem_formula {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS5 φ₀) :
    x.formula ∈ modalSubfmls φ₀ := by
  simp only [modalUniverseS5, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalUniverse_mem_label`
(unavailable across files): extraction of the label-component bound. -/
private lemma modalUniverseS5_mem_label {φ₀ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverseS5 φ₀) :
    x.label ≤ modalWorldBoundS5 φ₀ := by
  simp only [modalUniverseS5, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, ψ, -, heq | heq⟩ := hx <;> (subst heq; exact Nat.lt_succ_iff.mp hw)


-- ARCHIVED from Cslib/Logics/Modal/Tableau/S5Simplification.lean:974-1258
-- Retired: 2026-07-16, task 515 phase 14 (plan v4)
-- Superseded by: `modalApplyOneS5w_outputsSubsetUniverse` (`S5Simplification.lean`), stated at K's universe and discharged as a `RuleApplicationSpecCore` field
-- Why retired: the `modalUniverseS5`-based outputs-subset chain terminating in `modalApplyOneS5_outputs_subset`, whose only consumer was the retired `S5LoopInv`'s `bClosure` preservation. It takes `modalMaxWorld b < modalWorldBoundS5 φ₀` as an INPUT, so it could never establish the world bound itself.
-- Status at retirement: CI-green, sorry-free, zero axioms beyond propext/Classical.choice/Quot.sound
-- Recover a compiling version at: git show af59318098f7ed0eceb7a33634d072babb45b603 -- Cslib/Logics/Modal/Tableau/S5Simplification.lean

omit [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma boxProps_outputs_subset`
(unavailable across files), swapped to `modalUniverseS5`/`modalWorldBoundS5`: the box-positives
group propagated by both fresh-world rules (`diamondPos`, `boxNeg`) stays inside
`U_{S5}(φ₀)`. -/
private lemma boxProps_outputs_subset_S5 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS5 φ₀) :
    ∀ x ∈ (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none),
    x ∈ modalUniverseS5 φ₀ := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨⟨ψ, src⟩, hψsrc, heq⟩ := hx
  split at heq
  · split at heq
    · simp at heq
    · simp only [Option.some.injEq] at heq
      subst heq
      have hψbox : (⟨.pos, .box ψ, src⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := mem_boxPositivesOf_S5 hψsrc
      have hψsub : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
        modalUniverseS5_mem_formula (hb _ hψbox)
      have hψmem : ψ ∈ modalSubfmls (Proposition.box ψ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 ψ)
      exact mem_modalUniverseS5_of hwbound (modalSubfmls_trans_S5 hψmem hψsub)
  · simp at heq

omit [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma diaNegProps_outputs_subset`
(unavailable across files), swapped to `modalUniverseS5`/`modalWorldBoundS5`: the
diamond-negatives group propagated by both fresh-world rules stays inside `U_{S5}(φ₀)`. -/
private lemma diaNegProps_outputs_subset_S5 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hwbound : modalNextWorld b ≤ modalWorldBoundS5 φ₀) :
    ∀ x ∈ b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none),
    x ∈ modalUniverseS5 φ₀ := by
  intro x hx
  simp only [List.mem_filterMap] at hx
  obtain ⟨sf', hsf'mem, heq⟩ := hx
  split at heq
  · split at heq
    · rename_i ψ hform
      split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq
        subst heq
        have hψsub : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ := by
          have hmem := modalUniverseS5_mem_formula (hb sf' hsf'mem)
          rwa [hform] at hmem
        have hψmem : ψ ∈ modalSubfmls (Proposition.diamond ψ) :=
          List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 ψ)
        exact mem_modalUniverseS5_of hwbound (modalSubfmls_trans_S5 hψmem hψsub)
    · simp at heq
  · simp at heq

omit [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s
`private lemma modalApplyOne_diamondPos_outputs_subset` (unavailable across files, swapped to
`modalUniverseS5`/`modalWorldBoundS5`): `diamondPos`'s
three emitted groups (witness, propagated box-positives, propagated diamond-negatives) all stay
inside `U_{S5}(φ₀)`, given the branch invariant, source membership, and the S5 world-bound
hypothesis (consumed for the fresh label `modalNextWorld b ≤ modalWorldBoundS5 φ₀`). -/
lemma modalApplyOne_diamondPos_outputs_subset_S5
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hsf : (⟨.pos, .diamond φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hW : modalMaxWorld b < modalWorldBoundS5 φ₀) :
    ∀ x ∈ ((⟨.pos, φ, modalNextWorld b⟩ :
        SignedFormula (Proposition Atom) WorldIndex) ::
      (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none) ++
      b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none)),
    x ∈ modalUniverseS5 φ₀ := by
  have hwbound : modalNextWorld b ≤ modalWorldBoundS5 φ₀ := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.diamond φ) ∈ modalSubfmls φ₀ :=
    modalUniverseS5_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) :=
    List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverseS5_of hwbound (modalSubfmls_trans_S5 hφmem hsrc)
  · exact boxProps_outputs_subset_S5 φ₀ b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset_S5 φ₀ b w hb hwbound x hdia

omit [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalApplyOne_boxNeg_outputs_subset`
(unavailable across files, swapped to `modalUniverseS5`/`modalWorldBoundS5`): symmetric to
`modalApplyOne_diamondPos_outputs_subset_S5`. -/
lemma modalApplyOne_boxNeg_outputs_subset_S5
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀)
    (hsf : (⟨.neg, .box φ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hW : modalMaxWorld b < modalWorldBoundS5 φ₀) :
    ∀ x ∈ ((⟨.neg, φ, modalNextWorld b⟩ :
        SignedFormula (Proposition Atom) WorldIndex) ::
      (boxPositivesOf b).filterMap (fun (ψ, src) =>
        if src == w then
          let sf' : SignedFormula (Proposition Atom) WorldIndex :=
            ⟨.pos, ψ, modalNextWorld b⟩
          if b.any (· == sf') then none else some sf'
        else none) ++
      b.filterMap (fun sf' =>
        if sf'.sign == .neg && sf'.label == w then
          match sf'.formula with
          | .diamond ψ =>
            let prop : SignedFormula (Proposition Atom) WorldIndex :=
              ⟨.neg, ψ, modalNextWorld b⟩
            if b.any (· == prop) then none else some prop
          | _ => none
        else none)),
    x ∈ modalUniverseS5 φ₀ := by
  have hwbound : modalNextWorld b ≤ modalWorldBoundS5 φ₀ := by
    unfold modalNextWorld; exact hW
  have hsrc : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS5_mem_formula (hb _ hsf)
  have hφmem : φ ∈ modalSubfmls (Proposition.box φ) :=
    List.mem_cons_of_mem _ (modalSubfmls_self_mem_S5 φ)
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with (rfl | hbox) | hdia
  · exact mem_modalUniverseS5_of hwbound (modalSubfmls_trans_S5 hφmem hsrc)
  · exact boxProps_outputs_subset_S5 φ₀ b w hb hwbound x hbox
  · exact diaNegProps_outputs_subset_S5 φ₀ b w hb hwbound x hdia

/-- Local re-derivation of `FmpMeasure.lean`'s `lemma modalApplyOne_outputs_subset`, swapped to
`modalUniverseS5`/`modalWorldBoundS5`: every signed formula emitted by K's OWN `modalApplyOne
sf b acc` stays inside `U_{S5}(φ₀)`, given the branch invariant, source membership, the
freshness invariant, and the S5 world-bound hypothesis. Dispatches over the five `modalApplyOne`
outcomes exactly as the K-file's top-level dispatch does. This is purely about `modalApplyOne`
(K), independent of any S5 merge; `modalApplyOneS5_outputs_subset` (below) builds on this for the
two S5-relevant shapes. -/
lemma modalApplyOne_outputs_subset_S5
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS5 φ₀) (hsf : sf ∈ b)
    (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBoundS5 φ₀) :
    (match (modalApplyOne sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverseS5 φ₀
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverseS5 φ₀
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverseS5 φ₀
      | .notApplicable => True) := by
  have hsfU : sf ∈ modalUniverseS5 φ₀ := hb sf hsf
  have hprop := modalApplyOne_prop_outputs_subset sf
  unfold modalApplyOne
  by_cases hpa :
      (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
  · simp only [hpa, if_true]
    rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
      formulas | branches | formulas | -
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzform, hzlabel⟩ := hprop z hz
      refine mem_modalUniverseS5_of' ?_
        (modalSubfmls_trans_S5 hzform (modalUniverseS5_mem_formula hsfU))
      rw [hzlabel]; exact modalUniverseS5_mem_label hsfU
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzform, hzlabel⟩ := hprop z hz
      refine mem_modalUniverseS5_of' ?_
        (modalSubfmls_trans_S5 hzform (modalUniverseS5_mem_formula hsfU))
      rw [hzlabel]; exact modalUniverseS5_mem_label hsfU
    · rw [hpr] at hprop
      intro z hz
      obtain ⟨hzform, hzlabel⟩ := hprop z hz
      refine mem_modalUniverseS5_of' ?_
        (modalSubfmls_trans_S5 hzform (modalUniverseS5_mem_formula hsfU))
      rw [hzlabel]; exact modalUniverseS5_mem_label hsfU
    · rw [hpr] at hpa
      simp [RuleResult.isApplicable] at hpa
  · rw [if_neg hpa]
    obtain ⟨s, ff, l⟩ := sf
    rcases s with _ | _
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp
      · simp
      · simp
      · simp
      · simp
      · dsimp only
        by_cases hemp : (boxPropagation b acc φ l).isEmpty = true
        · simp only [if_pos hemp]
        · simp only [if_neg hemp]
          intro x hx
          obtain ⟨hxform, hxsucc⟩ := modalApplyOne_boxPos_outputs_subset b acc φ l x hx
          have hedge : acc.hasEdge l x.label = true := mem_successorsOf_hasEdge_S5 hxsucc
          have hxlt := (hInv l x.label hedge).2
          have hxle : x.label ≤ modalMaxWorld b := Nat.lt_succ_iff.mp hxlt
          exact mem_modalUniverseS5_of' (Nat.le_of_lt (Nat.lt_of_le_of_lt hxle hW))
            (modalSubfmls_trans_S5 hxform (modalUniverseS5_mem_formula hsfU))
      · dsimp only
        exact modalApplyOne_diamondPos_outputs_subset_S5 φ₀ b φ l hb hsf hW
    · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
      · simp
      · simp
      · simp
      · simp
      · simp
      · dsimp only
        exact modalApplyOne_boxNeg_outputs_subset_S5 φ₀ b φ l hb hsf hW
      · dsimp only
        by_cases hemp : ((acc.successorsOf l).filterMap (fun w' =>
            if b.any (· == (⟨.neg, φ, w'⟩ :
                SignedFormula (Proposition Atom) WorldIndex))
            then none
            else some (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
          ).isEmpty = true
        · simp only [if_pos hemp]
        · simp only [if_neg hemp]
          intro x hx
          obtain ⟨hxform, hxsucc⟩ := modalApplyOne_diamondNeg_outputs_subset b acc φ l x hx
          have hedge : acc.hasEdge l x.label = true := mem_successorsOf_hasEdge_S5 hxsucc
          have hxlt := (hInv l x.label hedge).2
          have hxle : x.label ≤ modalMaxWorld b := Nat.lt_succ_iff.mp hxlt
          exact mem_modalUniverseS5_of' (Nat.le_of_lt (Nat.lt_of_le_of_lt hxle hW))
            (modalSubfmls_trans_S5 hxform (modalUniverseS5_mem_formula hsfU))

/-- The S5 analogue of K's `modalApplyOne_knownWorlds_step`, stated directly over
`modalApplyOneS5` rather than `modalApplyOne`: either `modalApplyOneS5` leaves `acc` unchanged
with every emitted formula's label a known world of `b` (covering both the ordinary
agreement shapes, via `modalApplyOneS5_eq_of_not_boxPos_diaNeg` + K's own step lemma, and the two
S5-relevant shapes, via `modalApplyOneS5_boxPos_diaNeg_eq`), or it mints exactly one edge with a
nonempty `.linear` result entirely labeled at `modalNextWorld b` (only possible at the two
K-minting shapes, disjoint from the two S5-relevant shapes, so `modalApplyOneS5` agrees with K
there too). This is the uniform per-call fact `worldsContiguous`'s (and `bClosure`/`eClosure`'s)
preservation needs. -/
lemma modalApplyOneS5_knownWorlds_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneS5 sf b acc).snd = acc ∧
      (match (modalApplyOneS5 sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneS5 sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneS5 sf b acc).fst with
        | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
        | .branching _ => False
        | .persistent _ => False
        | .notApplicable => False)) := by
  by_cases hbd : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · obtain ⟨hsndeq, hor⟩ := modalApplyOneS5_boxPos_diaNeg_eq sf b acc hsfmem hknown hbd
    refine Or.inl ⟨hsndeq, ?_⟩
    rcases hor with hnot | ⟨out, hpers, hlabel⟩
    · rw [hnot]; trivial
    · rw [hpers]; exact hlabel
  · have hnbox : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) := fun hc => hbd (Or.inl hc)
    have hndia : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) := fun hc => hbd (Or.inr hc)
    rw [modalApplyOneS5_eq_of_not_boxPos_diaNeg sf b acc ⟨hnbox, hndia⟩]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown
