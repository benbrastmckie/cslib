/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Buchi
public import Cslib.Computability.Automata.DA.BuchiChar
public import Cslib.Computability.Automata.DA.Choueka
public import Cslib.Computability.Automata.DA.Concat
public import Cslib.Computability.Automata.NA.BuchiEquiv
public import Cslib.Computability.Automata.NA.BuchiInter
public import Cslib.Computability.Automata.NA.Sum
public import Cslib.Computability.Languages.Congruences.BuchiCongruence
public import Cslib.Computability.Languages.ExampleEventuallyZero
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# ω-Regular languages

This file defines ω-regular languages and proves some properties of them.
-/

@[expose] public section

namespace Cslib.ωLanguage

open Set Sum Filter ωSequence Automata ωAcceptor
open scoped Computability LTS

variable {Symbol : Type*}

/-- An ω-language is ω-regular iff it is accepted by a
finite-state nondeterministic Buchi automaton. -/
def IsRegular (p : ωLanguage Symbol) :=
  ∃ (State : Type) (_ : Finite State) (na : NA.Buchi State Symbol), language na = p

/-- Helper lemma for `isRegular_iff` below. -/
private lemma isRegular_iff.helper.{v'} {Symbol : Type u} {p : ωLanguage Symbol}
    (h : ∃ (σ : Type v) (_ : Finite σ) (na : NA.Buchi σ Symbol), language na = p) :
    ∃ (σ' : Type v') (_ : Finite σ') (na : NA.Buchi σ' Symbol), language na = p := by
  have ⟨σ, _, na, h_na⟩ := h
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  use σ', Finite.of_equiv σ f, na.reindex f
  rwa [NA.Buchi.reindex_language_eq]

/-- The state space of the accepting finite-state nondeterministic Buchi automaton
can in fact be universe-polymorphic. -/
theorem isRegular_iff {p : ωLanguage Symbol} :
    p.IsRegular ↔ ∃ (σ : Type v) (_ : Finite σ) (na : NA.Buchi σ Symbol), language na = p :=
  ⟨isRegular_iff.helper, isRegular_iff.helper⟩

/-- The ω-language accepted by a finite-state deterministic Buchi automaton is ω-regular. -/
theorem IsRegular.of_da_buchi {State : Type} [Finite State] (da : DA.Buchi State Symbol) :
    (language da).IsRegular :=
  ⟨State, inferInstance, da.toNABuchi, DA.Buchi.toNABuchi_language_eq⟩

/-- There is an ω-regular language that is not accepted by any deterministic Buchi automaton,
where the automaton is not even required to be finite-state. -/
theorem IsRegular.not_da_buchi :
  ∃ (Symbol : Type) (p : ωLanguage Symbol), p.IsRegular ∧
    ¬ ∃ (State : Type) (da : DA.Buchi State Symbol), language da = p := by
  refine ⟨Fin 2, Example.eventuallyZero, ?_, ?_⟩
  · use Fin 2, inferInstance, Example.eventuallyZeroNa,
      Example.eventuallyZero_accepted_by_na_buchi
  · rintro ⟨State, ⟨da, acc⟩, _⟩
    have := Example.eventuallyZero_not_omegaLim
    grind [DA.buchi_eq_finAcc_omegaLim]

/-- The ω-limit of a regular language is ω-regular. -/
@[simp]
theorem IsRegular.regular_omegaLim {l : Language Symbol}
    (h : l.IsRegular) : (l↗ω).IsRegular := by
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := Language.IsRegular.iff_dfa.mp h
  grind [IsRegular.of_da_buchi, =_ DA.buchi_eq_finAcc_omegaLim]

/-- The ω-limit of a regular language is recognized by a finite-state deterministic Muller
automaton (the base case of McNaughton's compositional determinization). -/
theorem IsRegular.omegaLim_da_muller {l : Language Symbol} (h : l.IsRegular) :
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol),
      language da = l↗ω := by
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := Language.IsRegular.iff_dfa.mp h
  exact ⟨State, inferInstance, (DA.Buchi.mk da acc).toMuller,
    by grind [DA.Buchi.toMuller_language_eq, DA.buchi_eq_finAcc_omegaLim]⟩

/-- The ω-power of a regular language is recognized by a finite-state deterministic Muller
automaton, via the Choueka route (task 241, McNaughton's theorem, Phase 3): decompose `l∗` as
a DFA language, take its Choueka language `U` (regular, via `DA.chouekaLang_regular`), obtain a
DMA for `U↗ω` (the base case, `omegaLim_da_muller` above), and combine the two via the Choueka
identity `DA.chouekaLang_omega_power_eq_omega_limit` and the concat-automaton correctness
`DA.concat_language_eq` (Phase 2). -/
theorem IsRegular.omegaPow_da_muller [Inhabited Symbol] {l : Language Symbol}
    (h : l.IsRegular) :
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol),
      language da = l^ω := by
  obtain ⟨State1, hfin1, dfa, hdfa⟩ := Language.IsRegular.iff_dfa.mp (Language.IsRegular.kstar h)
  haveI := hfin1
  have hU_reg : (DA.chouekaLang dfa.toDA dfa.accept).IsRegular :=
    DA.chouekaLang_regular dfa.toDA dfa.accept
  obtain ⟨State2, hfin2, da2, hda2⟩ := IsRegular.omegaLim_da_muller hU_reg
  haveI := hfin2
  refine ⟨State1 × (Fin (Nat.card State2 + 2) → Option State2), inferInstance,
    DA.Muller.mk (DA.concat dfa.toDA dfa.accept da2.toDA)
      (DA.mullerAccConcat dfa.toDA dfa.accept da2.toDA da2.accept), ?_⟩
  rw [DA.concat_language_eq]
  rw [show DA.FinAcc.mk dfa.toDA dfa.accept = dfa from rfl, hdfa,
    show DA.Muller.mk da2.toDA da2.accept = da2 from rfl, hda2]
  exact (DA.chouekaLang_omega_power_eq_omega_limit dfa.toDA dfa.accept hdfa).symm

open ωLanguage in
/-- The empty language is ω-regular. -/
@[simp]
theorem IsRegular.bot : (⊥ : ωLanguage Symbol).IsRegular := by
  let na : NA.Buchi Unit Symbol := {
    Tr _ _ _ := False
    start := ∅
    accept := ∅ }
  use Unit, inferInstance, na
  apply mem_ext
  intro xs
  simp [na, Accepts]

/-- The language of all ω-sequences is ω-regular. -/
@[simp]
theorem IsRegular.top : (⊤ : ωLanguage Symbol).IsRegular := by
  let na : NA.Buchi Unit Symbol := {
    Tr _ _ _ := True
    start := univ
    accept := univ }
  use Unit, inferInstance, na
  apply mem_ext
  intro xs
  simp +instances only [na, NA.Buchi.instωAcceptor, mem_language, mem_univ,
    frequently_true_iff_neBot, atTop_neBot, and_true, mem_top, iff_true]
  use const ()
  grind [NA.Run]

open NA.Buchi in
/-- The union of two ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.sup {p1 p2 : ωLanguage Symbol}
    (h1 : p1.IsRegular) (h2 : p2.IsRegular) : (p1 ⊔ p2).IsRegular := by
  obtain ⟨State1, h_fin1, ⟨na1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨na2, acc2⟩, rfl⟩ := h2
  let State : Fin 2 → Type
    | 0 => State1 | 1 => State2
  let na : (i : Fin 2) → NA (State i) Symbol
    | 0 => na1 | 1 => na2
  let acc : (i : Fin 2) → Set (State i)
    | 0 => acc1 | 1 => acc2
  have : ∀ i, Finite (State i) := by grind
  use (Σ i : Fin 2, State i), inferInstance, ⟨(NA.iSum na), (⋃ i, Sigma.mk i '' (acc i))⟩
  apply mem_ext
  intro xs
  simp only [iSum_language_eq, mem_sup, mem_language]
  rw [mem_iSup, Fin.exists_fin_two]
  rfl

open NA.Buchi in
/-- The intersection of two ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.inf {p1 p2 : ωLanguage Symbol}
    (h1 : p1.IsRegular) (h2 : p2.IsRegular) : (p1 ⊓ p2).IsRegular := by
  obtain ⟨State1, h_fin1, ⟨na1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨na2, acc2⟩, rfl⟩ := h2
  let State : Bool → Type
    | false => State1 | true => State2
  let na : (i : Bool) → NA (State i) Symbol
    | false => na1 | true => na2
  let acc : (i : Bool) → Set (State i)
    | false => acc1 | true => acc2
  have : ∀ i, Finite (State i) := by grind
  use (Π i : Bool, State i) × Bool, inferInstance, ⟨(interNA na acc), interAccept acc⟩
  apply mem_ext
  intro xs
  simp only [inter_language_eq, mem_inf, mem_language]
  rw [mem_iInf, Bool.forall_bool]
  rfl

/-- The union of any finite number of ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.iSup {I : Type*} [Finite I] {s : Set I} {p : I → ωLanguage Symbol}
    (h : ∀ i ∈ s, (p i).IsRegular) : (⨆ i ∈ s, p i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    have := ncard_eq_zero (s := s)
    grind [IsRegular.bot, iSup_bot]
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ).mp h_n
    rw [iSup_insert]
    grind [IsRegular.sup]

/-- The intersection of any finite number of ω-regular languages is ω-regular. -/
@[simp]
theorem IsRegular.iInf {I : Type*} [Finite I] {s : Set I} {p : I → ωLanguage Symbol}
    (h : ∀ i ∈ s, (p i).IsRegular) : (⨅ i ∈ s, p i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    have := ncard_eq_zero (s := s)
    grind [IsRegular.top, iInf_top]
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ).mp h_n
    rw [iInf_insert]
    grind [IsRegular.inf]

/-- The concatenation of a regular language and an ω-regular language is ω-regular. -/
@[simp]
theorem IsRegular.hmul {l : Language Symbol} {p : ωLanguage Symbol}
    (h1 : l.IsRegular) (h2 : p.IsRegular) : (l * p).IsRegular := by
  obtain ⟨State1, h_fin1, ⟨na1, acc1⟩, rfl⟩ := Language.IsRegular.iff_nfa.mp h1
  obtain ⟨State2, h_fin1, ⟨na2, acc2⟩, rfl⟩ := h2
  use State1 ⊕ State2, inferInstance, ⟨NA.concat ⟨na1, acc1⟩ na2, inr '' acc2⟩
  exact NA.Buchi.concat_language_eq

/-- The ω-power of a regular language is an ω-regular language. -/
@[simp]
theorem IsRegular.omegaPow [Inhabited Symbol] {l : Language Symbol}
    (h : l.IsRegular) : (l^ω).IsRegular := by
  obtain ⟨State, h_fin, na, rfl⟩ := Language.IsRegular.iff_nfa.mp h
  use Unit ⊕ State, inferInstance, ⟨na.loop, {inl ()}⟩
  exact NA.Buchi.loop_language_eq

/-- An ω-language is regular iff it is the finite union of ω-languages of the form `L * M^ω`,
where all `L`s and `M`s are regular languages. -/
theorem IsRegular.eq_fin_iSup_hmul_omegaPow [Inhabited Symbol] (p : ωLanguage Symbol) :
    p.IsRegular ↔ ∃ n : ℕ, ∃ l m : Fin n → Language Symbol,
      (∀ i, (l i).IsRegular ∧ (m i).IsRegular) ∧ p = ⨆ i, (l i) * (m i)^ω := by
  constructor
  · rintro ⟨State, _, na, rfl⟩
    rw [NA.Buchi.language_eq_fin_iSup_hmul_omegaPow na]
    have eq_start := Finite.equivFin ↑na.start
    have eq_accept := Finite.equivFin ↑na.accept
    have eq_prod := eq_start.prodCongr eq_accept
    have eq := (eq_prod.trans finProdFinEquiv).symm
    refine ⟨Nat.card ↑na.start * Nat.card ↑na.accept,
      fun i ↦ na.pairLang (eq i).1 (eq i).2,
      fun i ↦ na.pairLang (eq i).2 (eq i).2,
      by grind [LTS.pairLang_regular], ?_⟩
    apply mem_ext
    intro xs
    simp only [mem_iSup]
    refine ⟨?_, by grind⟩
    rintro ⟨s, h_s, t, h_t, h_mem⟩
    use eq.symm (⟨s, h_s⟩, ⟨t, h_t⟩)
    simp only [Equiv.apply_symm_apply]
    exact h_mem
  · rintro ⟨n, l, m, _, rfl⟩
    rw [← iSup_univ]
    apply IsRegular.iSup
    grind [IsRegular.hmul, IsRegular.omegaPow]

/-- If an ω-language has a finite saturating cover made of ω-regular languages,
then it is an ω-regular language. -/
theorem IsRegular.fin_cover_saturates {I : Type*} [Finite I]
    {p : I → ωLanguage Symbol} {q : ωLanguage Symbol}
    (hs : Saturates (fun i ↦ (p i).toSet) q.toSet)
    (hc : ⨆ i, p i = ⊤) (hr : ∀ i, (p i).IsRegular) : q.IsRegular := by
  suffices hu : q = ⨆ i ∈ {i | ((p i) ⊓ q).toSet.Nonempty}, (p i) by
    rw [hu]
    apply IsRegular.iSup
    grind
  have hc' : ⋃ i, (p i).toSet = univ := by grind [iSup_def, top_def]
  have hq := saturates_eq_biUnion hs hc'
  ext : 1
  rw [hq]
  simp [iSup_def, inf_def]

/-- If an ω-language has a finite saturating cover made of ω-regular languages,
then its complement is an ω-regular language. -/
theorem IsRegular.fin_cover_saturates_compl {I : Type*} [Finite I]
    {p : I → ωLanguage Symbol} {q : ωLanguage Symbol}
    (hs : Saturates (fun i ↦ (p i).toSet) q.toSet)
    (hc : ⨆ i, p i = ⊤) (hr : ∀ i, (p i).IsRegular) : (qᶜ).IsRegular :=
  IsRegular.fin_cover_saturates (saturates_compl hs) hc hr

open NA.Buchi in
/-- The complementation of an ω-regular language is ω-regular. -/
@[simp]
theorem IsRegular.compl {Symbol : Type} [Inhabited Symbol] {p : ωLanguage Symbol}
    (h : p.IsRegular) : (pᶜ).IsRegular := by
  obtain ⟨State, h_fin, na, rfl⟩ := h
  have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  have h_sat := buchiFamily_saturation (na := na)
  have h_cov := buchiFamily_cover (na := na)
  apply IsRegular.fin_cover_saturates_compl h_sat h_cov
  have := Language.IsRegular.congr_fin_index (c := na.BuchiCongruence)
  grind [buchiFamily, IsRegular.hmul, IsRegular.omegaPow]

/-- The ω-language recognized by a finite-state deterministic Muller automaton is ω-regular.

**Proof**: For each state `q`, the DBA built from the DMA's transition system with accept
set `{q}` recognizes exactly `{xs | q ∈ infOcc(da.run xs)}`. For each finite set
`F ⊆ State`, the language `{xs | infOcc(da.run xs) = F}` is a finite intersection of
such DBA languages and their complements (ω-regularity closed under complement by
`IsRegular.compl`). Since `[Finite State]` implies there are only finitely many subsets
`F`, and `da.accept` indexes exactly those F that are accepting, the DMA language is a
finite union of ω-regular languages and hence ω-regular. -/
theorem IsRegular.of_da_muller {State : Type} [Finite State]
    {Symbol : Type} [Inhabited Symbol]
    (da : DA.Muller State Symbol) : (language da).IsRegular := by
  -- Use classical decidability for Finset constructions
  haveI hde : DecidableEq State := Classical.decEq State
  haveI h_ft : Fintype State := Fintype.ofFinite State
  haveI h1 : Fintype (Finset State) := Finset.fintype
  -- For each state q, define the DBA that accepts iff q appears infinitely often
  let ba : State → DA.Buchi State Symbol := fun q => DA.Buchi.mk da.toDA {q}
  -- The DBA language: q ∈ infOcc iff q appears infinitely often
  have ba_lang : ∀ q (xs : ωSequence Symbol),
      xs ∈ language (ba q) ↔ q ∈ (da.run xs).infOcc := by
    intro q xs
    simp [ba, mem_language, Accepts, ωSequence.mem_infOcc]
  -- Each DBA language is ω-regular
  have ba_reg : ∀ q, (language (ba q)).IsRegular := fun q => IsRegular.of_da_buchi (ba q)
  -- Complement of each DBA language is ω-regular
  have ba_compl_reg : ∀ q, ((language (ba q))ᶜ).IsRegular :=
    fun q => IsRegular.compl (ba_reg q)
  -- For conciseness, name the per-F language
  let langF (F : Finset State) : ωLanguage Symbol :=
    {xs : ωSequence Symbol | (da.run xs).infOcc = (F : Set State)}
  have langF_reg : ∀ F : Finset State, (langF F).IsRegular := by
    intro F
    -- langF F = (⋂ q ∈ F, lang(ba q)) ∩ (⋂ q ∉ F, (lang(ba q))ᶜ)
    suffices h : langF F =
        (⨅ q ∈ F, language (ba q)) ⊓ ⨅ q ∈ Finset.univ \ F, (language (ba q))ᶜ by
      rw [h]
      apply IsRegular.inf
      · apply IsRegular.iInf; intro q _; exact ba_reg q
      · apply IsRegular.iInf; intro q _; exact ba_compl_reg q
    apply mem_ext
    intro xs
    simp only [mem_iInf, mem_inf, mem_compl, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro h_eq
      -- h_eq : xs ∈ {xs | (da.run xs).infOcc = ↑F}, i.e., (da.run xs).infOcc = ↑F
      have h_eq' : (da.run xs).infOcc = (F : Set State) := h_eq
      exact ⟨fun q hq => (ba_lang q xs).mpr (h_eq' ▸ Finset.mem_coe.mpr hq),
             fun q hqF hq => hqF (Finset.mem_coe.mp (h_eq' ▸ (ba_lang q xs).mp hq))⟩
    · intro ⟨h_in, h_out⟩
      -- Goal: xs ∈ langF F, i.e., (da.run xs).infOcc = ↑F
      change (da.run xs).infOcc = (F : Set State)
      ext q
      simp only [Finset.mem_coe]
      constructor
      · intro hq
        by_contra hqF
        exact h_out q hqF ((ba_lang q xs).mpr hq)
      · intro hq
        exact (ba_lang q xs).mp (h_in q hq)
  -- The DMA language equals the union over accepting finsets
  have lang_decomp : language da =
      ⨆ F ∈ {F : Finset State | (F : Set State) ∈ da.accept}, langF F := by
    apply mem_ext
    intro xs
    simp only [mem_language, Accepts, mem_iSup, Set.mem_setOf_eq]
    constructor
    · intro h_acc
      -- infOcc is finite (since State is finite)
      have h_fin_infOcc : (da.run xs).infOcc.Finite := ωSequence.infOcc_finite _
      -- Convert to Finset; its coercion back equals infOcc
      refine ⟨h_fin_infOcc.toFinset, ?_, ?_⟩
      · -- prove ↑h_fin_infOcc.toFinset ∈ da.accept
        rw [h_fin_infOcc.coe_toFinset]; exact h_acc
      · -- prove xs ∈ langF h_fin_infOcc.toFinset
        change (da.run xs).infOcc = ↑h_fin_infOcc.toFinset
        rw [h_fin_infOcc.coe_toFinset]
    · rintro ⟨F, h_F_acc, h_eq⟩
      have h_eq' : (da.run xs).infOcc = (F : Set State) := h_eq
      rw [h_eq']
      exact h_F_acc
  -- The DMA language is ω-regular as a finite union of ω-regular languages
  rw [lang_decomp]
  apply IsRegular.iSup
  intro F _
  exact langF_reg F

open NA.Buchi in
/-- Each element of the Büchi family of a finite-state NBA is an ω-regular language.

The family element `na.buchiFamily (a, b)` equals `eqvCls a * (eqvCls b)^ω`. Both
`eqvCls a` and `eqvCls b` are regular languages by `Language.IsRegular.congr_fin_index`
(which applies since `[Finite State]` yields `Finite (Quotient na.BuchiCongruence.eq)`
via `buchiCongruence_fin_index`). Regularity of the product follows from `IsRegular.hmul`
and `IsRegular.omegaPow`. -/
private lemma buchiFamily_component_isRegular {Symbol : Type} [Inhabited Symbol]
    {State : Type} [Finite State]
    {na : NA.Buchi State Symbol}
    (i : Quotient na.BuchiCongruence.eq × Quotient na.BuchiCongruence.eq) :
    (na.buchiFamily i).IsRegular := by
  haveI : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  have := Language.IsRegular.congr_fin_index (c := na.BuchiCongruence)
  grind [buchiFamily, IsRegular.hmul, IsRegular.omegaPow]

open NA.Buchi in
/-- Concrete deterministic Muller automaton (DMA) over the Büchi congruence quotient of `na`.

**Components** (Phase 3, task 241):
- **State space**: `Q = Quotient na.BuchiCongruence.eq`, finite by `buchiCongruence_fin_index`.
- **Initial state**: `Quotient.mk na.BuchiCongruence.eq []`, the class of the empty word.
- **Transition**: `δ(q, a) = ⟦u ++ [a]⟧` for the representative `u` of class `q`, well-defined
  by `BuchiCongruence.right_cov` (right-appending a single symbol preserves Büchi congruence).
- **Accept set**: `{S : Set Q | ∃ a ∈ S, ∃ b : Q, (buchiFamily (a, b) ∩ language na).Nonempty}`.
  A Muller set `S` is accepting iff it contains a recurrent prefix class `a` (the first,
  prefix index of `buchiFamily`, which is what the run's `infOcc` actually contains) such that
  some Büchi family element `buchiFamily (a, b)` intersects `language na`; by
  `buchiFamily_saturation` this is equivalent to `buchiFamily (a, b) ⊆ language na`.

The language equality is stated as `buchiCongr_DMA_language_eq` below (BLOCKED, Phase 4). -/
private noncomputable def buchiCongr_DMA [Inhabited Symbol]
    {State : Type} (na : NA.Buchi State Symbol) :
    DA.Muller (Quotient na.BuchiCongruence.eq) Symbol where
  tr q a := Quotient.liftOn q
    (fun u => Quotient.mk na.BuchiCongruence.eq (u ++ [a]))
    (fun _ _ h => Quotient.sound (na.BuchiCongruence.right_cov.elim [a] h))
  start := Quotient.mk na.BuchiCongruence.eq []
  accept := {S : Set (Quotient na.BuchiCongruence.eq) |
    ∃ a ∈ S, ∃ b : Quotient na.BuchiCongruence.eq,
      ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty}

open NA.Buchi in
/-- The state of `buchiCongr_DMA na` after reading the first `n` symbols of `xs` equals
the Büchi congruence class of the length-`n` prefix `xs.extract 0 n`.

This is the key run-state lemma for proving `buchiCongr_DMA_language_eq`: it connects
the DMA run to the congruence classes of prefixes, enabling both directions of the
language equality proof. -/
private lemma buchiCongr_DMA_run_eq [Inhabited Symbol] {State : Type}
    (na : NA.Buchi State Symbol) (xs : ωSequence Symbol) (n : ℕ) :
    (buchiCongr_DMA na).run xs n =
      Quotient.mk na.BuchiCongruence.eq (xs.extract 0 n) := by
  induction n with
  | zero =>
    simp only [DA.run_zero, buchiCongr_DMA, extract_eq_nil]
  | succ n ih =>
    rw [DA.run_succ, ih]
    simp only [buchiCongr_DMA, Quotient.liftOn_mk]
    congr 1
    exact (extract_succ_right (Nat.zero_le n)).symm

open NA.Buchi in
/-- Recurrent-class lemma for the Büchi-congruence DMA run: for `[Finite State]` and any
`xs`, there exist congruence classes `a b` with `b` idempotent (`b * b = b`), `a` absorbing
(`a * b = a`), and `a` occurring infinitely often in `(buchiCongr_DMA na).run xs`.

Bridges from `buchiCongruence_recurrentPrefixClass` (the pure prefix-class core lemma) via
`buchiCongr_DMA_run_eq`. Used by Phase 4 of the McNaughton theorem (task 241) to close the
forward direction of `buchiCongr_DMA_language_eq`. -/
private lemma buchiCongr_recurrentClass [Inhabited Symbol] {State : Type} [Finite State]
    (na : NA.Buchi State Symbol) (xs : ωSequence Symbol) :
    ∃ a b : Quotient na.BuchiCongruence.eq, b * b = b ∧ a * b = a ∧
      a ∈ ((buchiCongr_DMA na).run xs).infOcc := by
  obtain ⟨a, b, hbb, hab, hfreq⟩ := buchiCongruence_recurrentPrefixClass na xs
  exact ⟨a, b, hbb, hab, mem_infOcc.mpr
    (hfreq.mono fun k hk => (buchiCongr_DMA_run_eq na xs k).trans hk)⟩

open Finset NA.Buchi in
/-- For any `xs ∈ language na`, the infimum-occurrence set of the Büchi-congruence DMA run
contains a state that, paired with some partner state, gives a Büchi family element
intersecting `language na`. This is the Ramsey/recurrence core of the forward inclusion of
McNaughton's theorem, establishing `infOcc(run xs) ∈ (buchiCongr_DMA na).accept`.

The proof re-runs the Ramsey argument of `buchiCongruence_recurrentPrefixClass`/
`buchiFamily_cover` locally: a single application of `infinite_graph_ramsey` to the prefix
coloring of `xs` yields both the recurring absorbing class `a` (via the exposed pairwise
homogeneity `hcol`, not just the single-point recurrence exposed by `buchiCongr_recurrentClass`)
*and* a concrete decomposition of `xs` itself into `na.buchiFamily (a, b)`, so the recurring
class and the family witness come from the same Ramsey witness and are guaranteed consistent. -/
private lemma buchiCongr_DMA_accept_mem [Inhabited Symbol] {State : Type} [Finite State]
    (na : NA.Buchi State Symbol) (xs : ωSequence Symbol) (hxs : xs ∈ language na) :
    ∃ a ∈ ((buchiCongr_DMA na).run xs).infOcc,
      ∃ b, ((na.buchiFamily (a, b) ⊓ language na).toSet).Nonempty := by
  have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  let color (t : Finset ℕ) : Quotient na.BuchiCongruence.eq :=
    if h : t.Nonempty then ⟦ xs.extract (t.min' h) (t.max' h) ⟧ else ⟦ [] ⟧
  obtain ⟨b, ns, h_ns, h_color⟩ := infinite_graph_ramsey color
  obtain ⟨f, h_mono, rfl⟩ := strictMono_of_infinite h_ns
  -- Pairwise homogeneity: any two indices in the homogeneous set color the same as `b`.
  have hcol : ∀ i j : ℕ, i < j →
      (⟦xs.extract (f i) (f j)⟧ : Quotient na.BuchiCongruence.eq) = b := by
    intro i j hij
    have hfij : f i < f j := h_mono hij
    have h_le : f i ≤ f j := le_of_lt hfij
    have h_ne : f i ≠ f j := Nat.ne_of_lt hfij
    have h_ne' : ({f i, f j} : Finset ℕ).Nonempty := insert_nonempty _ _
    have h_card : ({f i, f j} : Finset ℕ).card = 2 := card_pair h_ne
    have h_sub : ↑({f i, f j} : Finset ℕ) ⊆ Set.range f := by
      rw [coe_pair]; rintro x (rfl | rfl) <;> exact ⟨_, rfl⟩
    have hbc := h_color _ h_card h_sub
    have heval : color {f i, f j} = ⟦xs.extract (f i) (f j)⟧ := by
      change (if h : ({f i, f j} : Finset ℕ).Nonempty then
        ⟦xs.extract (({f i, f j} : Finset ℕ).min' h) (({f i, f j} : Finset ℕ).max' h)⟧
        else ⟦[]⟧) = ⟦xs.extract (f i) (f j)⟧
      rw [dif_pos h_ne', min'_pair, max'_pair, min_eq_left h_le, max_eq_right h_le]
    rw [heval] at hbc
    exact hbc
  -- `b` is idempotent (the same 3-point argument as `buchiCongruence_recurrentPrefixClass`).
  have hbb : b * b = b := calc
    b * b
        = ⟦xs.extract (f 0) (f 1)⟧ * ⟦xs.extract (f 1) (f 2)⟧ := by
            rw [hcol 0 1 (by omega), hcol 1 2 (by omega)]
      _ = ⟦xs.extract (f 0) (f 1) ++ xs.extract (f 1) (f 2)⟧ :=
            (buchiCongruence_mk_append _ _).symm
      _ = ⟦xs.extract (f 0) (f 2)⟧ := by
            rw [append_extract_extract (le_of_lt (h_mono (by omega : 0 < 1)))
                                       (le_of_lt (h_mono (by omega : 1 < 2)))]
      _ = b := hcol 0 2 (by omega)
  -- `a` is the prefix class right after the first loop iteration: it recurs at every later
  -- breakpoint, and (unlike `b`) is literally attained by `(buchiCongr_DMA na).run xs`.
  set a := (⟦xs.extract 0 (f 1)⟧ : Quotient na.BuchiCongruence.eq) with ha_def
  have ha0b : a = ⟦xs.extract 0 (f 0)⟧ * b := by
    rw [ha_def, show xs.extract 0 (f 1) = xs.extract 0 (f 0) ++ xs.extract (f 0) (f 1)
          from (append_extract_extract (Nat.zero_le _)
            (le_of_lt (h_mono (by omega : 0 < 1)))).symm,
        buchiCongruence_mk_append, hcol 0 1 (by omega)]
  have hab : a * b = a := by rw [ha0b, mul_assoc, hbb]
  -- `a` recurs as a prefix class infinitely often.
  have hfreq : ∃ᶠ k in atTop, (⟦xs.extract 0 k⟧ : Quotient na.BuchiCongruence.eq) = a := by
    rw [frequently_iff_strictMono]
    refine ⟨fun m => f (m + 1), fun i j h => h_mono (Nat.succ_lt_succ h), fun m => ?_⟩
    rw [show xs.extract 0 (f (m + 1)) = xs.extract 0 (f 0) ++ xs.extract (f 0) (f (m + 1))
          from (append_extract_extract (Nat.zero_le _)
            (h_mono.monotone (Nat.zero_le _))).symm,
        buchiCongruence_mk_append, hcol 0 (m + 1) (Nat.zero_lt_succ m), ← ha0b]
  -- Transport `hfreq` to `infOcc` of the DMA run via `buchiCongr_DMA_run_eq`.
  have ha_infOcc : a ∈ ((buchiCongr_DMA na).run xs).infOcc :=
    mem_infOcc.mpr (hfreq.mono fun k hk => (buchiCongr_DMA_run_eq na xs k).trans hk)
  -- `xs` itself decomposes into `na.buchiFamily (a, b)`: prefix up to the second breakpoint
  -- has class `a`, and every later segment (between consecutive breakpoints) has class `b`.
  have hg_mono : StrictMono (fun k => f (k + 1)) := fun i j h => h_mono (Nat.succ_lt_succ h)
  have hmem : xs ∈ na.buchiFamily (a, b) := by
    apply mem_buchiFamily.mpr
    refine ⟨xs.take (f 1), (xs.drop (f 1)).toSegs (fun k => f (k + 1) - f 1), ?_, ?_, ?_⟩
    · show xs.take (f 1) ∈ na.BuchiCongruence.eqvCls a
      simp only [RightCongruence.eqvCls, ha_def, extract_eq_take]
      exact Set.mem_preimage.mpr rfl
    · intro k
      have h_le : f 1 ≤ f (k + 1) := hg_mono.monotone (Nat.zero_le _)
      have h_le' : f 1 ≤ f (k + 2) := hg_mono.monotone (by omega)
      have h_eq1 : f 1 + (f (k + 1) - f 1) = f (k + 1) := by omega
      have h_eq2 : f 1 + (f (k + 2) - f 1) = f (k + 2) := by omega
      simp only [Language.mem_sub_one, toSegs_def, extract_drop, h_eq1, h_eq2]
      refine ⟨?_, ?_⟩
      · show (⟦xs.extract (f (k + 1)) (f (k + 2))⟧ : Quotient na.BuchiCongruence.eq) = b
        exact hcol (k + 1) (k + 2) (by omega)
      · simp only [ne_eq, extract_eq_nil_iff, not_le]
        exact h_mono (by omega)
    · grind [Nat.base_zero_strictMono hg_mono]
  exact ⟨a, ha_infOcc, b, xs, hmem, hxs⟩

open NA.Buchi in
private lemma buchiCongr_DMA_language_forward [Inhabited Symbol] {State : Type} [Finite State]
    (na : NA.Buchi State Symbol) :
    language na ⊆ language (buchiCongr_DMA na) := by
  intro xs hxs
  change ((buchiCongr_DMA na).run xs).infOcc ∈ (buchiCongr_DMA na).accept
  -- The accept condition is exactly the Ramsey/recurrence statement: the run's `infOcc`
  -- contains a recurrent prefix class `a` (first `buchiFamily` index) paired with some `b`
  -- such that `buchiFamily (a, b)` meets `language na`.
  simp only [buchiCongr_DMA, Set.mem_setOf_eq]
  exact buchiCongr_DMA_accept_mem na xs hxs

open NA.Buchi in
/-- Forward direction scaffold for McNaughton's theorem: ω-regular → DMA-recognizable.

Reduces the forward direction of `IsRegular.iff_da_muller` to `h_pkg`: given any
finite-state NBA `na`, there exists a finite-state DMA over the Büchi congruence quotient
`Q = Quotient na.BuchiCongruence.eq` whose language equals `language na`.

**BLOCKED (Phase 3)**: Prove `h_pkg` by constructing the explicit `DA.Muller` record with:
- State space: `Q = Quotient na.BuchiCongruence.eq` (finite by `buchiCongruence_fin_index`)
- Initial state: `⟦[]⟧` (class of the empty word)
- Transition: `δ([u], a) = [u ++ [a]]` (right multiplication in the congruence quotient)
- Accept set: `{S : Set Q | ∃ b : Q, b ∈ S ∧ (⟦[]⟧, b) ∈ good_pairs na}` where
  `good_pairs na = {(a, b) | (na.buchiFamily (a, b) ∩ language na).Nonempty}`
  (equivalently, by `buchiFamily_saturation`, pairs whose family is ⊆ `language na`).

The language equality `language dm = language na` uses:
- `buchiFamily_saturation`: the Büchi family saturates `language na`
- `buchiFamily_cover`: the Büchi family covers all ω-sequences
- `buchiFamily_component_isRegular`: each component is ω-regular -/
private lemma IsRegular.to_da_muller_scaffold {Symbol : Type} [Inhabited Symbol]
    {p : ωLanguage Symbol}
    (h : p.IsRegular)
    (h_pkg : ∀ {State : Type} [Finite State] (na : NA.Buchi State Symbol),
        ∃ (dm : DA.Muller (Quotient na.BuchiCongruence.eq) Symbol),
          language dm = language na) :
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p := by
  obtain ⟨State, h_fin, na, rfl⟩ := h
  -- The Büchi congruence quotient Q is finite
  haveI h_qfin : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  -- The Büchi family saturates and covers language na (established here for Phase 3 reference)
  have _h_sat := buchiFamily_saturation (na := na)
  have _h_cov := buchiFamily_cover (na := na)
  -- Each Büchi family component is ω-regular (Phase 3 uses this in the language equality proof)
  have _h_comp : ∀ i, (na.buchiFamily i).IsRegular := buchiFamily_component_isRegular
  -- Phase 3 obligation: obtain the DMA over Q with language na
  obtain ⟨dm, h_dm⟩ := h_pkg na
  exact ⟨Quotient na.BuchiCongruence.eq, h_qfin, dm, h_dm⟩

/-- McNaughton's Theorem: an ω-language is ω-regular (recognized by a finite-state NBA)
if and only if it is recognized by a finite-state deterministic Muller automaton.

**Proof**: The backward direction `(⇐)` follows from `IsRegular.of_da_muller`.

The forward direction `(⇒)` follows the **Choueka decomposition route** (ported from
`ctchou/AutomataTheory`'s `DetMullerLang.lean`, which does *not* use a quotient-as-DMA
construction): decompose `p = ⨆ i, (l i) * (m i)^ω` via `eq_fin_iSup_hmul_omegaPow`; show
each `(m i)^ω` is DMA-recognizable via the Choueka identity `M^ω = M* · U↗ω` (regular `U`)
combined with the ω-limit base case `omegaLim_da_muller`; concatenate with the regular
prefix `l i` via the `DA.concat` flag-construction correctness lemma
(`concat_language_eq`); and fold the finite family into one DMA via DMA finite-union
closure (`DA.Muller.union`). See `IsRegular.to_da_muller` (task 241, phase 5) for the
assembly. -/
proof_wanted IsRegular.iff_da_muller [Inhabited Symbol] {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p

-- Once McNaughton's theorem is proved (task 241), the following corollaries follow from the
-- conversion chain in `Cslib.Computability.Automata.DA.Conversions`:
--
--   `IsRegular.iff_da_rabin`: ω-regularity ↔ recognizable by a finite-state DRA.
--   Proof: `IsRegular.iff_da_muller` + `Muller.toRabin_exists` (exponential pairs, proof_wanted).
--
--   `IsRegular.iff_da_parity`: ω-regularity ↔ recognizable by a finite-state DPA.
--   Proof: `IsRegular.iff_da_rabin` + `Rabin.toParity_exists` (LAR construction, proof_wanted).

end Cslib.ωLanguage
