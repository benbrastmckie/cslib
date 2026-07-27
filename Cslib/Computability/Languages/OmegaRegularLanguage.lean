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
public import Cslib.Computability.Automata.DA.MullerClosure
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
automaton, via the Choueka route (McNaughton's theorem): decompose `l∗` as
a DFA language, take its Choueka language `U` (regular, via `DA.chouekaLang_regular`), obtain a
DMA for `U↗ω` (the base case, `omegaLim_da_muller` above), and combine the two via the Choueka
identity `DA.chouekaLang_omega_power_eq_omega_limit` and the concat-automaton correctness
`DA.concat_language_eq`. -/
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
    use eq.invFun (⟨s, h_s⟩, ⟨t, h_t⟩)
    have := Equiv.apply_symm_apply eq
    simp_all
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
    simp only [mem_language, Accepts, mem_iSup, Set.mem_ofPred_eq]
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

/-- Every ω-regular language is recognized by a finite-state deterministic Muller automaton
(the forward direction `(⇒)` of McNaughton's theorem, Choueka route).

**Proof**: decompose `p = ⨆ i, (l i) * (m i)^ω` via `eq_fin_iSup_hmul_omegaPow`; for each
component `i`, obtain a DFA for the regular prefix `l i` (`Language.IsRegular.iff_dfa`) and a
DMA for the ω-power `(m i)^ω` (`omegaPow_da_muller`); combine them into a single DMA
for `(l i) * (m i)^ω` via the concat-automaton correctness lemma (`DA.concat_language_eq`);
fold the finite family (indexed by `Fin n`) into one DMA via the finite-union lift
`DA.Muller.exists_iSup_univ`. -/
theorem IsRegular.to_da_muller [Inhabited Symbol] {p : ωLanguage Symbol}
    (hp : p.IsRegular) :
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p := by
  obtain ⟨n, l, m, hreg, rfl⟩ := (IsRegular.eq_fin_iSup_hmul_omegaPow p).mp hp
  apply DA.Muller.exists_iSup_univ
  intro i
  obtain ⟨hl, hm⟩ := hreg i
  obtain ⟨State1, hfin1, dfa1, hdfa1⟩ := Language.IsRegular.iff_dfa.mp hl
  haveI := hfin1
  obtain ⟨State2, hfin2, da2, hda2⟩ := IsRegular.omegaPow_da_muller hm
  haveI := hfin2
  refine ⟨State1 × (Fin (Nat.card State2 + 2) → Option State2), inferInstance,
    DA.Muller.mk (DA.concat dfa1.toDA dfa1.accept da2.toDA)
      (DA.mullerAccConcat dfa1.toDA dfa1.accept da2.toDA da2.accept), ?_⟩
  rw [DA.concat_language_eq]
  rw [show DA.FinAcc.mk dfa1.toDA dfa1.accept = dfa1 from rfl, hdfa1,
    show DA.Muller.mk da2.toDA da2.accept = da2 from rfl, hda2]

/-- **McNaughton's Theorem**: an ω-language is ω-regular (recognized by a
finite-state nondeterministic Büchi automaton) if and only if it is recognized by a
finite-state deterministic Muller automaton.

**Proof**: The backward direction `(⇐)` follows from `IsRegular.of_da_muller`. The forward
direction `(⇒)` follows the **Choueka decomposition route** (ported from
`ctchou/AutomataTheory`'s `DetMullerLang.lean`, which does *not* use a quotient-as-DMA
construction): `IsRegular.to_da_muller` decomposes `p = ⨆ i, (l i) * (m i)^ω` via
`eq_fin_iSup_hmul_omegaPow`; shows each `(m i)^ω` is DMA-recognizable via the Choueka identity
`M^ω = M* · U↗ω` (regular `U`, `omegaPow_da_muller`) combined with the ω-limit base case
(`omegaLim_da_muller`); concatenates with the regular prefix `l i` via the `DA.concat`
flag-construction correctness lemma (`concat_language_eq`); and folds the finite family into
one DMA via the DMA finite-union closure lift (`DA.Muller.exists_iSup_univ`). -/
theorem IsRegular.iff_da_muller {Symbol : Type} [Inhabited Symbol] {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p :=
  ⟨fun hp => IsRegular.to_da_muller hp, fun ⟨_, _, da, h⟩ => h ▸ IsRegular.of_da_muller da⟩

-- Now that McNaughton's theorem is proved, the following corollaries follow from the
-- conversion chain in `Cslib.Computability.Automata.DA.Conversions`:
--
--   `IsRegular.iff_da_rabin`: ω-regularity ↔ recognizable by a finite-state DRA.
--   Proof: `IsRegular.iff_da_muller` + `Muller.toRabin_exists` (exponential pairs, proof_wanted).
--
--   `IsRegular.iff_da_parity`: ω-regularity ↔ recognizable by a finite-state DPA.
--   Proof: `IsRegular.iff_da_rabin` + `Rabin.toParity_exists` (LAR construction, proof_wanted).

end Cslib.ωLanguage
