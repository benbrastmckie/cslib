/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.Pair
public import Cslib.Foundations.Combinatorics.InfiniteGraphRamsey
public import Cslib.Foundations.Data.Set.Saturation

/-!
# Buchi Congruence

A special type of right congruences used by J.R. Büchi to prove the closure
of ω-regular languages under complementation.
-/

@[expose] public section

namespace Cslib.Automata.NA.Buchi

open Function Set Filter ωAcceptor ωLanguage ωSequence

variable {Symbol : Type*} {State : Type}

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Given a Buchi automaton `na`, two finite words `u` and `v` are Buchi-congruent
according to `na` iff for every pair of states `s` and `t` of `na`, both of the
following two conditions hold:
(1) `u` can move `na` from `s` to `t` iff `v` can move `na` from `s` to `t`;
(2) `u` can move `na` from `s` to `t` via an acceptingg states iff `v` can move `na`
from `s` to `t` via an acceptingg states. -/
@[implicit_reducible]
def BuchiCongruence (na : Buchi State Symbol) : RightCongruence Symbol where
  eq.r u v :=
    ∀ s t, (u ∈ na.pairLang s t ↔ v ∈ na.pairLang s t) ∧
      (u ∈ na.pairViaLang na.accept s t ↔ v ∈ na.pairViaLang na.accept s t)
  eq.iseqv.refl := by grind
  eq.iseqv.symm := by grind
  eq.iseqv.trans := by grind
  right_cov.elim := by
    grind only [Covariant, → LTS.pairLang_split, <= LTS.pairLang_append, → LTS.pairViaLang_split,
      <= LTS.pairViaLang_append_pairLang, <= LTS.pairLang_append_pairViaLang]

open scoped Classical in
/-- `BuchiCongrParam` is a parameterization of the equivalence classes of `na.BuchiCongruence`
using the type `State → State → Prop × Prop`, which is finite if `State` is. -/
noncomputable def BuchiCongrParam (na : Buchi State Symbol)
    (f : State → State → Prop × Prop) : Quotient na.BuchiCongruence.eq :=
  if h : ∃ u, ∀ s t, ((f s t).1 ↔ u ∈ na.pairLang s t) ∧
      ((f s t).2 ↔ u ∈ na.pairViaLang na.accept s t)
  then ⟦ Classical.choose h ⟧
  else ⟦ [] ⟧

variable {na : Buchi State Symbol}

/-- `BuchiCongrParam` is surjective. -/
lemma buchiCongrParam_surjective : Surjective na.BuchiCongrParam := by
  intro q
  let f s t := (q.out ∈ na.pairLang s t, q.out ∈ na.pairViaLang na.accept s t)
  have h : ∃ u, ∀ s t, ((f s t).1 ↔ u ∈ na.pairLang s t) ∧
        ((f s t).2 ↔ u ∈ na.pairViaLang na.accept s t) := by
    use q.out
    grind
  use f
  simp only [BuchiCongrParam, h, ↓reduceDIte]
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  intro s t
  grind

/-- `na.BuchiCongruence` is of finite index if `na` has only finitely many states. -/
theorem buchiCongruence_fin_index [Finite State] : Finite (Quotient na.BuchiCongruence.eq) :=
  Finite.of_surjective na.BuchiCongrParam buchiCongrParam_surjective

/-- If `xl` and `yl` belong to the same equivalence class of `na.BuchiCongruence`
and `xl` can move `na` from state `s` to state `t`, then so can `yl` and, furthermore,
if `xl` makes `na` go through an accepting state of `na`, then so can `yl`. -/
lemma buchiCongruence_transfer
    {a : Quotient na.BuchiCongruence.eq} {xl yl : List Symbol} {s t : State}
    (hc : xl ∈ na.BuchiCongruence.eqvCls a) (hc' : yl ∈ na.BuchiCongruence.eqvCls a)
    (hp : xl ∈ na.pairLang s t) : ∃ sl, na.Execution s yl t sl ∧
      ( xl ∈ na.pairViaLang na.accept s t → ∃ r ∈ na.accept, r ∈ sl ) := by
  have h_eq : na.BuchiCongruence.eq xl yl := by
    apply Quotient.exact
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    have : ⟦xl⟧ = a := mem_singleton_iff.mp <| mem_preimage.mp hc
    have : ⟦yl⟧ = a := mem_singleton_iff.mp <| mem_preimage.mp hc'
    grind
  obtain ⟨l, r⟩ := h_eq s t
  by_cases h_xl : xl ∈ na.pairViaLang na.accept s t
  · obtain := LTS.mem_pairViaLang.mp (r.mp h_xl)
    grind [LTS.Execution, → LTS.Execution.comp, → LTS.Execution.of_mTr]
  · use LTS.Execution.of_mTr (l.mp hp) |>.choose
    grind

/-- `na.buchiFamily` is a family of ω-languages indexed by a pair of equivalence classes
of `na.BuchiCongruence` which will turn out to saturate the ω-language accepted by `na`
and cover all possible ω-sequences. -/
def buchiFamily [Inhabited Symbol] (na : Buchi State Symbol) :
    Quotient na.BuchiCongruence.eq × Quotient na.BuchiCongruence.eq → ωLanguage Symbol
  | (a, b) => na.BuchiCongruence.eqvCls a * (na.BuchiCongruence.eqvCls b)^ω

theorem mem_buchiFamily [Inhabited Symbol]
    {xs : ωSequence Symbol} {a b : Quotient na.BuchiCongruence.eq} :
    xs ∈ na.buchiFamily (a, b) ↔ ∃ xl, ∃ xls : ωSequence (List Symbol),
      xl ∈ na.BuchiCongruence.eqvCls a ∧ (∀ k, xls k ∈ na.BuchiCongruence.eqvCls b - 1) ∧
      xl ++ω xls.flatten = xs := by
  grind [buchiFamily]

open Finset in
/-- `na.buchiFamily` is a cover if `na` has only finitely many states.
This theorem uses the Ramsey theorem for infinite graphs and does not depend on any details
of `na.BuchiCongruence` other than that it is of finite index. -/
theorem buchiFamily_cover [Inhabited Symbol] [Finite State] :
    ⨆ i, na.buchiFamily i = ⊤ := by
  apply mem_ext
  intro xs
  have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  let color (t : Finset ℕ) : Quotient na.BuchiCongruence.eq :=
    if h : t.Nonempty then ⟦ xs.extract (t.min' h) (t.max' h) ⟧ else ⟦ [] ⟧
  obtain ⟨b, ns, h_ns, h_color⟩ := infinite_graph_ramsey color
  obtain ⟨f, h_mono, rfl⟩ := strictMono_of_infinite h_ns
  simp only [ωLanguage.mem_iSup, Prod.exists, ωLanguage.mem_top, iff_true]
  use ⟦ xs.take (f 0) ⟧, b
  apply mem_buchiFamily.mpr
  use xs.take (f 0), xs.drop (f 0) |>.toSegs (f · - f 0)
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  split_ands
  · rfl
  · intro k
    specialize h_color {f k, f (k + 1)}
    have := @h_mono 0 k
    have := @h_mono k (k + 1)
    simp only [Language.mem_sub_one, toSegs_def]
    split_ands
    · have : b = color {f k, f (k + 1)} := by grind
      simp_all only [extract_drop, color]
      split_ifs with h
      · have : f k ≤ f (k + 1) := by lia
        have : f 0 + (f k - f 0) = f k := by grind
        have : f 0 + (f (k + 1) - f 0) = f (k + 1) := by lia
        simp_all
        rfl
      · simp at h
    · grind
  · grind [Nat.base_zero_strictMono h_mono]

-- This intermediate result is split out of the proof of `buchiCongruence_saturation` below
-- because that proof was too big and kept exceeding the default `maxHeartbeats`.
private lemma frequently_via_accept [Inhabited Symbol]
    {xl : List Symbol} {xls : ωSequence (List Symbol)} {ss : ωSequence State}
    (h_acc : ∃ᶠ (k : ℕ) in atTop, ss k ∈ na.accept)
    (h_exec : na.OmegaExecution ss (xl ++ω xls.flatten))
    (h_xls_p : ∀ (k : ℕ), (xls k).length > 0)
    (f : ℕ → ℕ) (h_f : f = fun k => xl.length + xls.cumLen k)
    (ts : ωSequence State) (h_ts : ts = ωSequence.mk (fun k ↦ ss (f k))) :
    ∃ᶠ (k : ℕ) in atTop, xls k ∈ na.pairViaLang na.accept (ts k) (ts (k + 1)) := by
  have hm : StrictMono f := by grind [StrictMono, cumLen_strictMono]
  apply Frequently.mono <| frequently_in_strictMono hm h_acc
  rintro n ⟨k, _, _⟩
  apply LTS.mem_pairViaLang.mpr
  use ss (f n + k), by grind, (xls n).take k, (xls n).drop k
  have := extract_flatten h_xls_p n
  have exec {m n} (h : m ≤ n) :=
    LTS.Execution.to_mTr <| LTS.OmegaExecution.extract_execution h_exec h
  split_ands
  · have h : f n ≤ f n + k := by lia
    specialize exec h
    grind [extract_append_right_right]
  · have h : f n + k ≤ f (n + 1) := by lia
    specialize exec h
    grind [extract_append_right_right]
  · grind only [!List.take_append_drop]

/-- `na.buchiFamily` saturates the ω-language accepted by `na`. -/
theorem buchiFamily_saturation [Inhabited Symbol] :
    Saturates (fun i ↦ (na.buchiFamily i).toSet) (language na).toSet := by
  rintro ⟨a, b⟩ ⟨xs, h_xs, h_lang⟩ ys h_ys
  obtain ⟨xl, xls, h_xl_c, h_xls_c, rfl⟩ := mem_buchiFamily.mp h_xs
  obtain ⟨yl, yls, h_yl_c, h_yls_c, rfl⟩ := mem_buchiFamily.mp h_ys
  obtain ⟨ss, ⟨h_init, h_exec⟩, h_acc⟩ := h_lang
  let f (k : ℕ) := xl.length + xls.cumLen k
  let ts := ωSequence.mk (fun k ↦ ss (f k))
  have (k : ℕ) : xls k ≠ [] := by grind [Language.mem_sub_one]
  have h_xls_p (k : ℕ) : (xls k).length > 0 := List.length_pos_iff.mpr (this k)
  have h_xls_e (k : ℕ) : xls k ∈ na.pairLang (ts k) (ts (k + 1)) := by
    grind [LTS.OmegaExecution.extract_mTr h_exec (?_ : f k ≤ f (k + 1)), LTS.mem_pairLang,
      extract_append_right_right, add_tsub_cancel_left]
  have h_yls (k : ℕ) := buchiCongruence_transfer ((h_xls_c k).left) ((h_yls_c k).left) (h_xls_e k)
  choose sls h_yls_e h_yls_a using h_yls
  have (k : ℕ) : yls k ≠ [] := by grind [Language.mem_sub_one]
  have h_yls_p (k : ℕ) : (yls k).length > 0 := List.length_pos_iff.mpr (this k)
  obtain ⟨ss1, h_ss1_run, h_ss1_seg⟩ := LTS.OmegaExecution.flatten_execution h_yls_e h_yls_p
  suffices ∃ᶠ (k : ℕ) in atTop, ss1 k ∈ na.accept by
    have h_xl_e : xl ∈ na.pairLang (ss 0) (ts 0) := by
      grind [LTS.OmegaExecution.extract_mTr h_exec (?_ : 0 ≤ xl.length),
        extract_append_zero_right, LTS.mem_pairLang]
    have h_yl_e : yl ∈ na.pairLang (ss 0) (ts 0) := by
      grind [buchiCongruence_transfer h_xl_c h_yl_c h_xl_e, LTS.mem_pairLang, LTS.Execution.to_mTr]
    have h_ss1_ts : ss1 0 = ts 0 := by
      have h : 0 < yls.cumLen 1 - yls.cumLen 0 := by grind
      have : sls 0 ≠ [] := by grind
      have : 0 < (sls 0).length := List.length_pos_iff.mpr this
      have : ss1 0 = (sls 0)[0] := by grind [get_extract (xs := ss1) h]
      have : (sls 0)[0] = ts 0 := h_yls_e 0 |>.choose_spec |>.1
      grind
    obtain ⟨ss2, _, _, _, _⟩ := LTS.OmegaExecution.append h_yl_e h_ss1_run h_ss1_ts
    use ss2
    have := @drop_frequently_iff_frequently _ ss2 na.accept yl.length
    grind [Run.mk]
  apply frequently_atTop.mpr
  intro n
  obtain ⟨m, _, s, _, h_mem⟩ :=
    frequently_atTop.mp ((frequently_via_accept h_acc h_exec h_xls_p f rfl ts rfl).mono h_yls_a) n
  obtain ⟨k, _, _⟩ := List.mem_iff_getElem.mp h_mem
  use yls.cumLen m + k
  suffices ss1 (yls.cumLen m + k) = (sls m)[k] by
    have h_mono := cumLen_strictMono h_yls_p
    have := StrictMono.add_le_nat h_mono m 0
    lia
  obtain ⟨_, _, _, _⟩ := h_yls_e m
  obtain ⟨_, _, _, _⟩ := h_yls_e (m + 1)
  grind =>
   have := @get_extract (xs := ss1)
   have : k < (yls m).length ∨ ¬ k < (yls m).length
   have : k < yls.cumLen (m + 1) - yls.cumLen m ∨ 0 < yls.cumLen (m + 2) - yls.cumLen (m + 1)
   finish

/-! ## Monoid structure on the Büchi-congruence quotient -/

/-- Left covariance of `na.BuchiCongruence`: if `u` and `u'` are Büchi-congruent
then `w ++ u` and `w ++ u'` are also Büchi-congruent for all finite words `w`.
This complements the right covariance provided by `RightCongruence` and is the
key ingredient for proving that concatenation of representatives is well-defined
on the quotient. -/
lemma buchiCongruence_left_cov {u u' : List Symbol}
    (h : na.BuchiCongruence.eq u u') (w : List Symbol) :
    na.BuchiCongruence.eq (w ++ u) (w ++ u') := by
  intro s t
  constructor
  · constructor
    · intro hw
      obtain ⟨r, h1, h2⟩ := LTS.pairLang_split hw
      exact LTS.pairLang_append h1 ((h r t).1.mp h2)
    · intro hw
      obtain ⟨r, h1, h2⟩ := LTS.pairLang_split hw
      exact LTS.pairLang_append h1 ((h r t).1.mpr h2)
  · constructor
    · intro hw
      obtain ⟨r, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := LTS.pairViaLang_split hw
      · exact LTS.pairViaLang_append_pairLang h1 ((h r t).1.mp h2)
      · exact LTS.pairLang_append_pairViaLang h1 ((h r t).2.mp h2)
    · intro hw
      obtain ⟨r, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := LTS.pairViaLang_split hw
      · exact LTS.pairViaLang_append_pairLang h1 ((h r t).1.mpr h2)
      · exact LTS.pairLang_append_pairViaLang h1 ((h r t).2.mpr h2)

/-- The `Monoid` instance on the quotient of `na.BuchiCongruence`:
- multiplication is `⟦u⟧ * ⟦v⟧ = ⟦u ++ v⟧` (list concatenation lifted to congruence classes);
- the identity element is `1 = ⟦[]⟧` (the class of the empty word).
Well-definedness of multiplication uses right covariance (from `RightCongruence`)
for the first argument and `buchiCongruence_left_cov` for the second argument. -/
instance buchiCongruence_instMonoid : Monoid (Quotient na.BuchiCongruence.eq) where
  mul a b := Quotient.liftOn₂ a b (fun u v => ⟦u ++ v⟧) fun u v u' v' hu hv =>
    Quotient.sound (na.BuchiCongruence.eq.trans
      (na.BuchiCongruence.right_cov.elim v hu)
      (buchiCongruence_left_cov hv u'))
  one := ⟦[]⟧
  mul_assoc a b c := by
    refine Quotient.inductionOn a fun u => ?_
    refine Quotient.inductionOn b fun v => ?_
    refine Quotient.inductionOn c fun w => ?_
    change (⟦(u ++ v) ++ w⟧ : Quotient na.BuchiCongruence.eq) = ⟦u ++ (v ++ w)⟧
    rw [List.append_assoc]
  one_mul a := by
    refine Quotient.inductionOn a fun u => ?_
    rfl
  mul_one a := by
    refine Quotient.inductionOn a fun u => ?_
    change (⟦u ++ []⟧ : Quotient na.BuchiCongruence.eq) = ⟦u⟧
    rw [List.append_nil]

/-- The quotient map sends concatenation to multiplication: `⟦u ++ v⟧ = ⟦u⟧ * ⟦v⟧`.
This is the canonical rewrite lemma for converting between `List.append` and
the monoid multiplication on `Quotient na.BuchiCongruence.eq`. -/
@[simp]
lemma buchiCongruence_mk_append (u v : List Symbol) :
    (⟦u ++ v⟧ : Quotient na.BuchiCongruence.eq) = ⟦u⟧ * ⟦v⟧ :=
  (Quotient.liftOn₂_mk (fun u v => ⟦u ++ v⟧) _ u v).symm

/-- Idempotent-power collapse helper: if `b * b = b` then `b ^ (n + 1) = b` for all `n`. -/
lemma buchiCongruence_pow_succ {b : Quotient na.BuchiCongruence.eq}
    (hb : b * b = b) (n : ℕ) : b ^ (n + 1) = b := by
  induction n with
  | zero => simp
  | succ m ih => simp only [pow_succ, ih, hb]

/-- Idempotent-power collapse: if `b * b = b` in the monoid of Büchi-congruence classes,
then `b ^ k = b` for all `k ≥ 1` (i.e., `k ≠ 0`). -/
lemma buchiCongruence_idempotentPow {b : Quotient na.BuchiCongruence.eq}
    (hb : b * b = b) {k : ℕ} (hk : k ≠ 0) : b ^ k = b := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n => exact buchiCongruence_pow_succ hb n

/-- Absorption corollary: if `b * b = b` and `a * b = a` in the monoid of Büchi-congruence
classes, then `a * b ^ k = a` for all `k ≥ 0`. For `k = 0`, `b ^ 0 = 1` and `a * 1 = a`.
For `k = n + 1`, `buchiCongruence_pow_succ` rewrites `b ^ (n + 1)` to `b`. -/
lemma buchiCongruence_absorption {a b : Quotient na.BuchiCongruence.eq}
    (hb : b * b = b) (hab : a * b = a) (k : ℕ) : a * b ^ k = a := by
  cases k with
  | zero => simp
  | succ n => rw [buchiCongruence_pow_succ hb, hab]

end Cslib.Automata.NA.Buchi
