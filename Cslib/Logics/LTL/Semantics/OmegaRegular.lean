/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.Satisfies
public import Cslib.Computability.Languages.OmegaRegularLanguage
public import Cslib.Logics.LTL.Semantics.GNBA

/-! # Omega-Regularity of LTL Languages

This module proves that for every LTL formula `φ` over a finite atom set, the set of
ω-words satisfying `φ` at the initial state is an ω-regular language. The alphabet is
`Set Atom` with `[Fintype Atom]`, and the valuation used is `fun p s => p ∈ s`,
interpreting each element of the sequence as the set of atoms that hold at that state.

## Main definitions

- `Formula.omegaLanguage φ` : the ω-language over `Set Atom` of ω-words satisfying `φ`

## Main theorems

- `Formula.isRegular` : the ω-language of every LTL formula is ω-regular (all cases proved,
  including `untl` via the GNBA construction in `GNBA.lean`)

## Design

The alphabet `Set Atom` is used rather than `Atom → Prop` because `Set Atom` is finite when
`Atom` is finite (`[Fintype Atom]`), matching the finite-state requirement of `IsRegular`.
The valuation `fun p s => p ∈ s` bridges the `Set Atom`-valued sequence to the
`Atom → State → Prop` signature of `Satisfies`.

## References

* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Set Filter ωSequence Automata ωAcceptor NA NA.Buchi Cslib.ωLanguage
open scoped Computability

/-! ## Language definition -/

/-- The ω-language of an LTL formula over `Set Atom`.

`v : ωSequence (Set Atom)` is interpreted as a valuation `fun p s => p ∈ s`, and
the membership relation checks `Satisfies` at the initial state (head of `v`). -/
def Formula.omegaLanguage {Atom : Type*} (φ : Formula Atom) : ωLanguage (Set Atom) :=
  ⟨{ v | Satisfies (fun p s => p ∈ s) v φ }⟩

/-- Membership in `Formula.omegaLanguage`: unfolds the set membership. -/
@[simp]
theorem mem_omegaLanguage {Atom : Type*} {φ : Formula Atom} {v : ωSequence (Set Atom)} :
    v ∈ φ.omegaLanguage ↔ Satisfies (fun p s => p ∈ s) v φ :=
  Iff.rfl

/-! ## Atom case -/

/-- NBA for `atom p`: a two-state automaton that accepts `v` iff `p ∈ v 0`.

State `none` is the (non-accepting) initial state; state `some ()` is the (accepting) sink.
The automaton checks `p ∈ a` on the first step, then stays in the accepting state forever. -/
private def atomNBA {Atom : Type*} (p : Atom) : NA.Buchi (Option Unit) (Set Atom) where
  Tr s a t := (s = none ∧ p ∈ a ∧ t = some ()) ∨ (s = some () ∧ t = some ())
  start := {none}
  accept := {some ()}

/-- The language of `atomNBA p` is the ω-language of `atom p`. -/
private theorem atomNBA_language_eq {Atom : Type*} (p : Atom) :
    language (atomNBA p) = (Formula.atom p).omegaLanguage := by
  apply ωLanguage.mem_ext
  intro xs
  simp only [mem_language, mem_omegaLanguage, Satisfies]
  constructor
  · rintro ⟨ss, ⟨h_start, h_trans⟩, _⟩
    simp only [atomNBA, Set.mem_singleton_iff] at h_start
    have h_step := h_trans 0
    simp only [atomNBA, h_start] at h_step
    rcases h_step with ⟨_, hp, _⟩ | ⟨h, _⟩
    · exact hp
    · simp at h
  · intro hp
    -- Run: ss 0 = none; ss n = some () for n ≥ 1
    let ss : ωSequence (Option Unit) := ⟨fun n => if n = 0 then none else some ()⟩
    refine ⟨ss, ⟨?_, ?_⟩, ?_⟩
    · -- ss 0 = none ∈ {none}
      simp [atomNBA, ss]
    · -- transitions
      intro i
      simp only [atomNBA, ss]
      by_cases hi : i = 0
      · -- i = 0: none →[xs 0] some () because p ∈ xs 0
        subst hi; exact Or.inl ⟨rfl, hp, rfl⟩
      · -- i ≠ 0: some () →[xs i] some ()
        simp [hi]
    · -- accept = {some ()} visited infinitely often
      simp only [atomNBA, ss]
      rw [frequently_atTop]
      intro k
      refine ⟨k + 1, Nat.le_add_right k 1, ?_⟩
      simp

/-- The ω-language of an atomic formula is ω-regular. -/
theorem Formula.isRegular_atom {Atom : Type*} (p : Atom) :
    (Formula.atom p : Formula Atom).omegaLanguage.IsRegular :=
  ⟨Option Unit, inferInstance, atomNBA p, atomNBA_language_eq p⟩

/-! ## Bot case -/

/-- The ω-language of `bot` is the empty language. -/
private theorem omegaLanguage_bot_eq {Atom : Type*} :
    (Formula.bot : Formula Atom).omegaLanguage = ⊥ := by
  apply ωLanguage.mem_ext
  intro xs
  simp [Satisfies]

/-- The ω-language of `bot` is ω-regular. -/
theorem Formula.isRegular_bot {Atom : Type*} :
    (Formula.bot : Formula Atom).omegaLanguage.IsRegular := by
  rw [omegaLanguage_bot_eq]
  exact Cslib.ωLanguage.IsRegular.bot

/-! ## Imp case -/

/-- `L(φ → ψ) = L(φ)ᶜ ⊔ L(ψ)`. -/
private theorem omegaLanguage_imp {Atom : Type*} (φ ψ : Formula Atom) :
    (Formula.imp φ ψ).omegaLanguage = φ.omegaLanguage ᶜ ⊔ ψ.omegaLanguage := by
  apply ωLanguage.mem_ext
  intro xs
  simp only [ωLanguage.sup_def, ωLanguage.compl_def, ωLanguage.mem_def, Set.mem_union,
    Set.mem_compl_iff]
  tauto

/-- The ω-language of `imp φ ψ` is ω-regular, given IH for both subformulas.

Requires `Atom : Type` (not `Type*`) because `IsRegular.compl` requires `Symbol : Type`. -/
theorem Formula.isRegular_imp {Atom : Type} {φ ψ : Formula Atom}
    (hφ : φ.omegaLanguage.IsRegular) (hψ : ψ.omegaLanguage.IsRegular) :
    (Formula.imp φ ψ).omegaLanguage.IsRegular := by
  rw [omegaLanguage_imp]
  exact Cslib.ωLanguage.IsRegular.sup (Cslib.ωLanguage.IsRegular.compl hφ) hψ

/-! ## Next case -/

/-- NBA for `next φ` given `na : NA.Buchi State (Set Atom)` recognizing `L(φ)`.

The construction adds a fresh initial state `none`. On the first step, the automaton
transitions from `none` to any start state of `na` (reading the first symbol arbitrarily).
Subsequent steps simulate `na`. This accepts exactly the ω-sequences whose tails are in
the language of `na`. -/
private def nextNBA {State : Type*} (na : NA.Buchi State (Set Atom)) :
    NA.Buchi (Option State) (Set Atom) where
  Tr s a t :=
    match s with
    | none => match t with
      | none => False
      | some t' => t' ∈ na.start
    | some s' => match t with
      | none => False
      | some t' => na.Tr s' a t'
  start := {none}
  accept := some '' na.accept

/-- The language of `nextNBA na` is `{ xs | xs.tail ∈ language na }`. -/
private theorem nextNBA_language_eq {State : Type*} (na : NA.Buchi State (Set Atom)) :
    language (nextNBA na) = ⟨{ xs | xs.tail ∈ language na }⟩ := by
  apply ωLanguage.mem_ext
  intro xs
  simp only [ωLanguage.mem_def, Set.mem_setOf]
  constructor
  · rintro ⟨ss, ⟨h_start, h_trans⟩, h_acc⟩
    simp only [nextNBA, Set.mem_singleton_iff] at h_start
    -- After the first step, all states are `some _`
    have h_some : ∀ n, ∃ s, ss (n + 1) = some s := by
      intro n
      induction n with
      | zero =>
        have h_step := h_trans 0
        simp only [nextNBA, h_start] at h_step
        match h : ss 1 with
        | none => simp only [h] at h_step
        | some t => exact ⟨t, rfl⟩
      | succ n ih =>
        obtain ⟨s, hs⟩ := ih
        have h_step := h_trans (n + 1)
        simp only [nextNBA, hs] at h_step
        match h : ss (n + 2) with
        | none => simp only [h] at h_step
        | some t => exact ⟨t, rfl⟩
    -- Define the projected inner run
    let inner : ωSequence State := ⟨fun n => (h_some n).choose⟩
    -- inner n value is the state ss (n+1) stripped of `some`
    have h_inner : ∀ n, ss (n + 1) = some (inner n) := fun n => (h_some n).choose_spec
    use inner
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- inner 0 ∈ na.start
      have h_step := h_trans 0
      simp only [nextNBA, h_start] at h_step
      rw [h_inner 0] at h_step
      simp only [] at h_step
      exact h_step
    · -- na.OmegaExecution inner xs.tail
      intro i
      have h_step := h_trans (i + 1)
      simp only [nextNBA, h_inner i, h_inner (i + 1)] at h_step
      exact h_step
    · -- Accepting: na.accept visited infinitely often in inner
      simp only [nextNBA] at h_acc
      rw [frequently_atTop] at h_acc ⊢
      intro k
      obtain ⟨j, hj, h_acc_j⟩ := h_acc (k + 1)
      simp only [Set.mem_image] at h_acc_j
      obtain ⟨s, hs, hs_eq⟩ := h_acc_j
      refine ⟨j - 1, by omega, ?_⟩
      have hj_pos : 0 < j := by omega
      have h_eq : ss j = some (inner (j - 1)) := by
        cases j with
        | zero => omega
        | succ j => simp only [Nat.succ_sub_one]; exact h_inner j
      rw [← hs_eq] at h_eq
      have : inner (j - 1) = s := Option.some.inj h_eq.symm
      rw [this]
      exact hs
  · rintro ⟨inner, ⟨h_start, h_trans⟩, h_acc⟩
    -- Construct: ss 0 = none; ss (n+1) = some (inner n)
    let ss : ωSequence (Option State) := ⟨fun n => if n = 0 then none else some (inner (n - 1))⟩
    use ss
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [ss, nextNBA]
    · intro i
      unfold nextNBA; dsimp [ss]
      by_cases hi : i = 0
      · -- First step: none → some (inner 0)
        subst hi; change inner 0 ∈ na.start
        exact h_start
      · -- Subsequent steps: some (inner (i-1)) → some (inner i)
        simp [hi]
        have hi' : 0 < i := Nat.pos_of_ne_zero hi
        have := h_trans (i - 1)
        have h_eq : i - 1 + 1 = i := Nat.sub_add_cancel hi'
        rwa [show xs.tail (i - 1) = xs i from congrArg xs h_eq, h_eq] at this
    · -- Accepting condition
      simp only [nextNBA]
      rw [frequently_atTop] at h_acc ⊢
      intro k
      obtain ⟨j, hj, h_acc_j⟩ := h_acc k
      exact ⟨j + 1, by omega, by simp only [ss, Set.mem_image]; exact ⟨inner j, h_acc_j, rfl⟩⟩

/-- `L(◯φ) = { xs | xs.tail ∈ L(φ) }`. -/
private theorem omegaLanguage_next {Atom : Type*} (φ : Formula Atom) :
    (Formula.next φ).omegaLanguage = ⟨{ xs | xs.tail ∈ φ.omegaLanguage }⟩ := by
  apply ωLanguage.mem_ext
  intro xs
  simp only [Formula.omegaLanguage, ωLanguage.mem_def, Set.mem_setOf_eq, Satisfies]

/-- The ω-language of `next φ` is ω-regular, given IH for `φ`. -/
theorem Formula.isRegular_next {Atom : Type*} {φ : Formula Atom}
    (hφ : φ.omegaLanguage.IsRegular) : (Formula.next φ).omegaLanguage.IsRegular := by
  obtain ⟨State, h_fin, na, h_na⟩ := hφ
  rw [omegaLanguage_next]
  -- language (nextNBA na) = { xs | xs.tail ∈ language na } = { xs | xs.tail ∈ φ.omegaLanguage }
  have h_eq : language (nextNBA na) = ⟨{ xs | xs.tail ∈ φ.omegaLanguage }⟩ := by
    rw [nextNBA_language_eq, h_na]
  exact ⟨Option State, inferInstance, nextNBA na, h_eq⟩

/-! ## Until case -/

/-- Membership in `φ.omegaLanguage` at a shifted sequence: `v.drop k ∈ φ.omegaLanguage` iff
`φ` is satisfied at the initial state of `v.drop k`. -/
private theorem mem_omegaLanguage_drop {Atom : Type*} {φ : Formula Atom}
    {v : ωSequence (Set Atom)} {k : ℕ} :
    v.drop k ∈ φ.omegaLanguage ↔ Satisfies (fun p s => p ∈ s) (v.drop k) φ :=
  Iff.rfl

/-- The ω-language of `φ U ψ` (guard `φ`, event `ψ`) expressed via `drop`.

`v ∈ L(untl φ ψ)` iff there exists a position `j` such that `ψ` holds at `v.drop j`
(the event) and `φ` holds at every `v.drop k` for `k < j` (the guard). -/
private theorem omegaLanguage_untl {Atom : Type*} (φ ψ : Formula Atom) :
    (Formula.untl φ ψ).omegaLanguage =
      ⟨{ v | ∃ j, v.drop j ∈ ψ.omegaLanguage ∧ ∀ k < j, v.drop k ∈ φ.omegaLanguage }⟩ := by
  apply ωLanguage.mem_ext
  intro v
  simp only [Formula.omegaLanguage, ωLanguage.mem_def, Set.mem_setOf_eq, Satisfies]

/-- The ω-language of any LTL formula over a finite atom set is ω-regular.

Proved by exhibiting the NBA `gnbaNBA φ` (from `GNBA.lean`) with finite state type
`GNBANBAState φ`, whose language equals `φ.gnbaOmegaLanguage` by `gnba_language_eq`.
Since `gnbaOmegaLanguage` is definitionally equal to `omegaLanguage`, the result follows. -/
theorem Formula.isRegular' {Atom : Type} [Finite Atom] (φ : Formula Atom) :
    φ.omegaLanguage.IsRegular :=
  ⟨Formula.GNBANBAState φ, inferInstance, Formula.gnbaNBA φ, Formula.gnba_language_eq φ⟩

/-- The ω-language of `φ U ψ` (guard `φ`, event `ψ`) is ω-regular,
given IH for both subformulas.

Proved via the global GNBA construction (Baier-Katoen / Vardi-Wolper 1986). The hypotheses
`hφ` and `hψ` are not needed by this approach — the GNBA for `untl φ ψ` handles all
subformulas simultaneously — but the signature retains them for uniformity with the
inductive cases in `Formula.isRegular`. -/
theorem Formula.isRegular_untl {Atom : Type} [Finite Atom] {φ ψ : Formula Atom}
    (_hφ : φ.omegaLanguage.IsRegular) (_hψ : ψ.omegaLanguage.IsRegular) :
    (Formula.untl φ ψ).omegaLanguage.IsRegular :=
  Formula.isRegular' (Formula.untl φ ψ)

/-! ## Main theorem -/

/-- Every LTL formula over a finite atom set defines an ω-regular language.

The proof is by structural induction on `φ`:
- `atom p`: 2-state NBA checking first symbol membership
- `bot`: empty language (`IsRegular.bot`)
- `imp φ ψ`: `L(φ → ψ) = L(φ)ᶜ ⊔ L(ψ)` via complement and union closure
- `next φ`: NBA reading and discarding the first symbol, then simulating `φ`'s NBA
- `untl φ ψ`: via `Formula.isRegular_untl`, which uses the GNBA construction from `GNBA.lean`

The `untl` case uses the global GNBA tableau construction (Baier-Katoen / Vardi-Wolper 1986):
the GNBA for `untl φ ψ` has finite state type `GNBANBAState (untl φ ψ)` and is converted to
an NBA via the cycling counter construction. -/
theorem Formula.isRegular {Atom : Type} [Finite Atom] (φ : Formula Atom) :
    φ.omegaLanguage.IsRegular := by
  induction φ with
  | atom p => exact Formula.isRegular_atom p
  | bot => exact Formula.isRegular_bot
  | imp φ ψ hφ hψ => exact Formula.isRegular_imp hφ hψ
  | next φ hφ => exact Formula.isRegular_next hφ
  | untl φ ψ hφ hψ => exact Formula.isRegular_untl hφ hψ

end Cslib.Logic.LTL

end
