/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Data.FinFun
import Cslib.Semantics.LTS.Basic
import Cslib.Semantics.LTS.Bisimulation
import Cslib.ProcessCalculus.CCS.Basic
import Cslib.ProcessCalculus.CCS.Semantics

section CCS.BehaviouralTheory

variable {Name : Type u} {Constant : Type v} {defs : Constant ⇀ CCS.Process Name Constant}

open CCS CCS.Process CCS.Act

namespace CCS

private inductive ParNil : Rel (Process Name Constant) (Process Name Constant) where
| parNil : ParNil (par p nil) p

theorem bisimilarity_par_nil (p : Process Name Constant) : (par p nil) ~[@lts Name Constant defs] p := by
  constructor
  exists ParNil
  constructor; constructor
  simp only [Bisimulation]
  intro s1 s2 hr μ
  constructor
  case left =>
    intro s1' htr
    cases hr
    cases htr
    case parL p' htr =>
      exists p'
      apply And.intro htr ParNil.parNil
    case parR q' htr =>
      cases htr
    case com μ p' q' htrp htrq =>
      cases htrq
  case right =>
    intro s2' htr
    cases hr
    exists (par s2' nil)
    constructor
    case left =>
      apply tr.parL htr
    case right =>
      constructor

private inductive ParComm : Rel (Process Name Constant) (Process Name Constant) where
| parComm : ParComm (par p q) (par q p)

theorem bisimilarity_par_comm (p q : Process Name Constant) : (par p q) ~[@lts Name Constant defs] (par q p) := by
  constructor
  exists ParComm
  constructor
  case left =>
    constructor
  case right =>
    simp only [Bisimulation]
    intro s1 s2 hr μ
    cases hr
    case parComm p q =>
      constructor
      case left =>
        intro t htr
        cases htr
        case parL p' htr' =>
          exists (par q p')
          constructor
          · apply tr.parR htr'
          · constructor
        case parR q' htr' =>
          exists (par q' p)
          constructor
          · apply tr.parL htr'
          · constructor
        case com μ p' q' htrp htrq =>
          exists (par q' p')
          constructor
          · rw [← Act.co.involution Name μ] at htrp
            apply tr.com htrq htrp
          . constructor
      case right =>
        intro t htr
        cases htr
        case parL q' htr' =>
          exists (par p q')
          constructor
          · apply tr.parR htr'
          · constructor
        case parR p' htr' =>
          exists (par p' q)
          constructor
          · apply tr.parL htr'
          · constructor
        case com μ p' q' htrp htrq =>
          exists (par q' p')
          constructor
          · rw [← Act.co.involution Name μ] at htrp
            apply tr.com htrq htrp
          . constructor

private inductive PreBisim : Rel (Process Name Constant) (Process Name Constant) where
| pre : (p ~[@lts Name Constant defs] q) → PreBisim (pre μ p) (pre μ q)
| bisim : (p ~[@lts Name Constant defs] q) → PreBisim p q

theorem bisimilarity_congr_pre : (p ~[@lts Name Constant defs] q) → (pre μ p) ~[@lts Name Constant defs] (pre μ q) := by
  intro hpq
  constructor
  exists @PreBisim _ _ defs
  constructor; constructor; assumption
  simp only [Bisimulation]
  intro s1 s2 hr μ'
  cases hr
  case pre =>
    rename_i p' q' μ hbis
    constructor
    case left =>
      intro s1' htr
      cases htr
      exists q'
      constructor; constructor
      apply PreBisim.bisim hbis
    case right =>
      intro s2' htr
      cases htr
      exists p'
      constructor; constructor
      apply PreBisim.bisim hbis
  case bisim hbis =>
    constructor
    case left =>
      intro s1' htr
      obtain ⟨_, _, r, hr, hb⟩ := hbis
      let hbisim := hb
      obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr μ' htr
      exists s2'
      apply And.intro htr2
      constructor
      apply Bisimilarity.largest_bisimulation _ r hbisim _ _ hr2
    case right =>
      intro s2' htr
      obtain ⟨_, _, r, hr, hb⟩ := hbis
      let hbisim := hb
      specialize hb _ _ hr μ'
      obtain ⟨hb1, hb2⟩ := hb
      specialize hb2 _ htr
      obtain ⟨s1', htr1, hr1⟩ := hb2
      exists s1'
      apply And.intro htr1
      constructor
      apply Bisimilarity.largest_bisimulation _ r hbisim s1' s2' hr1

private inductive ChoiceBisim : Rel (Process Name Constant) (Process Name Constant) where
| choice : (p ~[@lts Name Constant defs] q) → ChoiceBisim (choice p r) (choice q r)
| bisim : (p ~[@lts Name Constant defs] q) → ChoiceBisim p q

theorem bisimilarity_congr_choice : (p ~[@lts Name Constant defs] q) → (choice p r) ~[@lts Name Constant defs] (choice q r) := by
  intro h
  constructor
  exists @ChoiceBisim _ _ defs
  constructor; constructor; assumption
  simp only [Bisimulation]
  intro s1 s2 r μ
  constructor
  case left =>
    intro s1' htr
    cases r
    case choice p q r hbisim =>
      obtain ⟨_, _, rel, hr, hb⟩ := hbisim
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr μ htr
        exists s2'
        constructor
        · apply tr.choiceL htr2
        · constructor
          apply Bisimilarity.largest_bisimulation _ _ hb _ _ hr2
      case choiceR a b c htr =>
        exists s1'
        constructor
        · apply tr.choiceR htr
        · constructor
          apply Bisimilarity.refl
    case bisim hbisim =>
      obtain ⟨_, _, rel, hr, hb⟩ := hbisim
      obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr μ htr
      exists s2'
      constructor; assumption
      constructor
      apply Bisimilarity.largest_bisimulation _ _ hb _ _ hr2
  case right =>
    intro s2' htr
    cases r
    case choice p q r hbisim =>
      obtain ⟨_, _, rel, hr, hb⟩ := hbisim
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr μ htr
        exists s1'
        constructor
        · apply tr.choiceL htr1
        · constructor
          apply Bisimilarity.largest_bisimulation _ _ hb _ _ hr1
      case choiceR a b c htr =>
        exists s2'
        constructor
        · apply tr.choiceR htr
        · constructor
          apply Bisimilarity.refl
    case bisim hbisim =>
      obtain ⟨_, _, rel, hr, hb⟩ := hbisim
      obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr μ htr
      exists s1'
      constructor; assumption
      constructor
      apply Bisimilarity.largest_bisimulation _ _ hb _ _ hr1

theorem bisimilarity_congr (c : Context Name Constant) (p q : Process Name Constant) (h : p ~[@lts Name Constant defs] q) :
  c.fill p ~[@lts Name Constant defs] c.fill q := by
  induction c
  case hole =>
    simp only [Context.fill]
    exact h
  case pre μ c ih =>
    simp [Context.fill]
    apply bisimilarity_congr_pre ih
  case parL c r ih =>
    simp [Context.fill]
    -- apply bisimilarity_congr_par ih
    sorry
  case parR r c ih =>
    sorry
  case choiceL c r ih =>
    simp [Context.fill]
    apply bisimilarity_congr_choice
    exact ih
  case choiceR r c ih =>
    simp [Context.fill]
    have bisimilarity_choice_comm : ∀ p q, (choice p q) ~[@lts Name Constant defs] (choice q p) := by
      sorry
    apply Bisimilarity.trans
    · apply bisimilarity_choice_comm
    · apply Bisimilarity.trans
      · apply bisimilarity_congr_choice
        exact ih
      · apply bisimilarity_choice_comm
  case res =>
    sorry

end CCS

end CCS.BehaviouralTheory
