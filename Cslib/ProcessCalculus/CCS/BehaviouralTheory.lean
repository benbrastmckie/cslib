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

theorem bisim_par_nil (p : Process Name Constant) : (par p nil) ~[@lts Name Constant defs] p := by
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

theorem bisim_par_comm (p q : Process Name Constant) : (par p q) ~[@lts Name Constant defs] (par q p) := by
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

end CCS

end CCS.BehaviouralTheory
