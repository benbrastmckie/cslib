import Cslib.Init
import Cslib.Logics.Modal.Tableau.FrameSoundness

/-! # Task 515 — VERIFICATION GATE: is the 5/KB5 deliverable really unreachable from `s5Valid`?

Plan v3 drops the task description's 5/KB5 deliverable, claiming `fiveValid ⊊ s5Valid` and that
`□p → p` separates them. This file settles that claim by proof rather than by prose.

**Definitions verified verbatim against `FrameSoundness.lean`** (the plan's `fiveFC` line cite is
:1283; the actual line is :1282 — the only drift found):

    s5FC   := fun r => Std.Refl r ∧ Relation.RightEuclidean r    -- :1273
    fiveFC := fun r => Relation.RightEuclidean r                  -- :1282  (reflexivity absent)
    kb5FC  := fun r => Std.Symm r ∧ Relation.RightEuclidean r     -- :1291  (reflexivity absent)

**Verdict**: the four theorems below are sorry-free. The strict inclusion holds, and it holds for
the reason the plan gives. The separating countermodel is the one-world empty frame: `RightEuclidean`
and `Std.Symm` are both *vacuous* on the empty relation, so `□p` is vacuously true while `p` is
false. This is a fact about the frame classes, not about any tableau.

**Scope of what this does and does not establish.** It confirms `fiveValid ⊊ s5Valid`, hence an
`s5Valid` decision procedure does not compose into a `fiveValid` one. It does NOT establish that
5/KB5 completeness is unreachable *in principle* — K5 and KB5 are well-known to be complete and
decidable via a Euclidean-frame tableau. The honest claim is the narrower one: 5/KB5 is unreachable
*by this S5 route*, so delivering it means building a separate Euclidean tableau, not extending
this one.
-/

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Modal

namespace Task515SeparationProbe

/-! ## 1. The inclusion direction: every S5 frame is a Euclidean frame -/

/-- `s5FC` entails `fiveFC` by projection: S5 frames are Euclidean frames with reflexivity added. -/
theorem s5FC_imp_fiveFC {World : Type} {r : World → World → Prop} (h : s5FC r) : fiveFC r := h.2

/-- **Inclusion**: `fiveValid φ → s5Valid φ`. Validity over the larger (Euclidean) frame class is
the stronger requirement, so it descends to the smaller (S5) class. -/
theorem fiveValid_imp_s5Valid {Atom : Type} (φ : Proposition Atom) (h : fiveValid φ) :
    s5Valid φ := fun World m hFC w => h World m hFC.2 w

/-! ## 2. The separating formula: `□p → p` -/

/-- The one-world empty frame. `r` is the empty relation, and `p` is false at the sole world. -/
private def emptyFrame : Model Unit Unit where
  r := fun _ _ => False
  v := fun _ _ => False

/-- The empty relation is `RightEuclidean` — vacuously, since it has no edges to chain. -/
private instance : Relation.RightEuclidean emptyFrame.r where
  rightEuclidean hab _ := absurd hab id

/-- The empty relation is `Std.Symm` — vacuously, for the same reason. This is what makes the
countermodel serve `kb5FC` as well as `fiveFC`. -/
private instance : Std.Symm emptyFrame.r where
  symm _ _ hab := absurd hab id

/-- `□p` holds vacuously at the sole world of the empty frame: there is no accessible world. -/
private theorem box_atom_holds : Satisfies emptyFrame () (.box (.atom ())) :=
  fun _ hr => absurd hr id

/-- `p` fails at the sole world of the empty frame. -/
private theorem atom_fails : ¬ Satisfies emptyFrame () (.atom ()) := id

/-- **`□p → p` is `s5Valid`**, discharged by reflexivity alone — this is the `T` axiom. -/
theorem boxImp_s5Valid (p : Unit) : s5Valid (.imp (.box (.atom p)) (.atom p)) := by
  intro World m hFC w hbox
  exact hbox w (hFC.1.refl w)

/-- **`□p → p` is NOT `fiveValid`**: the one-world empty frame is Euclidean and refutes it.
Reflexivity is exactly what `fiveFC` drops, and exactly what the proof above needed. -/
theorem boxImp_not_fiveValid : ¬ fiveValid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := by
  intro h
  exact atom_fails
    (h Unit emptyFrame (inferInstanceAs (Relation.RightEuclidean emptyFrame.r)) () box_atom_holds)

/-- **`□p → p` is NOT `kb5Valid`** either: the same countermodel is symmetric. So the gap is not
repaired by moving from 5 to KB5 — `kb5FC` drops reflexivity too. -/
theorem boxImp_not_kb5Valid : ¬ kb5Valid (Atom := Unit) (.imp (.box (.atom ())) (.atom ())) := by
  intro h
  exact atom_fails (h Unit emptyFrame ⟨inferInstance, inferInstance⟩ () box_atom_holds)

/-! ## 3. The verdict -/

/-- **`fiveValid ⊊ s5Valid`**: the inclusion is strict, witnessed by `□p → p`.

This is the claim plan v3 rests its scope correction on, and it is TRUE. A sound+complete decision
procedure for `s5Valid` cannot decide `fiveValid`: the S5 tableau's closure sits on the wrong side
of a strict inclusion. -/
theorem fiveValid_ssubset_s5Valid :
    (∀ φ : Proposition Unit, fiveValid φ → s5Valid φ) ∧
    (∃ φ : Proposition Unit, s5Valid φ ∧ ¬ fiveValid φ) :=
  ⟨fun φ => fiveValid_imp_s5Valid φ,
   ⟨.imp (.box (.atom ())) (.atom ()), boxImp_s5Valid (), boxImp_not_fiveValid⟩⟩

/-- `s5FC` entails `kb5FC`: reflexivity and right-Euclideanness together give symmetry. Proved
directly (`rightEuclidean ab (refl a) : r b a`) rather than via the `[Std.Refl r] : Std.Symm r`
instance at `Euclidean.lean:53`, so the argument is legible without instance-resolution context. -/
theorem s5FC_imp_kb5FC {World : Type} {r : World → World → Prop} (h : s5FC r) : kb5FC r := by
  obtain ⟨hrefl, heucl⟩ := h
  exact ⟨⟨fun a _ ab => heucl.rightEuclidean ab (hrefl.refl a)⟩, heucl⟩

/-- **Inclusion**: `kb5Valid φ → s5Valid φ`. -/
theorem kb5Valid_imp_s5Valid {Atom : Type} (φ : Proposition Atom) (h : kb5Valid φ) :
    s5Valid φ := fun World m hFC w => h World m (s5FC_imp_kb5FC hFC) w

/-- The same, for KB5: `kb5Valid ⊊ s5Valid`. -/
theorem kb5Valid_ssubset_s5Valid :
    (∀ φ : Proposition Unit, kb5Valid φ → s5Valid φ) ∧
    (∃ φ : Proposition Unit, s5Valid φ ∧ ¬ kb5Valid φ) :=
  ⟨fun φ => kb5Valid_imp_s5Valid φ,
   ⟨.imp (.box (.atom ())) (.atom ()), boxImp_s5Valid (), boxImp_not_kb5Valid⟩⟩

end Task515SeparationProbe

end Cslib.Logic.Modal.Tableau
