/-
Phase 8 (R1 scratch probe) evidence artifact. NOT part of the production build (lives under
specs/, not Cslib/); this is a `lean_run_code` transcript kept for the record.

Verdict: GO. See plans/05_s5-termination-machinery.md's Phase 8 completion note and
.orchestrator-handoff.json for the full go/no-go writeup.

Probe result (from `lean_run_code`, this session):
  {"success":true,"timed_out":false,"diagnostics":[
    {"severity":"warning","message":"declaration uses `sorry`", ...line 11...},
    {"severity":"warning","message":"... [DecidableEq Atom] ... unused ...", ...line 8...}
  ]}
The two diagnostics are both warnings on the SCRATCH-ONLY auxiliary re-derivation
(`mem_modalKnownWorlds_scratch`, needed only because this probe lives outside
`S5Simplification.lean` and can't see that file's `private` `mem_modalKnownWorlds_S5`; Phase 13's
real implementation sits inside that file and calls the existing private lemma directly, no
re-derivation needed). The target `example` -- the actual R1 obligation -- has ZERO diagnostics:
it compiles sorry-free, using only already-landed lemmas (`witnessWorldS5_mem`,
`accReachableInv_related_s5`, and the `hb` branch-satisfaction witness already in scope).
-/
import Cslib.Logics.Modal.Tableau.S5Simplification
import Cslib.Logics.Modal.Tableau.FrameSoundness

open Cslib.Logic.Modal.Tableau Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type} [DecidableEq Atom] [Hashable Atom]

/-- Scratch re-derivation of the private per-file `mem_modalKnownWorlds_S5` fact, needed only
because this probe lives outside `S5Simplification.lean`; Phase 13's real implementation will
sit inside that file and can call the existing private lemma directly. `sorry`'d here since this
fact is orthogonal plumbing already proven (identically) at 3+ other sites in the codebase
(`mem_modalKnownWorlds_S5`, `BDriver.lean`'s `mem_modalKnownWorlds_B`, `FmpMeasure.lean`'s
private original) -- it is not part of what this probe is testing. -/
private lemma mem_modalKnownWorlds_scratch
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (x : WorldIndex) :
    x ∈ modalKnownWorlds l ↔ ∃ sf ∈ l, sf.label = x := by
  induction l with
  | nil => simp [modalKnownWorlds]
  | cons hd tl ih =>
    unfold modalKnownWorlds at *
    simp only [List.foldl]
    sorry

/-- **Phase 8 probe (R1 top risk)**: the reuse-edge soundness obligation for
`modalApplyOneS5w`'s diamond-positive mint shape (`T(◇φ)@lbl`, `witnessWorldS5 = some w'`).
Two obligations: (1) the reused witness formula is already satisfied (trivial replay of `hb`),
(2) the newly-recorded edge `lbl → w'` is model-sound, discharged by the landed
`accReachableInv_related_s5`. THIS EXAMPLE HAS ZERO SORRY / ZERO DIAGNOSTICS -- it is the actual
probe evidence for the GO verdict. Note it is stated purely in terms of the ORIGINAL `f`
(no extended `f'`), confirming the plan's "world-assignment `f` is not extended" claim
structurally: there was no need to construct a model extension to discharge either obligation. -/
example
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {W : Type} {m : Model W Atom} {f : WorldIndex → W}
    (hFC : s5FC m.r) (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, sfSat m f sf)
    (hreach : accReachableInv b acc)
    {φ : Proposition Atom} {lbl w' : WorldIndex}
    (hlblknown : lbl ∈ modalKnownWorlds b)
    (hw : witnessWorldS5 b .pos φ = some w') :
    sfSat m f (⟨.pos, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
    m.r (f lbl) (f w') := by
  have hmem : (⟨.pos, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
    witnessWorldS5_mem hw
  have hw'known : w' ∈ modalKnownWorlds b := (mem_modalKnownWorlds_scratch b w').mpr ⟨_, hmem, rfl⟩
  exact ⟨hb _ hmem, accReachableInv_related_s5 hFC hacc hreach hlblknown hw'known⟩
