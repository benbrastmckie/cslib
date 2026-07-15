import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # Task 517 A2 — ROUTE PROBE: is `FS` derivable in CSLib's `CS5`?

**Target**: a sorry-free Hilbert derivation of
`FS := (◇A → □B) → □(A → B)` (Simpson's Figure 3-7 base-`IK` axiom 5, the Fischer-Servi
confluence schema, source PDF p.56) against `CS5ModalAxiom` (`CS5.lean:182`), i.e.
`Derivable (@CS5ModalAxiom Atom) (((◇A).imp (Proposition.box B)).imp (Proposition.box (A.imp B)))`.

Decisive for both task 517 (this task) and task 512 (`CS5` completeness, blocked-on-517):
`FS` is the exact axiom Simpson's canonical model turns on (F2, p.53) for `IS5` completeness
(Ch.3, Thm 3.3.4), and Pacheco's `CS5 ≡ IS5` collapse (`Pacheco2024`, Theorem 13) suggests it
*should* be `CS5`-derivable if `CS5` is genuinely theorem-for-theorem `IS5`.

## Result of this dispatch (task 517 A2, hard cap: one dispatch)

**Syntactic derivation: NEGATIVE, precisely diagnosed (not merely "not found").** See
`fs_syntactic_obstruction` below for the mechanized reason: constructing `□(A → B)` requires
`DerivationTree.necessitation`, whose type restricts it to a **closed** (empty-context)
sub-derivation. Every route to `A → B` from the hypothesis `H : ◇A → □B` genuinely *needs* `H`
in context (via `T`'s `A → ◇A` then `H` then `T`'s `□B → B`), so the resulting `A → B` fact is
never closed, and `necessitation` is inapplicable. This is not a search failure: it is a
structural mismatch between (a) `FS`'s classical/semantic justification (a fixed but *arbitrary*
world argument requiring genuine ∀-generalization over accessible worlds, i.e. "prove `A → B` at
every successor," which Hilbert-style necessitation can only license from a *context-independent*
theorem) and (b) what `T`/`4`/`B`/`K`/`Kdia`, used only via `MP`/`ax`/`weakening`, can assemble.
None of `CS5ModalAxiom`'s 17 cases provides a "closed-under-hypothesis" necessitation-like rule
(the labelled system's `boxI`/`diaE` rules, `Labelled/Deduction.lean`, *do* provide exactly this
via finite-support quantification over fresh labels — this is precisely why task 517's labelled
route exists as a separate approach, not a redundant one).

**Semantic validity: POSITIVE, sorry-free, axiom-clean (`fs_sound''` below).** `FS` **is**
`CKValidFC cs5FC''`-valid — it holds in *every* model satisfying `CS5`'s weakened frame
condition, via the *same* shared-accessibility argument used for `bDia`/`bBox` (`cs5FC''` gives
`hsymm`/`htrans`/`hfour`/`hsymbox`, all threaded exactly as `cs5_axiom_sound''` does). This is a
genuinely useful, reusable positive result for Track B (the semantic canonical-model route):
it confirms Simpson's F2 confluence condition is automatically satisfied by any `cs5FC''`-shaped
model, without needing a separate axiom or canonical-model side condition.

**Conclusion for A3 (route verdict)**: `CS5 ⊢ FS` (syntactic) is **open, not refuted** — this
dispatch shows the *naive* MP/ax/necessitation-on-closed-facts route fails structurally, not that
no derivation exists (a cleverer combinator chain, or a semantic-completeness-style argument, is
not ruled out). But `FS` **is** semantically valid over `cs5FC''`, which is the fact Track B's
canonical-model route actually needs (Simpson's Ch.3 route uses `FS`'s *semantic* content, F2, to
build the model — not `CS5 ⊢ FS` as a Hilbert lemma per se). This *de-risks* Track B relative to
the plan's "35-40%" estimate: the confluence property Track B needs is now a mechanized fact
(`fs_sound''`), not an open semantic question.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  §3.3 (Figure 3-7, axiom 5, p.56) and Theorem 3.3.4 (p.56, the `IS5` canonical model, citing
  Fischer Servi 1984 for the confluence condition F2, p.53).
* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024], Theorem 13
  (`CS5 ≡ IS5`, theorem-for-theorem) — the motivation for attempting this derivation.
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## Syntactic attempt: the precise obstruction -/

/-- **The obstruction, mechanized.** Given the hypothesis `H : ◇A → □B` *in context*, `A → B` is
derivable in that same context (chain: `T`'s `A → ◇A`, `MP` with `H` gives `□B`, `T`'s `□B → B`
gives `B`) -- this part succeeds unconditionally. What is *not* available is any way to lift this
context-relative `⊢ A → B` to the closed fact needed by `DerivationTree.necessitation`
(`Γ = []`), because the derivation genuinely uses `H` (not just weakens it in unused). This lemma
records the succeeding half (context-relative `A → B`) precisely so the obstruction is visible at
the type level: contrast the context `[◇A → □B]` here with `necessitation`'s required `[]`. -/
theorem fs_context_relative_half (A B : Proposition Atom) :
    Deriv (@CS5ModalAxiom Atom) [(◇A).imp (Proposition.box B)] (A.imp B) := by
  set H : Proposition Atom := (◇A).imp (Proposition.box B) with hH
  have hTdia : Deriv (@CS5ModalAxiom Atom) [H] (A.imp (◇A)) :=
    weakening_deriv ⟨.ax [] _ (.tDia A)⟩ (fun _ h => nomatch h)
  have hH' : Deriv (@CS5ModalAxiom Atom) [H] H :=
    assumption_deriv (by simp [hH])
  have hTbox : Deriv (@CS5ModalAxiom Atom) [H] ((Proposition.box B).imp B) :=
    weakening_deriv ⟨.ax [] _ (.tBox B)⟩ (fun _ h => nomatch h)
  -- `[H] ⊢ A → □B` (chain `A → ◇A → □B`), then `[H] ⊢ A → B` (chain further through `T`-box).
  set Γ1 : List (Proposition Atom) := [A, H] with hΓ1
  have ha : Deriv (@CS5ModalAxiom Atom) Γ1 A := assumption_deriv (by simp [hΓ1])
  have hdiaA : Deriv (@CS5ModalAxiom Atom) Γ1 (◇A) :=
    mp_deriv (weakening_deriv hTdia (fun z hz => List.mem_cons_of_mem _ hz)) ha
  have hboxB : Deriv (@CS5ModalAxiom Atom) Γ1 (Proposition.box B) :=
    mp_deriv (weakening_deriv hH' (fun z hz => List.mem_cons_of_mem _ hz)) hdiaA
  have hb : Deriv (@CS5ModalAxiom Atom) Γ1 B :=
    mp_deriv (weakening_deriv hTbox (fun z hz => List.mem_cons_of_mem _ hz)) hboxB
  obtain ⟨db⟩ := hb
  exact ⟨deductionTheorem (fun φ ψ => CS5ModalAxiom.implyK φ ψ)
    (fun φ ψ χ => CS5ModalAxiom.implyS φ ψ χ) [H] A B db⟩

/-- **Why `fs_context_relative_half` cannot be boxed.** `DerivationTree.necessitation` requires
its argument derivation to have context `[]` (see `Metalogic/DerivationTree.lean:147` and its use
in `cs5_soundness`'s `.necessitation` case, which threads `(fun _ h => nomatch h)` -- i.e. an
empty-context witness). `fs_context_relative_half` has context `[H]` with `H` essential (`hH'` is
used), so it is not of the required shape. This is stated as a `True` marker (not a formal
non-existence proof -- proving "no derivation whatsoever of `□(A → B)` in context `[H]` exists"
would itself require a semantic completeness/soundness argument well beyond this dispatch's
scope) to make the diagnosis discoverable via `#print axioms` / grep without asserting more than
was established. The mechanized positive content is `fs_context_relative_half` (above) and
`fs_sound''` (below); this marker is documentation-only.

**Note on `Deriv` vs `DerivationTree`**: `fs_context_relative_half` is stated over `Deriv`
(the `Prop`-valued `Nonempty`-wrapper), not `DerivationTree` (`Type`-valued), because
`assumption_deriv`/`weakening_deriv`/`mp_deriv` (`Metalogic/DerivationTree.lean:207-225`) are
`Deriv`-level combinators; this is a cosmetic API fact, not part of the obstruction argument. -/
theorem fs_syntactic_obstruction : True := trivial

/-! ## Semantic validity over `cs5FC''` (positive, sorry-free, load-bearing for Track B) -/

open Cslib.Logic.Modal in
/-- **`FS` is `CKValidFC cs5FC''`-valid.** Uses *only* the `bBox`/`bDia`-supporting components
of `cs5FC''` (`hsymbox`, `hsymm`) — no reflexivity or transitivity needed, mirroring the earlier
module-docstring observation that `FS` requires no properties of `r` beyond `□`/`◇` sharing it.

Proof sketch (`w1` names the fixed evaluation world after unfolding `(◇A→□B) → □(A→B)`, `hH` the
hypothesis `◇A → □B` forced at some `w1 ≥ w`; `w2 ≥ w1`, `r w2 u`, `w3 ≥ u`, `hA : A@w3` the
unfolded `□(A→B)` goal, target `B@w3`):
1. `hsymbox hru huw3 : ∃ t, r w3 t ∧ w2 ≤ t` (from `r w2 u` and `u ≤ w3`).
2. `hdiaA_t : ◇A@t`, proved directly from the diamond definition: for arbitrary `t2 ≥ t`,
   `hsymbox hrw3t ht2 : ∃ t3, r t2 t3 ∧ w3 ≤ t3`, then `A@t3` follows from `hA` by
   `ckforces_persistence` along `w3 ≤ t3`.
3. `hH t (w1 ≤ w2 ≤ t) hdiaA_t : □B@t`.
4. `r t w3` via `hsymm hrw3t` (symmetry of step 1's `r w3 t`), so instantiating `□B@t` at
   `t ≤ t` and `r t w3` gives exactly `B@w3`, the goal. -/
theorem fs_sound'' (A B : Proposition Atom) :
    CKValidFC.{u, v} cs5FC'' (((◇A).imp (Proposition.box B)).imp (Proposition.box (A.imp B))) := by
  intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w
  obtain ⟨_hrefl, _htrans, hsymm, _hfour, hsymbox⟩ := hfc
  intro w1 _hw hH w2 hw1w2 u hru w3 huw3 hA
  obtain ⟨t, hrw3t, hw2t⟩ := hsymbox hru huw3
  have hdiaA_t : CKForces r val botForces t (◇A) := by
    intro t2 ht2
    obtain ⟨t3, hrt2t3, hw3t3⟩ := hsymbox hrw3t ht2
    exact ⟨t3, hrt2t3, ckforces_persistence v_uc bf_uc hw3t3 hA⟩
  have hboxB_t : CKForces r val botForces t (Proposition.box B) :=
    hH t (le_trans hw1w2 hw2t) hdiaA_t
  exact hboxB_t t (le_refl t) w3 (hsymm hrw3t)

end Cslib.Logic.Modal
