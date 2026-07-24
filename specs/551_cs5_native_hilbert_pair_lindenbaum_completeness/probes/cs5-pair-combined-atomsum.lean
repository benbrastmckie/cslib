import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # Probe (Phase 1, R1 de-risking): the combined `Atom ⊕ Atom` axiom system for `CS5`'s
box-backward pair construction.

**Goal (per the plan's Phase 1 gate)**: prove that `CS5PairAxiom`, the combined axiom system
over the doubled atom space `Atom ⊕ Atom` sketched by the research report (§7) and the archived
probe `cs5-pair-primeness.lean`'s docstring, is *simultaneously*:

(i) **sound** for the intended pair semantics — the two new cross-condition axioms
`□(τ_L B) → τ_R B` / `□(τ_R B) → τ_L B` are validated by any fallible-world model whose modal
relation `r` satisfies `cs5FC` (in particular its reflexivity clause), using a valuation that
tags both copies of the doubled atom space with the *same* underlying valuation; and

(ii) **`cl`-stable by construction** — because the cross-conditions are *axioms* of the combined
system (not an externally-imposed `Cons` predicate, unlike the archived probe's `cs5PairPoset`),
any set deductively closed under `CS5PairAxiom` satisfies them automatically, for free, via a
single `modus_ponens` step. This sidesteps exactly the gap the archived probe
(`specs/archive/509_.../probes/cs5-pair-primeness.lean`) and the research report
(`specs/551_.../reports/01_route-b-native-hilbert-cs5-research.md`, §6) diagnose: the natural
candidate `Cons_Y Z := boxInv Z ⊆ Y` (cross-condition, `Y` fixed *externally*) is not
closure-stable, because nothing prevents `cl (insert ψ Z)` from deriving a *new* boxed formula
whose witness was never required to lie in `Y`. Internalising the cross-condition as an axiom of
the *same* derivation system removes the external side-condition entirely: `Y` is no longer
fixed, it is *itself* the `τ_R`-projection of the very same growing `Z`, so the cross-condition is
a theorem of `Z`, inherited automatically by any deductively-closed extension.

**Distinct from the discarded `CS5Combined` scaffold** (`CS5Canonical.lean`'s module docstring):
that earlier `Atom ⊕ Atom` attempt re-entered Pacheco's unsound negation-completeness move
(`ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, unsound for a poset-maximal quasi-prime `Θ`). This probe's construction never
invokes negation-completeness anywhere: the cross-conditions are *axioms* (available via `MP` to
any set that already contains their antecedent), not something derived from maximality. The two
constructions are mathematically unrelated beyond both using a doubled atom space.

**Verdict of this probe**: both (i) and (ii) close sorry-free below. Per the plan's Phase 1 gate,
this DE-RISKS R1 and the implementation may proceed to Phase 2 (library functoriality
infrastructure) and beyond.

## References

* `specs/archive/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean` —
  the pair poset, the three landed ingredients, the `cl`-stability gap this probe repairs.
* `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — `CS5ModalAxiom`, `cs5_axiom_sound`,
  `cs5_symmetric_tail_box_gap`.
* `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — `cs5FC`.
* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024] — source of
  the pair-construction *technique* (not an importable soundness argument; see above).
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## Tagging maps and the combined axiom system -/

/-- Tag a proposition as belonging to the "left" copy of the doubled atom space `Atom ⊕ Atom`. -/
def tauL : Proposition Atom → Proposition (Atom ⊕ Atom) := Proposition.map Sum.inl

/-- Tag a proposition as belonging to the "right" copy of the doubled atom space `Atom ⊕ Atom`. -/
def tauR : Proposition Atom → Proposition (Atom ⊕ Atom) := Proposition.map Sum.inr

/-- **The combined `CS5` pair axiom system.** `CS5ModalAxiom` on each tagged copy (`left`/`right`)
plus the two cross-condition implications, internalised as *axioms* rather than as an externally
imposed invariant on a pair poset. -/
inductive CS5PairAxiom : Proposition (Atom ⊕ Atom) → Prop where
  /-- Every `CS5ModalAxiom` instance holds on the left-tagged copy. -/
  | left (ψ : Proposition Atom) (h : CS5ModalAxiom ψ) : CS5PairAxiom (tauL ψ)
  /-- Every `CS5ModalAxiom` instance holds on the right-tagged copy. -/
  | right (ψ : Proposition Atom) (h : CS5ModalAxiom ψ) : CS5PairAxiom (tauR ψ)
  /-- Cross-condition realising `boxInv X ⊆ Y`. -/
  | cross1 (B : Proposition Atom) : CS5PairAxiom ((Proposition.box (tauL B)).imp (tauR B))
  /-- Cross-condition realising `boxInv Y ⊆ X`. -/
  | cross2 (B : Proposition Atom) : CS5PairAxiom ((Proposition.box (tauR B)).imp (tauL B))

/-! ## (ii) `cl`-stability of the cross-conditions, as a corollary of internalisation

Any set deductively closed under `CS5PairAxiom` satisfies both cross-conditions -- no appeal to
preservation of an *external* side predicate under `cl` is needed (contrast the archived probe's
`Cons_Y Z := boxInv Z ⊆ Y`, not closure-stable for `Y` externally fixed). Here the "other side" is
never fixed externally: it is read off the very same set `Z`, via `tauR`/`tauL`, so the fact holds
uniformly for *every* deductively-closed `Z`, including every set reached during a Zorn/Lindenbaum
extension. -/

/-- **Cross-condition 1 is `cl`-stable.** For any `CS5PairAxiom`-deductively-closed `Z`,
`□(τ_L B) ∈ Z → τ_R B ∈ Z`, by a single `modus_ponens` against the internalised axiom
`cross1`. -/
theorem crossCond_left_stable {Z : Set (Proposition (Atom ⊕ Atom))}
    (hZ : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5PairAxiom Atom)) Z)
    {B : Proposition Atom} (hB : Proposition.box (tauL B) ∈ Z) : tauR B ∈ Z := by
  refine hZ [Proposition.box (tauL B)] (tauR B) ?_ ?_
  · intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hB
  · exact ⟨.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (CS5PairAxiom.cross1 B)) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_singleton.mpr rfl))⟩

/-- **Cross-condition 2 is `cl`-stable.** Symmetric to `crossCond_left_stable`, using `cross2`. -/
theorem crossCond_right_stable {Z : Set (Proposition (Atom ⊕ Atom))}
    (hZ : Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5PairAxiom Atom)) Z)
    {B : Proposition Atom} (hB : Proposition.box (tauR B) ∈ Z) : tauL B ∈ Z := by
  refine hZ [Proposition.box (tauR B)] (tauL B) ?_ ?_
  · intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hB
  · exact ⟨.modus_ponens _ _ _
      (.weakening [] _ _ (.ax [] _ (CS5PairAxiom.cross2 B)) (fun _ h => nomatch h))
      (.assumption _ _ (List.mem_singleton.mpr rfl))⟩

/-! ## (i) Semantic soundness of the combined axioms

`ckforces_map` transports `CKForces` along an atom relabeling `f`, when the target valuation
tags the relabeled copy with the same underlying source valuation. Applying it with
`f := Sum.inl`/`Sum.inr` at a *common* `val2` (both tags sharing the same underlying `val`) makes
forcing `τ_L B` and forcing `τ_R B` the *same fact* semantically -- so the cross-condition axioms
reduce to plain reflexivity of `r` (`cs5FC`'s first clause), with no negation-completeness step
anywhere. -/

/-- **Transport of `CKForces` along an atom relabeling.** If the target valuation `val2` tags the
image of `f` with the source valuation `val` (`hval2`), then `CKForces` on the relabeled formula
`φ.map f` (evaluated with `val2`) coincides with `CKForces` on `φ` itself (evaluated with `val`).
Proved by structural induction on `φ`; independent of `f`'s injectivity, and reusable at both
`Sum.inl` and `Sum.inr`. -/
theorem ckforces_map {Atom' : Type u} {World : Type v} [Preorder World]
    (r : World → World → Prop) (val : World → Atom → Prop) (botForces : World → Prop)
    (f : Atom → Atom') (val2 : World → Atom' → Prop)
    (hval2 : ∀ w a, val2 w (f a) = val w a) (w : World) (φ : Proposition Atom) :
    CKForces r val2 botForces w (φ.map f) ↔ CKForces r val botForces w φ := by
  induction φ generalizing w with
  | atom p => simpa using hval2 w p
  | bot => simp
  | imp φ ψ ihφ ihψ =>
    simp only [Proposition.map_imp, CKForces_imp]
    exact forall_congr' fun w' => forall_congr' fun _ => imp_congr (ihφ w') (ihψ w')
  | and φ ψ ihφ ihψ =>
    simp only [Proposition.map_and, CKForces_and]
    exact and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ =>
    simp only [Proposition.map_or, CKForces_or]
    exact or_congr (ihφ w) (ihψ w)
  | box φ ih =>
    simp only [Proposition.map_box, CKForces_box]
    exact forall_congr' fun w' => forall_congr' fun _ =>
      forall_congr' fun u => forall_congr' fun _ => ih u
  | diamond φ ih =>
    simp only [Proposition.map_diamond, CKForces_diamond]
    exact forall_congr' fun w' => forall_congr' fun _ =>
      exists_congr fun u => and_congr_right fun _ => ih u

/-- **Prototype (i): the combined axioms are sound for the intended pair semantics.** For any
fallible-world model whose modal relation `r` satisfies `cs5FC` (so in particular the ordinary
`CS5ModalAxiom` copies are sound, via `cs5_axiom_sound`), and any valuation `val2` tagging both
`τ_L`/`τ_R` copies with a common underlying `val`, every `CS5PairAxiom` instance is forced. The
two new cross-condition axioms are validated purely by `r`'s reflexivity: instantiate the boxed
hypothesis at the re-based world itself, then use `ckforces_map` (twice, at `Sum.inl` and
`Sum.inr`) to identify forcing `τ_L B` with forcing `τ_R B`. -/
theorem cs5PairAxiom_sound {World : Type v} [Preorder World] {r : World → World → Prop}
    (hfc : cs5FC r) {val : World → Atom → Prop} {botForces : World → Prop}
    (val2 : World → (Atom ⊕ Atom) → Prop)
    (hval2L : ∀ w a, val2 w (Sum.inl a) = val w a)
    (hval2R : ∀ w a, val2 w (Sum.inr a) = val w a)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (bf_val : ∀ {w : World} (p : Atom), botForces w → val w p)
    (bf_r : ∀ {w u : World}, botForces w → r w u → botForces u)
    (bf_r_wit : ∀ {w : World}, botForces w → ∃ u, r w u ∧ botForces u)
    {φ : Proposition (Atom ⊕ Atom)} (h : CS5PairAxiom φ) (w : World) :
    CKForces r val2 botForces w φ := by
  have hrefl := hfc.1
  cases h with
  | left ψ hψ =>
    exact (ckforces_map r val botForces Sum.inl val2 hval2L w ψ).mpr
      (cs5_axiom_sound hψ World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w)
  | right ψ hψ =>
    exact (ckforces_map r val botForces Sum.inr val2 hval2R w ψ).mpr
      (cs5_axiom_sound hψ World r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w)
  | cross1 B =>
    intro w' _hw' hbox
    have hB' : CKForces r val2 botForces w' (tauL B) := hbox w' (le_refl w') w' (hrefl w')
    have hBmid : CKForces r val botForces w' B :=
      (ckforces_map r val botForces Sum.inl val2 hval2L w' B).mp hB'
    exact (ckforces_map r val botForces Sum.inr val2 hval2R w' B).mpr hBmid
  | cross2 B =>
    intro w' _hw' hbox
    have hB' : CKForces r val2 botForces w' (tauR B) := hbox w' (le_refl w') w' (hrefl w')
    have hBmid : CKForces r val botForces w' B :=
      (ckforces_map r val botForces Sum.inr val2 hval2R w' B).mp hB'
    exact (ckforces_map r val botForces Sum.inl val2 hval2L w' B).mpr hBmid

/-- **Corollary: `CS5PairAxiom` is consistent** (has a model), instantiating `cs5PairAxiom_sound`
at the same trivial single-point model `cs5_consistent_incest` uses to witness `CS5`'s own
consistency (`World := Unit`, `r := fun _ _ => True`, `botForces := fun _ => False`). This shows
the combined system is not "too strong" in the crude sense of collapsing to triviality: it has a
genuine model, so the two cross-condition axioms do not, by themselves, force any particular
formula to hold that would not already need to. -/
theorem cs5PairAxiom_has_model {φ : Proposition (Atom ⊕ Atom)} (h : CS5PairAxiom φ) :
    CKForces (fun (_ _ : Unit) => True) (fun (_ : Unit) (_ : Atom ⊕ Atom) => True)
      (fun (_ : Unit) => False) Unit.unit φ := by
  have hfc : cs5FC (fun (_ _ : Unit) => True) := ⟨fun _ => trivial, fun _ _ _ => trivial,
    fun _ _ => trivial⟩
  exact cs5PairAxiom_sound hfc (fun (_ : Unit) (_ : Atom ⊕ Atom) => True)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => trivial) (fun _ h => h.elim) (fun _ h => h.elim)
    (fun h _ => h.elim) (fun h => h.elim) h Unit.unit

end Cslib.Logic.Modal

/-! ## Axiom checks -/

#print axioms Cslib.Logic.Modal.crossCond_left_stable
#print axioms Cslib.Logic.Modal.crossCond_right_stable
#print axioms Cslib.Logic.Modal.ckforces_map
#print axioms Cslib.Logic.Modal.cs5PairAxiom_sound
#print axioms Cslib.Logic.Modal.cs5PairAxiom_has_model
