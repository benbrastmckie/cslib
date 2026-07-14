import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! Probe for task 509 Phase 8: designated-formula-exclusion primeness for the box-backward pair.

**Corpus confirmation** (rule 2 of the Phase 8-11 dispatch): re-read via
`bash .claude/scripts/literature-search.sh --read ec3a8bddd907f0c4` (Lemma 16/17/18, the recovered
page-5 chunk) and `--read 39fb2b22fa8afe5a` (Lemma 18/19). Both defects hold exactly as the plan
states:
- Lemma 16's proof (delegated-to by Lemma 18: "As in the proof of Lemma 16") contains, verbatim in
  the chunk: *"if ϕ ∉ Θ and ψ ∉ Θ, we would have that ¬ϕ ∈ Θ and ¬ψ ∈ Θ. By MP, we would have
  ¬(ϕ ∨ ψ) ∈ Θ"* — the unlabelled negation-completeness move, unsound for a quasi-prime,
  poset-maximal `Θ` in a poset carrying cross-conditions (maximality can fail via `Θ'□ ⊄ Σ`, not
  inconsistency).
- Lemma 18's invariant is stated exactly as `ϕ ∉ X ∪ Y` alongside the cross-condition `Γ ⊆ Y`
  (chunk `39fb2b22fa8afe5a`: *"Consider now the pairs of sets of formulas ⟨X, Y⟩ such that
  Υ ⊆ X, Φ ⊆ Y, Γ ⊆ Y, ... ϕ ∉ X ∪ Y"*) — confirming the empty-poset risk the plan flags (if `ϕ`
  is ever forced into `Y` by `Γ ⊆ Y`, no pair satisfies the invariant).

Both defects hold as stated. No correction to the plan's characterization is needed.

## The designated-formula-exclusion swap: what is free, and what is NOT

The plan's Phase 8 background predicts: *"the one-sided `set_maximal_is_prime` delivers component
primeness directly when the pair order is projected onto one component with the other held
fixed — the expected answer is yes, and if so this phase is largely a mapping exercise, not new
mathematics."* This probe checks that prediction directly. The verdict is mixed:

**What IS a free mapping exercise** (proved below, sorry-free):
1. The pair poset `cs5PairPoset` (designated-formula exclusion `□A ∉ X`, `A ∉ Y`, cross-conditions
   `boxInv X ⊆ Y`, `boxInv Y ⊆ X`, seeded at `H ⊆ X`) is well-defined and its **seed pair**
   `(H, cl (boxInv H))` lies in it whenever `□A ∉ H` — `cs5_pair_seed_mem`, fixing Pacheco defect
   (c) (his seed is merely asserted). The proof needs no MP-closure/`◇`-preprocessing à la
   Pacheco's `Υ`/`Φ`: `boxInv H ⊆ H` (axiom `T`) already puts `cl (boxInv H) ⊆ H` for free
   (`H` deductively closed), and `A ∉ cl (boxInv H)` follows directly from `□A ∉ H` via
   `box_mem_of_boxed_context`.
2. The **chain-upper-bound step** (Pacheco defect (d), absent in his proof) is free:
   `boxInv`/designated-formula membership are both *pointwise* (`boxInv S := {B | □B ∈ S}`),
   so they commute with **arbitrary** unions, not merely directed ones — no "`boxInv` commutes
   with directed unions" lemma is needed. `cs5_pair_chain_union_mem` below.
3. **General order fact**: if a pair `(X, Y)` is `Maximal` in `cs5PairPoset H φX φY` (product
   order, componentwise `⊆`), then `X` is maximal among `{X' | (X', Y) ∈ cs5PairPoset H φX φY}`
   (`Y` held fixed) — `cs5_pair_maximal_component_left`. This is pure order theory (`Maximal.le_of_ge`
   applied at `(X', Y)`), needing nothing CS5-specific.

**What is NOT free — the gap this probe reports** (Phase 8's genuine finding, not anticipated by
the plan's "largely a mapping exercise" framing): step 3 gives maximality of `X` in the *slice*
`{X' | (X', Y) ∈ cs5PairPoset H φX φY}`, but invoking the library's `prime_maximal_is_prime`
(`PrimeExclusion.lean:428`) at that slice requires exhibiting it as `PrimeExcludingSupersets D Cons
S φX` for a `Cons` predicate closed under `cl_admissible_of_cons : Cons Z → Cons (cl Z)` (needed
internally by `prime_maximal_is_prime`'s own proof, which closes `insert ψ X` and must stay in the
poset). The natural candidate `Cons_Y (Z) := boxInv Z ⊆ Y` (the cross-condition, `Y` fixed) is
**not** closure-stable: `cl` only guarantees closure under the *given* axioms and MP from members
already present, and nothing in `Cons_Y`'s statement prevents `cl (insert ψ Z)` from deriving a
*new* propositionally-entailed `□B` (e.g. from `ψ` and `ψ → □B` both already admitted into `Z`)
whose witness `B` was never required to lie in `Y`. Unlike Phase 6/7's exclusion-*set* `E := {□B |
B ∉ H}` (which is stated and discharged entirely in terms of `H` itself, never needing `cl`-stability
of a *side* predicate), a `Cons`-predicate route here would need `boxInv (cl Z) ⊆ Y` to follow from
`boxInv Z ⊆ Y`, which is false in general.

**The route that repairs this** (documented, not built here — out of Phase 8's stub scope; see the
Phase 9/10 blocker in the task handoff): encode the pair as a *single* quasi-prime theory over the
doubled atom space `Atom ⊕ Atom` (tag `X`'s formulas via `Sum.inl`, `Y`'s via `Sum.inr`) under a
combined axiom system that adds the two cross-condition implications
`□(τ_L B) → (τ_R B)`/`□(τ_R B) → (τ_L B)` as *axioms* rather than as an external invariant. Then
`cl`-stability of the cross-condition is free (it is a theorem of the combined system, so any
deductively-closed superset inherits it via `MP`), and a *single* `quasi_prime_set_exclusion`-style
application (excluding `E := {τ_L (□A), τ_R A}`, a 2-element set — simpler than Phase 6/7's n-ary
box-list case, since neither exclusion element needs `Kd`/`bDia` unboxing) yields prime `T'`, whose
`τ_L`/`τ_R` preimages are the desired `H'`/`T`. This needs a new `Proposition.map`-style atom
relabeling functor and a `DerivationTree` functoriality lemma (`CS5ModalAxiom`-derivability lifts
along atom relabeling) — genuinely new infrastructure beyond a "mapping exercise", not a small
addition, and not attempted in this dispatch given Phase 10's hard time bound. -/

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-- **The box-backward pair poset.** Pairs `(X, Y)` of `CS5`-deductively-closed theories with `H`
seeded into `X`, the cross-conditions `boxInv X ⊆ Y`/`boxInv Y ⊆ X`, and the two designated-formula
exclusions `φX ∉ X`, `φY ∉ Y`. Ordered by the product order (componentwise `⊆`) inherited from
`Set (Proposition Atom) × Set (Proposition Atom)`. Deliberately **not** a bot-exclusion poset
(Pacheco's `⊥ ∉ X ∪ Y`) — see the module docstring. -/
def cs5PairPoset (H : Set (Proposition Atom)) (φX φY : Proposition Atom) :
    Set (Set (Proposition Atom) × Set (Proposition Atom)) :=
  {p | H ⊆ p.1 ∧
       Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5ModalAxiom Atom)) p.1 ∧
       Metalogic.DeductivelyClosed (modalDerivationSystem (@CS5ModalAxiom Atom)) p.2 ∧
       boxInv p.1 ⊆ p.2 ∧ boxInv p.2 ⊆ p.1 ∧
       φX ∉ p.1 ∧ φY ∉ p.2}

/-- **Seed membership, fixing Pacheco defect (c).** `(H, cl (boxInv H))` lies in the pair poset
excluding `□A`/`A` whenever `□A ∉ H`. No asserted seed, no `Υ`/`Φ` MP-closure preprocessing:
`cl (boxInv H) ⊆ H` is immediate from `boxInv H ⊆ H` (`cs5_boxInv_subset`, axiom `T`) plus `H`
already being deductively closed, and `A ∉ cl (boxInv H)` follows directly from `□A ∉ H` via
`box_mem_of_boxed_context`. -/
theorem cs5_pair_seed_mem {H : Set (Proposition Atom)}
    (hH : QuasiPrime (@CS5ModalAxiom Atom) H) {A : Proposition Atom}
    (h_not : Proposition.box A ∉ H) :
    (H, modalDeductiveClosure CS5ModalAxiom (boxInv H)) ∈
      cs5PairPoset H (Proposition.box A) A := by
  have h_cl_sub_H : modalDeductiveClosure CS5ModalAxiom (boxInv H) ⊆ H := by
    rintro φ ⟨L, hL, ⟨d⟩⟩
    exact hH.closed L φ (fun x hx => cs5_boxInv_subset hH (hL x hx)) ⟨d⟩
  refine ⟨Set.Subset.refl H, hH.closed,
    modalDeductiveClosure_closed (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ),
    modal_subset_deductive_closure _ _, ?_, h_not, ?_⟩
  · exact fun B hB => cs5_boxInv_subset hH (boxInv_mono h_cl_sub_H hB)
  · rintro ⟨L, hL, ⟨d⟩⟩
    exact h_not (box_mem_of_boxed_context (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ => .k φ ψ) hH.closed L d hL)
where
  /-- `boxInv` is monotone. Local helper (not worth exporting: `Set.preimage_mono`-style, but
  `boxInv` is not literally a `Set.preimage`). -/
  boxInv_mono {S T : Set (Proposition Atom)} (h : S ⊆ T) : boxInv S ⊆ boxInv T :=
    fun _B hB => h hB

/-- **Chain-upper-bound step, fixing Pacheco defect (d).** The componentwise union of a nonempty
`⊆`-chain of pairs in the poset stays in the poset. `boxInv`/designated-formula membership are
*pointwise* (`boxInv S := {B | □B ∈ S}`), so they commute with arbitrary (not merely directed)
unions — no extra lemma beyond `deductivelyClosed_chain_union` (already in `PrimeExclusion.lean`,
applied to each component's projected chain) is needed. -/
theorem cs5_pair_chain_union_mem {H : Set (Proposition Atom)} {φX φY : Proposition Atom}
    {C : Set (Set (Proposition Atom) × Set (Proposition Atom))}
    (hCsub : C ⊆ cs5PairPoset H φX φY)
    (hchain : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
    (⋃ p ∈ C, p.1, ⋃ p ∈ C, p.2) ∈ cs5PairPoset H φX φY := by
  obtain ⟨p₀, hp₀⟩ := hCne
  have hchain1 : IsChain (· ⊆ ·) (Prod.fst '' C) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    rcases hchain hp hq (fun h => hne (congrArg Prod.fst h)) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hchain2 : IsChain (· ⊆ ·) (Prod.snd '' C) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    rcases hchain hp hq (fun h => hne (congrArg Prod.snd h)) with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hUfst : (⋃ p ∈ C, p.1) = ⋃₀ (Prod.fst '' C) := by
    simp [Set.sUnion_image]
  have hUsnd : (⋃ p ∈ C, p.2) = ⋃₀ (Prod.snd '' C) := by
    simp [Set.sUnion_image]
  refine ⟨fun x hx => Set.mem_iUnion₂.mpr ⟨p₀, hp₀, (hCsub hp₀).1 hx⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hUfst]
    exact Metalogic.deductivelyClosed_chain_union (modalDerivationSystem (@CS5ModalAxiom Atom))
      hchain1 ⟨p₀.1, Set.mem_image_of_mem _ hp₀⟩ (fun T ⟨p, hp, hpT⟩ => hpT ▸ (hCsub hp).2.1)
  · rw [hUsnd]
    exact Metalogic.deductivelyClosed_chain_union (modalDerivationSystem (@CS5ModalAxiom Atom))
      hchain2 ⟨p₀.2, Set.mem_image_of_mem _ hp₀⟩ (fun T ⟨p, hp, hpT⟩ => hpT ▸ (hCsub hp).2.2.1)
  · intro B hB
    obtain ⟨p, hp, hBp⟩ := Set.mem_iUnion₂.mp hB
    exact Set.mem_iUnion₂.mpr ⟨p, hp, (hCsub hp).2.2.2.1 hBp⟩
  · intro B hB
    obtain ⟨p, hp, hBp⟩ := Set.mem_iUnion₂.mp hB
    exact Set.mem_iUnion₂.mpr ⟨p, hp, (hCsub hp).2.2.2.2.1 hBp⟩
  · rintro hmem
    obtain ⟨p, hp, hpmem⟩ := Set.mem_iUnion₂.mp hmem
    exact (hCsub hp).2.2.2.2.2.1 hpmem
  · rintro hmem
    obtain ⟨p, hp, hpmem⟩ := Set.mem_iUnion₂.mp hmem
    exact (hCsub hp).2.2.2.2.2.2 hpmem

/-- **General order fact (free, not CS5-specific): pair-maximality projects to component
maximality with the other side fixed.** If `(X, Y)` is maximal in the pair poset, `X` is maximal
among `{X' | (X', Y) ∈ cs5PairPoset H φX φY}` under `⊆`. Pure order theory
(`Maximal.le_of_ge` applied at `(X', Y)`, using that the pair order is componentwise `⊆`); no
CS5-specific reasoning. This is the "expected yes" half of the plan's Phase 8 prediction. -/
theorem cs5_pair_maximal_component_left {H : Set (Proposition Atom)} {φX φY : Proposition Atom}
    {X Y : Set (Proposition Atom)} (hmax : Maximal (· ∈ cs5PairPoset H φX φY) (X, Y))
    {X' : Set (Proposition Atom)} (hX' : (X', Y) ∈ cs5PairPoset H φX φY) (hsub : X ⊆ X') :
    X' ⊆ X :=
  (hmax.le_of_ge hX' ⟨hsub, Set.Subset.refl Y⟩).1

/-- **Symmetric general order fact** for the right-hand (`Y`) component. -/
theorem cs5_pair_maximal_component_right {H : Set (Proposition Atom)} {φX φY : Proposition Atom}
    {X Y : Set (Proposition Atom)} (hmax : Maximal (· ∈ cs5PairPoset H φX φY) (X, Y))
    {Y' : Set (Proposition Atom)} (hY' : (X, Y') ∈ cs5PairPoset H φX φY) (hsub : Y ⊆ Y') :
    Y' ⊆ Y :=
  (hmax.le_of_ge hY' ⟨Set.Subset.refl X, hsub⟩).2

end Cslib.Logic.Modal

#print axioms Cslib.Logic.Modal.cs5_pair_seed_mem
#print axioms Cslib.Logic.Modal.cs5_pair_chain_union_mem
#print axioms Cslib.Logic.Modal.cs5_pair_maximal_component_left
#print axioms Cslib.Logic.Modal.cs5_pair_maximal_component_right
