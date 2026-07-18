import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # Task 512 Phase 1 — Q1 GO/NO-GO GATE probe

Settles, at proof level, whether the Simpson/Došen intuitionistic-diamond box-backward
argument for `CS5`, instantiated to CSLib's **actual** `CS5ModalAxiom` set (CK+T+4+B), avoids
the classical negation-completeness move `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, when the canonical relation is made
**one-sided** (`Γ R Δ := boxInv Γ ⊆ Δ`, Simpson's `{B | □B ∈ X} ⊆ Y`) instead of the two-sided
`cs5Tail` (`boxInv H ⊆ T ∧ boxInv T ⊆ H`) that CSLib's `CS5.lean` currently bakes into worlds.

## Paper proof (Simpson Prime Lemma 3.3.2 / Canonical Model Lemma 3.3.3, instantiated)

Simpson's canonical model (corpus chunk `682e04d443e7bbd7`, `Simpson1994`) is
`B = (W, ≤, R, V)`, `W = {X | X prime}`, `X ≤ X' iff X ⊆ X'`,
`X R Y iff {B | □B ∈ X} ⊆ Y` (`V(X) = {a | a ∈ X}`) — the modal clause is **one-sided**: no
"back" clause is baked into the world/relation pair. The Canonical Model Lemma 3.3.3 proves the
truth lemma "using the prime lemma in the implication and necessity cases" (chunk
`caf3305a53065b87`); the Prime Lemma 3.3.2 (chunk `8372f27240fe345d`) is a "standard Lindenbaum
construction" — disjunction property only, **never** `A ∉ X ⟹ ¬A ∈ X`.

Instantiated to CSLib's quasi-prime theories over `CS5ModalAxiom`: the box-backward case of a
`CKForces`-style truth lemma needs, for `□A ∉ Γ` (`Γ` quasi-prime), a quasi-prime `Δ` with
`Γ R Δ` (i.e. `boxInv Γ ⊆ Δ`) and `A ∉ Δ`. CSLib **already has** exactly Simpson's Prime Lemma
for this shape: `box_refuting_theory` (`SegmentLindenbaum.lean`) extends `boxInv Γ` by
`quasi_prime_exclusion` (Lindenbaum at the trivially-true consistency predicate — admits the
exploding theory, never needs `¬A ∈ Θ`) to a quasi-prime `Δ ⊇ boxInv Γ` omitting `A`; `A` stays
out because a derivation of `A` from `boxInv Γ` would place `□A` in `Γ` by
`box_mem_of_boxed_context` (the `Kb`-rule closure lemma), contradicting `□A ∉ Γ`. **No
negation-completeness step appears anywhere in this chain**: the only saturation primitive used
is `quasi_prime_exclusion`, whose own proof (a thin wrapper around `Metalogic.prime_exclusion`
at `Cons := fun _ => True`) never invokes `A ∉ S ⟹ ¬A ∈ S` — the trivial consistency predicate
makes that move both unavailable and unnecessary (no `efq`/`Cons` bridge is needed at all).

Cross-check against Marin–Morales–Straßburger Thm 7.1/7.2 (`MarinMoralesStrassburger2021`):
Thm 7.1 gives symmetry/Euclidean as **≤-mediated klmn-incestuality**, a condition on the FRAME
(`wRᵏu ∧ wRᵐv ⟹ ∃u′ ≥ u, ∃x. u′Rˡx ∧ vRⁿx`), never a per-world back-inclusion baked into `R`
itself; Thm 7.2's soundness direction is "a semantic argument over incestuous frames using the
disjunction-property saturated sets" — again no negation-completeness. This confirms the
one-sided design is not an ad-hoc CSLib trick: it is exactly the published intuitionistic
architecture, and the incestuality condition (Phase 3/5, out of scope for this gate) is what
carries the "symmetry" content instead of a two-sided relation clause.

## Where the two-sided design (CSLib's CURRENT `cs5Tail`) actually breaks

`cs5_symmetric_tail_box_gap` (`CS5.lean:712`, already landed, axiom-free) is the adversarial
probe requested by this gate's task list: it shows that if the SAME existential is asked to
produce a `Δ` satisfying **both** `boxInv Γ ⊆ Δ` **and** `boxInv Δ ⊆ Γ` (i.e. `Δ ∈ cs5Tail Γ`,
the two-sided membership CSLib's current design requires), then for `Γ` with
`□(p ∨ □q) ∈ Γ`, `q ∉ Γ`: **every** such `Δ` contains `p` (via `Δ`'s disjunction property on
`p ∨ □q ∈ Δ` — either `p ∈ Δ` directly, or `□q ∈ Δ`, which the extra back-clause
`boxInv Δ ⊆ Γ` immediately reflects into `q ∈ Γ`, contradicting `q ∉ Γ`). So if `□p ∉ Γ` too,
NO witness at `Γ` itself can omit `p` — the construction must move to a strictly larger head
`Γ' ⊇ Γ` (containing `q`), whose `boxInv Γ'` changes in turn, forcing the simultaneous-pair
fixpoint (task 509 Phases 8-10) that ultimately re-enters Pacheco's unsound Lemma 16
negation-completeness step (`CS5.lean:108-114`) to repair.

**This confirms the one-sided route genuinely dissolves the wall, not merely relocates it**:
the two-sided existential fails to be satisfiable at `Γ` (a non-existence problem, forcing head
enlargement and eventually negation-completeness to repair); the one-sided existential is
*always* satisfiable at `Γ` directly, by `box_refuting_theory`, with no enlargement and no
back-clause to discharge. The extra back-clause — not any inherent difficulty in Lindenbaum
extension — is the exact ingredient the gap's proof needs (`hsym : boxInv T ⊆ H` is used
exactly once, to convert `□q ∈ T` into `q ∈ H`). Deleting it (this gate's one-sided design)
deletes the gap outright: `cs5_box_backward_onesided` below has no `hsym`-shaped hypothesis to
supply, and no case-split on `p ∨ □q` membership is even reachable in its proof (`box_refuting_theory`
never inspects the excluded formula's shape).

## Verdict

**GATE PASS.** `cs5_box_backward_onesided` reduces EXACTLY to `box_refuting_theory` +
`quasi_prime_exclusion`'s Lindenbaum construction, with the one-sided `Γ R Δ := boxInv Γ ⊆ Δ`
relation. No `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ` step is used or needed. `lean_goal` after applying
`box_refuting_theory` shows no goals remain (the theorem is a direct corollary, not merely a
plausible reduction) — see the implementation summary for the exact `lean_goal` transcript.
Phase 2 (discard the `CS5Combined` atom-sum scaffold) and the birelational pivot proper
(Phases 3-7) are cleared to proceed, pending human greenlight (Phase 4 touches landed task-509
soundness).
-/

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## The one-sided canonical relation (Simpson's `{B | □B ∈ X} ⊆ Y`) -/

/-- **The one-sided `CS5` canonical relation.** `Γ R Δ` iff `boxInv Γ ⊆ Δ` — Simpson's
`{B | □B ∈ X} ⊆ Y` (`Simpson1994`, chunk `682e04d443e7bbd7`), with **no** "back" clause baked
in (unlike CSLib's current two-sided `cs5Tail`, `CS5.lean:632`). Symmetry becomes a global
frame-correspondence condition (the ≤-mediated incestuality condition, Marin Thm 7.1) to be
established separately (Phase 3/5 of the pivot plan) — NOT a per-world clause here. -/
def cs5OnesidedR (Γ Δ : Set (Proposition Atom)) : Prop :=
  boxInv Γ ⊆ Δ

/-- **The Phase 1 gate substantiation: `cs5_box_backward` over the one-sided relation.**
From `□A ∉ Γ` (`Γ` quasi-prime), obtain a quasi-prime `Δ` with `Γ R Δ` and `A ∉ Δ` — the SAME
object Simpson's Prime Lemma 3.3.2 uses, and *exactly* `box_refuting_theory`'s output with no
further work. No simultaneous pair, no second (back-inclusion) clause, no enlargement of `Γ`.
This is the whole five-dispatch (task 509 Phases 8-11) blocker, dissolved. -/
theorem cs5_box_backward_onesided {Γ : Set (Proposition Atom)}
    (hΓ : QuasiPrime (@CS5ModalAxiom Atom) Γ)
    {A : Proposition Atom} (h_not : Proposition.box A ∉ Γ) :
    ∃ Δ, cs5OnesidedR Γ Δ ∧ QuasiPrime (@CS5ModalAxiom Atom) Δ ∧ A ∉ Δ := by
  obtain ⟨Δ, hsub, hΔ, hAΔ⟩ :=
    box_refuting_theory (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      (fun A B χ => .orE A B χ) (fun φ ψ => .k φ ψ) hΓ h_not
  exact ⟨Δ, hsub, hΔ, hAΔ⟩

/-! ## Adversarial check: reconstructing exactly where the two-sided condition would bite -/

/-- **Adversarial confirmation.** If box-backward instead demanded a `Δ` satisfying the
two-sided `cs5Tail`-membership shape (`boxInv Γ ⊆ Δ ∧ boxInv Δ ⊆ Γ`, CSLib's CURRENT design),
the witness can fail to exist: reproduces `cs5_symmetric_tail_box_gap`'s argument inline,
confirming (adversarially, as this gate's task list requires) the EXACT spot a two-sided
condition reintroduces difficulty — the `hsym : boxInv Δ ⊆ Γ` hypothesis is used essentially,
to convert `□q ∈ Δ` into `q ∈ Γ`. `cs5_box_backward_onesided` above supplies no such hypothesis
and needs none: its proof never inspects `A`'s shape or splits on any disjunction. -/
theorem cs5_two_sided_witness_can_fail_to_omit {Γ Δ : Set (Proposition Atom)}
    (hΔ : QuasiPrime (@CS5ModalAxiom Atom) Δ) {p q : Proposition Atom}
    (hbox : Proposition.box (p.or (Proposition.box q)) ∈ Γ)
    (hsub : boxInv Γ ⊆ Δ) (hsym : boxInv Δ ⊆ Γ) (hq : q ∉ Γ) : p ∈ Δ :=
  cs5_symmetric_tail_box_gap hΔ hbox hsub hsym hq

end Cslib.Logic.Modal
