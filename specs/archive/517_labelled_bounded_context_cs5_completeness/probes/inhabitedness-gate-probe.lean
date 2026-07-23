import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

/-! # Task 517 Phase 2 — INHABITEDNESS GATE

**Objective** (plan `11_tprime-repair-cs5-completeness.md`, Phase 2): before any Zorn/proof
dispatch, confirm the Phase-1-repaired `TPrime` clears the inhabitedness gate. This file re-runs
both emptiness drivers from `prime-lemma-blockers.lean` (clause 1) and
`rchi-internalization-gate.lean` (clause 0, at `TS5`) against the repaired clauses and shows,
formally, that neither fires any more — and proves the gate's minimum form (plan task 2's
sanctioned alternative to a full explicit construction): the shared conclusion both drivers
relied on, `G.X = Set.univ`, is unreachable from the repaired clauses.

## Why a full explicit inhabitant is NOT attempted here

Every candidate is either immediately blocked or requires machinery out of scope for a gate
check:

- **`Γ = ∅`, any nonempty `G.X`.** `NIK.imp_self` (`prime-lemma-blockers.lean:70-74`) derives
  `x ∶ A⊃A` at **every** label, from **every** `Γ`, with **zero** premises. `Graph.X` is
  structurally required nonempty (`Graph.nonempty`), so pick any `x₀ ∈ G.X`: `deductiveClosure`
  (now relativized, but still firing at `x₀` since `x₀ ∈ G.X` by choice) forces
  `(x₀ ∶ A⊃A) ∈ Γ` for **every** proposition `A`. `Γ = ∅` fails clause 1 immediately.
- **`Γ` = the full consistent theory at a single node `x₀` (trivial graph).** This is the actual
  mathematical content of Simpson's Prime Lemma 5.3.1 (Phase 4, Zorn over whole contexts) --
  proving `Γ` is simultaneously deductively closed (clause 1) *and* consistent (clause 2)
  requires either the Zorn maximalisation itself, or a substitution/cut-admissibility lemma for
  `NIK` (showing derivability from `Γ`-as-assumptions collapses to derivability from `∅`) that is
  not established anywhere in this development and is significant, independent meta-theory (on
  the order of Phase 3's reflection lemma, not a Phase-2 gate check).

Per the plan's own hedge ("if a genuine construction is premature here, prove the weaker 'no
emptiness chain survives the repair' as the minimum gate"), this file takes that route.

## Provenance

Re-running, against `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Context.lean`'s landed
(task 517 Phase 1) repair:
- `probes/prime-lemma-blockers.lean`'s `tPrime_false` / `instIsEmptyTPrime` (driver 1, clause 1).
- `probes/rchi-internalization-gate.lean`'s `tPrime_TS5_false` (driver 2, clause 0, at `TS5`).
-/

namespace Cslib.Logic.Modal.Labelled

universe u
variable {Atom : Type u} {𝒯 : Set GeomAxiom}

/-! ## The fact that blocks both drivers -/

/-- **The single fact that defeats both known emptiness drivers.** Every `TPrime` carries a
`coinfinite` witness `V'` together with a fresh prefix `n ∉ V'` (existence: `Coinfinite.nonempty`
on the complement); the associated label `Label.var n` is, provably, never a member of `G.X`.
This is exactly the label both old drivers instantiated their (now-relativized) clause at. -/
theorem freshWitness_notMem_GX (P : TPrime 𝒯 Atom) : ∃ n : PrefixVar, Label.var n ∉ P.G.X := by
  obtain ⟨V', hV', hX⟩ := P.coinfinite
  obtain ⟨n, hn⟩ := hV'.nonempty
  exact ⟨n, fun hmem => hn (hX _ hmem)⟩

/-! ## Driver 1 (clause 1 / `deductiveClosure`) no longer fires -/

/-- **`tPrime_false`'s chain, replayed.** The old proof (`prime-lemma-blockers.lean:92-96`)
applied the *type-wide* `P.deductiveClosure (Label.var n) (.imp .bot .bot) (Deriv.imp_self _ _)`
with no membership obligation at all -- the type-wide clause took a label and a derivation, full
stop. The repaired clause is `∀ x ∈ G.X, ∀ A, Deriv 𝒯 G Γ (x ∶ A) → (x ∶ A) ∈ Γ`: a term of type
`Label.var n ∈ P.G.X` is now a *required first argument*, supplied before the derivation. Driver
1's own witness `n` (fresh: `n ∉ V'`) is exactly the label `freshWitness_notMem_GX` shows is
**not** in `P.G.X` -- so the very first argument `P.deductiveClosure` now demands cannot be
constructed for this `n`. The old chain has no successor step here: it is blocked at its first
application, not merely left with an unclosed goal further down. -/
theorem driver1_blocked (P : TPrime 𝒯 Atom) :
    ∃ n : PrefixVar, ¬ ∃ _ : Label.var n ∈ P.G.X, True :=
  let ⟨n, hn⟩ := freshWitness_notMem_GX P
  ⟨n, fun ⟨hmem, _⟩ => hn hmem⟩

/-! ## Driver 2 (clause 0 / `clModel`, at `TS5`) no longer fires -/

/-- **`tPrime_TS5_false`'s chain, replayed.** The old proof (`rchi-internalization-gate.lean:
278-283`) applied the *type-wide* `P.clModel GeomAxiom.T GeomAxiom.T_mem_TS5 (Label.var n)` to
get `P.G.R (Label.var n) (Label.var n)` unconditionally, then chased `Graph.edge_mem` to *derive*
membership `Label.var n ∈ P.G.X` from that reflexive edge. The repaired clause 0 is
`ClassicalModelOn TS5 P.G.X P.G.R`, whose `T`-component unfolds (`GeomAxiom.HoldsOn`) to
`∀ x ∈ P.G.X, P.G.R x x` -- membership is now a *hypothesis* `clModel` needs, not a fact it can
be made to yield. The chain's very first step (obtaining the reflexive edge at the fresh witness)
needs `Label.var n ∈ P.G.X` as an input it cannot supply, by the same `freshWitness_notMem_GX`
fact driver 1 uses. -/
theorem driver2_blocked (P : TPrime TS5 Atom) :
    ∃ n : PrefixVar, ¬ ∃ _ : Label.var n ∈ P.G.X, True :=
  driver1_blocked P

/-! ## The gate: the shared conclusion both drivers relied on is unreachable -/

/-- **Minimum inhabitedness gate (plan task 2, weaker form).** Both `tPrime_false` and
`tPrime_TS5_false` derived their contradiction by first reaching `G.X = Set.univ` (driver 1: from
type-wide `deductiveClosure` forcing membership for *every* label; driver 2: from type-wide
`clModel .T` forcing a reflexive edge, hence membership, at *every* label) and *then* chasing
`coinfinite` for the final contradiction. This theorem shows that shared conclusion is now
unreachable **for every `𝒯`, not merely the two instances above**: `P.G.X = Set.univ` directly
contradicts `freshWitness_notMem_GX`, independently of which relativized clause one might try to
push through to reach it. No chain of this shape -- reach `G.X = univ`, then contradict
`coinfinite` -- can succeed against the repaired `TPrime`, at any `𝒯`. -/
theorem TPrime.gx_ne_univ (P : TPrime 𝒯 Atom) : P.G.X ≠ Set.univ := by
  intro hcontra
  obtain ⟨n, hn⟩ := freshWitness_notMem_GX P
  exact hn (hcontra ▸ Set.mem_univ _)

end Cslib.Logic.Modal.Labelled

section Verification
open Cslib.Logic.Modal.Labelled
#print axioms Cslib.Logic.Modal.Labelled.freshWitness_notMem_GX
#print axioms Cslib.Logic.Modal.Labelled.driver1_blocked
#print axioms Cslib.Logic.Modal.Labelled.driver2_blocked
#print axioms Cslib.Logic.Modal.Labelled.TPrime.gx_ne_univ
end Verification
