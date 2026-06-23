# Task 252 — Acceptance Conditions Zoo: Critic Findings

**Teammate C (Critic) | Artifact 01**
**Date**: 2026-06-23

---

## Key Findings

### Finding 1: The Piterman 2007 Reference Is Wrong for the Stated Goal

The task description states "Rabin↔parity conversion (Piterman 2007)" and the seed report
repeats this under "Rabin → Parity: O(n · k!) states, Piterman 2007." This is a category
error. Piterman 2007 ("From nondeterministic Büchi and Streett automata to deterministic
parity automata") constructs a DPA from an **NBA** (or NSA), not from a **DRA**. The paper's
input is a nondeterministic Büchi automaton; its Safra-like tree construction is what produces
the O(n·k!)-state DPA. The task scope targets DRA → DPA, which is a different (generally
easier) problem, and the correct references are Zielonka 1998 or the LAR (latest-appearance-record)
construction from Kupferman–Vardi 1998 / Löding 1999. Citing Piterman 2007 for a DRA → DPA proof
will send implementers to read the wrong construction.

### Finding 2: Muller → Rabin Is Not Polynomial on the Same State Space

The seed report claims "Muller → Rabin: Polynomial (in Muller table size)". This claim is
only true in a limited, misleading sense. On the **same state space**, the Muller acceptance
condition `infOcc ∈ {F_1,...,F_k}` expresses **equality** (`infOcc = F_i`), while Rabin
captures `infOcc ⊆ F_i ∧ infOcc ∩ F_i ≠ ∅`. These are not equivalent on the same state
space without an exponential number of pairs that "pin" each element of the complement from
appearing in infOcc. In the limit, the number of pairs needed is bounded by `k · 2^|Q|` for
a DMA with k accepting sets over Q states. In contrast:

- **Rabin → Muller** (same state space): Define `accept := {S | ∃i, S ∩ Eᵢ = ∅ ∧ S ∩ Fᵢ ≠ ∅}`.
  This is trivial and does not require finiteness.
- **Muller → Rabin** (same state space): Requires exponentially many pairs in general.

The task description conflates "language equivalence" (possibly with state blowup) with
"same-state-space conversion". If the goal is language equivalence (i.e., showing equal
expressive power), the standard route is NBA → DMA (McNaughton's theorem, already a
`proof_wanted` in CSLib) and then the reverse direction. Neither direction is polynomial
without state blowup.

### Finding 3: The Existing Automata Infrastructure Has No Finite-State Constraints on Definitions

Reading `DA/Basic.lean` directly: `DA.Buchi`, `DA.Muller`, and `DA.FinAcc` are all defined
with `{State Symbol : Type*}` — no `[Finite State]` constraint on the structure definition
itself. Constraints appear only on theorems that need them (e.g., `Buchi.toMuller_language_eq`
requires `[Finite State]`, and Landweber's theorem uses `[Fintype State] [DecidableEq State]`).

For parity acceptance, this creates a genuine semantic problem: the acceptance condition
"minimum priority occurring in infOcc is even" requires `infOcc` to be nonempty and finite.
The theorem `infOcc_nonempty` (in `Foundations/Data/OmegaSequence/InfOcc.lean`) requires
`[Finite α]`. Without `[Finite State]`, the infOcc of an infinite-state run can be **empty**
(e.g., if the state space is ℕ and each state is visited exactly once, infOcc = ∅). The task
description does not address this. The CSLib team must decide:

- **Option A**: Define `DA.Parity` with an implicit `[Finite State]` constraint, breaking
  symmetry with Buchi/Muller.
- **Option B**: Use `csInf {a.priority q | q ∈ (a.run xs).infOcc}` with the convention that
  `csInf ∅ = 0` in ℕ (even → accepts vacuously). This is technically clean but semantically
  wrong for infinite-state automata with empty infOcc.
- **Option C**: Require `[Finite State]` in the `ωAcceptor` instance only, not in the
  structure definition. This allows the structure to exist but acceptance only makes sense
  under the constraint.

The existing `Buchi.toMuller_language_eq` uses Option C implicitly — but parity needs the
finiteness **in the acceptance definition** itself, not just in theorems about it.

### Finding 4: Rabin → Parity Requires a Type That Depends on a Runtime Value

The DRA → DPA construction (whether LAR-based or Piterman-style) produces a new automaton
whose **state type depends on the number of Rabin pairs**. If a `DA.Rabin` has pairs stored
as `List (Set State × Set State)`, then `pairs.length` is a runtime `ℕ`, and the DPA state
type would be something like `State × Equiv.Perm (Fin pairs.length)`. In Lean 4, this creates
a dependent type where the output type depends on the input value.

This is not impossible (Lean 4 has dependent types), but it cannot be expressed as a simple
`def toParity (a : DA.Rabin State Symbol) : DA.Parity ??? Symbol` without the output type
being computed from `a`. The existing `Buchi.toMuller` works because both types live in the
same state space `State`. A `Rabin.toParity` conversion function would need either:

- An output type `DA.Parity (State × Equiv.Perm (Fin k)) Symbol` where `k : ℕ` is a
  parameter of the `DA.Rabin` structure (making it a dependent structure).
- Or an existential/language-level statement: `∃ (S : Type) (_ : Finite S) (da : DA.Parity S Symbol), language da = language rabinAut`.

The task description does not identify this type-level obstacle.

### Finding 5: The Proposed File Structure Has an Architectural Coupling Problem

The proposed files `DA/Rabin.lean`, `DA/Parity.lean`, `DA/Conversions.lean` place all
conversion proofs in a single `Conversions.lean`. This creates a file that imports both
`Rabin.lean` and `Parity.lean` but also potentially imports `BuchiChar.lean` (for Muller
context) and the McNaughton theorem (`IsRegular.iff_da_muller`, currently `proof_wanted`).
If Muller↔Rabin conversions depend on McNaughton (which is unproven), then `Conversions.lean`
would have `proof_wanted` statements blocked by an upstream `proof_wanted`, creating a chain
of deferred obligations.

Additionally, the `DA/` namespace currently has only conversion files that keep the same
state space (`Buchi.lean` → `BuchiChar.lean`). A `Conversions.lean` with state-blowup
constructions would be architecturally inconsistent with this pattern.

### Finding 6: Streett Acceptance Is Arguably Required for Scope Completeness

The seed report acknowledges Streett as the dual of Rabin but puts it in the "optionally"
bucket. However:

1. The Piterman 2007 paper (the cited reference) actually converts **NSA → DPA**, not DRA → DPA.
   The NSA direction requires Streett.
2. Rabin ↔ Streett duality is a one-liner (flip E and F in every pair), and formalization
   without it leaves a glaring gap.
3. Task 250 (NBA complementation) is closely related: the complement of a DRA is a DStreett
   on the same state space, which may be needed for correctness arguments.

Omitting Streett is a scope decision that should be explicit, not silent.

### Finding 7: Existing proof_wanted Obligations Are Upstream Blockers

CSLib currently has three `proof_wanted` obligations that are directly related to this task:

- `DA.Muller.dba_recognizable_implies_closedUnderSuperloops` (BuchiChar.lean:132)
- `DA.Muller.closedUnderSuperloops_implies_dba_recognizable` (BuchiChar.lean:159)
- `IsRegular.iff_da_muller` (OmegaRegularLanguage.lean:262) — McNaughton's theorem

Any formulation of "Muller language equivalence with Rabin" that relies on McNaughton's
theorem is blocked by these unproven results. The task description does not acknowledge
this dependency. If the conversions are stated as language-level theorems (not just structural
ones), they may inherit these upstream blockers.

---

## Recommended Approach

1. **Scope Reduction**: Do not attempt DRA → DPA as part of this task. The type-theoretic
   obstacles (dependent types on pair count) make this disproportionately difficult. The
   correct scope for zero-sorry completion is:
   - Define `DA.Rabin` and `DA.Parity` as structures (analogous to `DA.Muller`).
   - Prove: Rabin → Muller (same state space, trivial).
   - Prove: Parity → Rabin (same state space, k/2 pairs, requires `[Finite State]`).
   - State DRA → DPA as `proof_wanted` with the LAR/Zielonka reference.

2. **Fix the Muller → Rabin claim**: Either (a) prove language equivalence on different state
   spaces using an existential construction, or (b) replace "Muller → Rabin" with a weaker
   "Rabin → Muller" and note the asymmetry explicitly.

3. **Fix the Piterman reference**: Replace "Piterman 2007" with "Zielonka 1998" or
   "Kupferman–Vardi 1998 LAR construction" for the DRA → DPA direction.

4. **Address the Finite State constraint for Parity**: Decide on Option A or C above and
   document the deviation from the Buchi/Muller pattern.

5. **Add Streett or explicitly exclude it**: A 3-line definition and a single `language_eq`
   lemma (by flipping E and F) would be trivial to add and complete the acceptance condition
   zoo.

6. **Use the same file layout as BuchiChar.lean**: Rather than a monolithic `Conversions.lean`,
   follow the pattern of separate files per conversion direction (e.g., `RabinChar.lean`,
   `ParityChar.lean`).

---

## Evidence and Examples

### Evidence 1: DA.Muller is defined without [Finite State]

File: `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/Basic.lean`, lines 106–118:
```lean
structure Muller (State Symbol : Type*) extends DA State Symbol where
  accept : Set (Set State)

instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts (a : Muller State Symbol) (xs : ωSequence Symbol) :=
    (a.run xs).infOcc ∈ a.accept
```
No `[Finite State]` anywhere. The instance works because `infOcc` is a `Set State` and
membership in `Set (Set State)` does not require finiteness.

### Evidence 2: infOcc_finite and infOcc_nonempty both require [Finite α]

File: `/home/benjamin/Projects/cslib/Cslib/Foundations/Data/OmegaSequence/InfOcc.lean`, lines 93–108:
```lean
theorem infOcc_finite [Finite α] (xs : ωSequence α) : xs.infOcc.Finite := ...
theorem infOcc_nonempty [Finite α] (xs : ωSequence α) : xs.infOcc.Nonempty := ...
```
Both require `[Finite α]`. Without this, `infOcc xs` may be empty (consider
`xs : ωSequence ℕ` where `xs k = k`; then `infOcc xs = ∅`).

### Evidence 3: Parity acceptance requires min over infOcc, which needs finiteness

For min-even parity: `Even (csInf {a.priority q | q ∈ (a.run xs).infOcc})`. With `csInf ∅ = 0`
(Lean convention for `csInf` on `ℕ`), the automaton would spuriously accept any run on an
infinite state space where every state is visited only finitely often. This semantic issue
does not affect `DA.Muller` because membership of a set in `Set (Set State)` is well-defined
regardless of cardinality.

### Evidence 4: Buchi.toMuller follows same-state-space pattern

File: `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/DA/BuchiChar.lean`, lines 75–78:
```lean
def Buchi.toMuller (a : Buchi State Symbol) : Muller State Symbol where
  toDA := a.toDA
  accept := {S | (S ∩ a.accept).Nonempty}
```
The output type is `Muller State Symbol` — **same `State`**. This pattern cannot be
followed for `Rabin.toParity` because the output parity automaton needs a different (larger)
state space.

### Evidence 5: McNaughton's theorem is currently proof_wanted (upstream blocker)

File: `/home/benjamin/Projects/cslib/Cslib/Computability/Languages/OmegaRegularLanguage.lean`, line 262:
```lean
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p
```
Any language-level theorem of the form "every DRA language = some DMA language" that tries
to use McNaughton as a stepping stone will be blocked by this unproven result.

---

## Confidence Level

| Claim | Confidence |
|-------|-----------|
| Piterman 2007 is NBA→DPA not DRA→DPA | High — paper title and abstract are unambiguous |
| Muller→Rabin not polynomial on same state space | High — standard result from automata theory literature |
| infOcc empty for infinite State without Finite constraint | High — trivial counterexample xs k = k |
| DRA→DPA requires dependent types on pair count | High — type of Equiv.Perm (Fin k) depends on k |
| Streett duality is a one-liner | High — direct from Rabin definition by flipping sets |
| McNaughton is upstream blocker | High — confirmed proof_wanted in codebase |
| Rabin→Muller same-state-space is trivial | High — direct construction verified above |
| Parity→Rabin with k/2 pairs is provable | Medium-High — standard, but needs [Finite State] decision first |
