# Research Report: Task #252

**Task**: acceptance_conditions_zoo
**Date**: 2026-06-23
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-23T00:00:00Z

---

## Summary

- `DA.Rabin` and `DA.Parity` are entirely new to CSLib; no prior art exists in Mathlib or any Lean 4 external library. Both extend `DA` and implement `ωAcceptor`, following the exact pattern of `DA.Muller`.
- The optimal `pairs` representation for `DA.Rabin` is `Set (Set State × Set State)`, mirroring `DA.Muller.accept : Set (Set State)`, with `infOcc`-based acceptance. `DA.Parity` uses `color : State → ℕ` with `Nat.sInf`-based min-even acceptance; `[Finite State]` belongs on theorems, not the structure definition.
- **Conflict resolved (Piterman reference)**: The "Piterman 2007" citation for DRA→DPA is incorrect. Piterman 2007 converts NBA→DPA (a Safra-like construction); DRA→DPA uses the LAR construction from Kupferman-Vardi 1998 or Zielonka 1998. The `proof_wanted` stub must cite the correct references.
- **Conflict resolved (Muller↔Rabin complexity)**: Rabin→Muller is trivial on the same state space (one line). Muller→Rabin on the same state space requires exponentially many pairs and is not "polynomial" in the standard sense; the polynomial claim holds only when state blowup is permitted. For this task, only Rabin→Muller (same state space) should be fully proved; Muller→Rabin is a separate, harder direction.
- `DA.Streett` (dual of Rabin) should be included: it costs 30-50 lines, is a one-liner flip of Rabin pairs, and is required to properly motivate the Piterman/NSA context later. All four teammates agree on including it.
- The Rabin→Parity construction requires a dependent output type (`State × Equiv.Perm (Fin k)` where `k = pairs.length`) that cannot be expressed as a simple `def toParity : DA.Rabin → DA.Parity`. This must be stated as `proof_wanted` with an existential language-level formulation.
- Three upstream `proof_wanted` obligations in `BuchiChar.lean` and `OmegaRegularLanguage.lean` (McNaughton) are blockers for any Muller-language-level conversion theorems; structural conversions on the same state space are unaffected.

---

## Key Findings

### Primary Approach (from Teammate A)

**Infrastructure assessment**: The existing CSLib codebase provides exactly the right primitives. `DA.Buchi`, `DA.Muller`, `DA.FinAcc`, and the `ωAcceptor` typeclass all live in `Cslib/Computability/Automata/DA/Basic.lean`. The `infOcc` predicate and its key lemmas (`mem_infOcc`, `infOcc_finite [Finite α]`, `infOcc_nonempty [Finite α]`, `frequently_in_finite_type`) are in `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean`. The `DA.IsLoop` predicate in `BuchiChar.lean` explicitly references task 252 in its docstring as a future reuse target.

**Rabin formalization**: The recommended structure is:
```lean
structure Rabin (State Symbol : Type*) extends DA State Symbol where
  pairs : Set (Set State × Set State)
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts a xs := ∃ EF ∈ a.pairs,
    (a.run xs).infOcc ∩ EF.1 = ∅ ∧ ((a.run xs).infOcc ∩ EF.2).Nonempty
```
Using `Set (Set State × Set State)` (not `List`) mirrors the `DA.Muller.accept : Set (Set State)` design and avoids ordering concerns. The `infOcc`-based formulation keeps structural consistency with Muller acceptance.

**Parity formalization**: Use `color : State → ℕ` with `Nat.sInf`-based acceptance:
```lean
structure Parity (State Symbol : Type*) extends DA State Symbol where
  color : State → ℕ
instance : ωAcceptor (Parity State Symbol) Symbol where
  Accepts a xs := Even (Nat.sInf (a.color '' (a.run xs).infOcc))
```
`Nat.sInf ∅ = 0` (even) provides a graceful degenerate case when `State` is not `[Finite]`. The `[Finite State]` hypothesis goes on the correctness theorem (`infOcc_nonempty` requires it), not on the structure or the `ωAcceptor` instance.

**Conversions (easy direction first)**:
- `Buchi.toRabin`: 1 pair `(∅, accept)` — trivial, proof follows from `frequently_in_finite_type`
- `Rabin.toMuller`: define `accept := {S | ∃ EF ∈ a.pairs, S ∩ EF.1 = ∅ ∧ (S ∩ EF.2).Nonempty}` — immediate from definitions
- `Parity.toRabin`: k/2 pairs `(c⁻¹({2i+1}), c⁻¹({2i}))` — direct construction

**File structure** (3 new files in `Cslib/Computability/Automata/DA/`):
- `Rabin.lean` — `DA.Rabin`, `DA.Streett`, `Buchi.toRabin`, `Rabin.toMuller`
- `Parity.lean` — `DA.Parity`, `Parity.toRabin`
- `Conversions.lean` — `Rabin.toParity` (LAR construction, `proof_wanted` for correctness)

Confidence: **High** for structures and easy conversions; **Low** for Rabin→Parity proof.

---

### Alternative Approaches (from Teammate B)

**Pairs container alternatives**: Teammate B evaluated three representations — `List (Set State × Set State)`, `Finset (Set State × Set State)`, and `ι → (Set State × Set State)`. The `List` approach uses `List.Any` cleanly and supports `List.indexOf` for the Piterman pair indexing. However, after synthesis with Teammate A's `Set`-based approach, `Set (Set State × Set State)` is the preferred choice for structural parallelism with `DA.Muller`; `List` remains a valid alternative if indexed access becomes necessary for the Piterman construction.

**Parity acceptance alternative**: Teammate B proposed `Finset.min'` on `infOcc.toFinset.image coloring` as an alternative to `Nat.sInf`. Both are equivalent under `[Finite State]`; `Nat.sInf` is cleaner because it requires no `[DecidableEq State]` on the acceptance definition itself, and its `∅`-behavior is well-defined. The Critic's assessment supports `Nat.sInf` for this reason.

**Muller→Rabin via three routes**: Teammate B identified a route through Generalized Büchi (DMA → GNBA → DBA → DRA). This is significantly more complex than the direct construction and adds dead abstraction (`DA.GenBuchi`) unless independently useful. The direct route (Approach A: one Rabin pair `(Qᶜ \ Fᵢ, Fᵢ)` per accepting set) is simpler and should be preferred, but with the critical caveat from the Critic (see Conflicts section) that this requires exponentially many pairs on the same state space.

**Streett as `DA.Rabin` dual**: Teammate B confirmed the Rabin↔Streett duality theorem is a one-liner with acceptance `∀ EF ∈ a.accept, ((a.run xs).infOcc ∩ EF.2).Nonempty → ((a.run xs).infOcc ∩ EF.1).Nonempty`. Including `DA.Streett` in `Rabin.lean` adds minimal complexity.

**Mathlib filter infrastructure**: Key lemmas for proofs — `Nat.cofinite_eq_atTop`, `Finset.min'_mem`, `Finset.min'_le`, `Nat.even_or_odd`, `Filter.cofinite.limsup_set_eq` — are confirmed available in Mathlib.

Confidence: **High** for infrastructure verification; **High** for Büchi→Rabin and Parity→Rabin; **Medium** for Rabin→Parity definition.

---

### Gaps and Shortcomings (from Critic)

Teammate C (Critic) identified five substantive issues requiring resolution before implementation proceeds:

**1. Piterman 2007 reference is a category error** (Conflict 2, see resolution below). Piterman 2007 converts NBA→DPA, not DRA→DPA. The DRA→DPA construction uses the LAR (Latest-Appearance-Record) method from Kupferman–Vardi 1998 or Zielonka 1998.

**2. Muller→Rabin complexity claim is misleading** (Conflict 1, see resolution below). The claim "polynomial in Muller table size" holds only when state blowup is allowed. On the same state space, Muller→Rabin requires exponentially many pairs. The easy direction is Rabin→Muller (same state space, trivial).

**3. Parity acceptance requires `[Finite State]` in the acceptance definition itself**, not just in theorems. Without `[Finite State]`, `infOcc` can be empty (e.g., `xs : ωSequence ℕ` with `xs k = k`), causing `Nat.sInf ∅ = 0` (spurious acceptance). The recommended resolution is Option C: `[Finite State]` on the `ωAcceptor` instance, not on the structure definition. This matches `BuchiChar.lean`'s precedent.

**4. Rabin→Parity produces a type depending on a runtime value**: the output parity automaton has state type `State × Equiv.Perm (Fin k)` where `k = pairs.length`. Lean 4 supports dependent types, but the conversion cannot be expressed as `def toParity (a : DA.Rabin State Symbol) : DA.Parity ??? Symbol`. The correct formulation is either (a) a `DA.Rabin` with an explicit `k : ℕ` parameter making it `DA.Rabin k State Symbol`, or (b) a language-level existential: `∃ (S : Type) (_ : Finite S) (da : DA.Parity S Symbol), language da = language rabinAut`.

**5. Monolithic `Conversions.lean` risks an architectural coupling chain**: if Muller↔Rabin language theorems reference McNaughton (`IsRegular.iff_da_muller`, currently `proof_wanted`), the conversion file inherits the upstream blocker. Follow `BuchiChar.lean` pattern with separate `RabinChar.lean` and `ParityChar.lean` files rather than a monolithic `Conversions.lean`.

**6. Streett omission is a scope decision that should be explicit**: the Piterman 2007 paper converts NSA (Streett) → DPA, so Streett is architecturally required context. The Critic recommends explicit inclusion with a 3-line definition and a `rabin_compl_eq_streett` lemma.

Confidence: **High** on all six findings (confirmed from first principles or codebase evidence).

---

### Strategic Horizons (from Teammate D)

**Architectural placement**: Task 252 belongs entirely to `Cslib/Computability/Automata/`. There is no import path from temporal logic (`Cslib/Logics/Temporal/`) into the automata layer. Tasks 39/40 (temporal completeness) use canonical-model proofs and are architecturally isolated from task 252.

**Downstream chain**: Task 252 → Task 241 (McNaughton: `IsRegular.iff_da_muller`) → free corollaries `IsRegular.iff_da_rabin`, `IsRegular.iff_da_parity` → future μ-calculus/parity games model checking. The `proof_wanted IsRegular.iff_da_muller` in `OmegaRegularLanguage.lean` already has a stub awaiting the conversion chain.

**`IsLoop` pre-positioned**: The `DA.IsLoop` predicate in `BuchiChar.lean` carries an explicit docstring comment referencing task 252 as the intended reuse target. This is a direct architectural affordance from existing contributors.

**Scope estimate**: Three new files, roughly 400–600 lines total (comparable to `BuchiChar.lean` at ~180 lines per file). Nondeterministic variants (NA.Rabin, NA.Parity) are optional stretch goals.

**`proof_wanted` convention confirmed**: The pattern from `BuchiChar.lean` — fully proved easy conversions plus `proof_wanted` stubs for complex ones — is the correct approach for this PR. The Rabin→Parity direction and the Landweber-style characterization theorems are appropriate `proof_wanted` targets.

Confidence: **High** for architectural claims; **Medium** for μ-calculus future scope.

---

## Synthesis

### Conflicts Resolved

**Conflict 1: Muller↔Rabin direction and complexity**

- Teammate A described Muller→Rabin as "polynomial (in Muller table size)" and Rabin→Muller as "straightforward."
- Teammate C (Critic) identified that Muller→Rabin on the **same state space** requires exponentially many pairs, not polynomially many. The "polynomial" claim holds only if state blowup is permitted (a different setting). On the same state space, expressing `infOcc = Fᵢ` via Rabin pairs requires pairs for every subset constraint, which is exponential in `|Q|`.

**Resolution**: Rabin→Muller is the trivial same-state-space direction and should be the fully proved conversion in this PR. It requires only defining `accept := {S | ∃ EF ∈ a.pairs, S ∩ EF.1 = ∅ ∧ (S ∩ EF.2).Nonempty}` and is immediately correct by definition unfolding. Muller→Rabin (same state space) is hard in general and should either be omitted from the initial PR or stated as `proof_wanted` with a note about the exponential pair count. The task description's goal of "Muller↔Rabin language equivalence" is achievable via `proof_wanted` stubs for the hard directions.

The Critic's position is preferred here: it is grounded in the concrete semantics (`infOcc = S` vs. `S ∩ Eᵢ = ∅ ∧ S ∩ Fᵢ ≠ ∅`) and the standard textbook result.

**Conflict 2: Piterman 2007 reference for DRA→DPA**

- Teammates A, B, and D all cited "Piterman 2007" for the Rabin→Parity construction.
- Teammate C (Critic) identified that Piterman 2007 ("From nondeterministic Büchi and Streett automata to deterministic parity automata") converts NBA→DPA (or NSA→DPA) via a Safra-like tree construction. The input is a **nondeterministic** automaton. The paper's O(n·k!) blowup is for the determinization, not for a conversion between two already-deterministic acceptance conditions.

**Resolution**: The Critic is correct. The DRA→DPA conversion (a deterministic-to-deterministic problem) uses the LAR (Latest-Appearance-Record) construction. The canonical references are:
- Kupferman, Vardi (1998) — "Weak alternating automata are not that weak" (introduces LAR)
- Zielonka (1998) — "Infinite games on finitely coloured graphs with applications to automata on infinite trees"
- Löding (1999) — "Methods for the transformation of omega-automata: Complexity and connection to second order logic" (accessible survey)

The `proof_wanted` stub for `Rabin.toParity` must cite these references, not Piterman 2007. The O(n·k!) state count is still correct for LAR-based DRA→DPA, but the paper attribution must be fixed.

---

### Gaps Identified

**Gap 1: Dependent output type for Rabin→Parity not addressed in task description**

The task description states "Rabin→Parity conversion" as if the output type is known. In Lean 4, `def toParity (a : DA.Rabin State Symbol) : DA.Parity ??? Symbol` has an unknown output state type that depends on `a.pairs.card` (a runtime value). Teammates A and B do not address this. The Critic identifies it clearly. The implementation plan must choose between: (a) parameterizing `DA.Rabin` with an explicit `k : ℕ` field for pair count, making the output type `DA.Parity (State × Equiv.Perm (Fin k)) Symbol`; or (b) stating the theorem existentially at the language level. Option (b) is likely cleaner for an initial `proof_wanted`.

**Gap 2: `[Finite State]` placement for `DA.Parity` `ωAcceptor` instance**

Teammates A and B suggest `[Finite State]` on theorems only. The Critic points out that `Nat.sInf ∅ = 0` (even) produces spurious acceptance for infinite state spaces, which is semantically wrong for parity automata. No teammate explicitly resolves whether `[Finite State]` should go on the `ωAcceptor` instance itself. The plan should decide this before implementation: Option C (on the instance, not the structure) is recommended to avoid inconsistency with `DA.Muller`'s no-constraint structure definition while still providing correct acceptance semantics.

**Gap 3: File architecture for conversions**

Teammate D and the Critic both flag that a monolithic `Conversions.lean` may create an architecture coupling problem if Muller↔Rabin language theorems reference McNaughton. No teammate provides a specific resolution beyond "follow `BuchiChar.lean`." The plan should specify whether conversions live in `Rabin.lean`/`Parity.lean` (same-state-space conversions) and `Conversions.lean` (language-level / state-blowup conversions), or whether a `RabinChar.lean` / `ParityChar.lean` naming scheme is preferred.

**Gap 4: `@[expose]` vs. `public section` pattern**

Teammate A raises uncertainty about whether new files should use `module` / `@[expose] public section` or `public section`. This is a lint risk. The implementation agent should verify by reading `BuchiChar.lean` header directly and matching the exact pattern.

**Gap 5: No nondeterministic variants (NA.Rabin, NA.Parity)**

All teammates agree these are optional stretch goals. They are not gaps for the initial PR but are noted as natural follow-on tasks.

---

### Recommendations

1. **Define `DA.Rabin` with `pairs : Set (Set State × Set State)`** in a new `Rabin.lean`, following the exact `DA.Muller` structural pattern. Include `DA.Streett` in the same file (30-50 lines, dual acceptance predicate).

2. **Define `DA.Parity` with `color : State → ℕ` and `Nat.sInf`-based acceptance** in a new `Parity.lean`. Place `[Finite State]` on the `ωAcceptor` instance (Option C from the Critic) to avoid spurious acceptance on infinite state spaces while preserving the no-constraint structure definition.

3. **Fully prove these conversions** (same state space, no blowup):
   - `Buchi.toRabin` (1 pair, `(∅, accept)`) with `toRabin_language_eq [Finite State]`
   - `Rabin.toMuller` (define `accept` set-theoretically) with `toMuller_language_eq`
   - `Parity.toRabin` (k/2 pairs) with `toRabin_language_eq [Finite State]`
   - `Rabin.toStreett` and `Streett.toRabin` (flip E↔F, trivial) with duality theorem

4. **State `Rabin.toParity` as `proof_wanted`** with: (a) the LAR state type `State × Equiv.Perm (Fin k)` where `k` is the number of pairs; (b) the full construction definition; (c) the language inclusion theorem as `proof_wanted`; (d) references to Kupferman–Vardi 1998 and Zielonka 1998, not Piterman 2007.

5. **Use separate files per acceptance type** (`Rabin.lean`, `Parity.lean`) with same-state-space conversions co-located in each file, following the `BuchiChar.lean` model. Reserve `Conversions.lean` for cross-type conversions (e.g., `Parity.toRabin` which requires `[Finite State]`). Avoid a monolithic `Conversions.lean` that would inherit McNaughton as an upstream blocker.

6. **Add a comment in `OmegaRegularLanguage.lean`** noting that once `IsRegular.iff_da_muller` (McNaughton, task 241) is proved, `IsRegular.iff_da_rabin` and `IsRegular.iff_da_parity` follow as corollaries via the conversion chain in `Rabin.lean`/`Parity.lean`.

7. **Explicitly exclude** from this PR: NBA→DPA (Piterman determinization), NA.Rabin/NA.Parity nondeterministic variants, and `IsRegular.iff_da_rabin`/`IsRegular.iff_da_parity` (depend on task 241).

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary: structure definitions, acceptance formalizations, proof sketches | completed | high |
| B | Alternatives: representation style comparison, Mathlib infrastructure survey, conversion routes | completed | high |
| C | Critic: reference audit, complexity analysis, type-theoretic obstacles, upstream blockers | completed | high |
| D | Horizons: architectural placement, downstream chain, scope/cost estimate, `proof_wanted` strategy | completed | high |

---

## References

**CSLib source files consulted by teammates:**
- `Cslib/Computability/Automata/DA/Basic.lean` — `DA.Buchi`, `DA.Muller`, `DA.FinAcc`, `ωAcceptor` typeclass
- `Cslib/Computability/Automata/DA/BuchiChar.lean` — `DA.IsLoop`, `Buchi.toMuller`, Landweber `proof_wanted`s
- `Cslib/Computability/Automata/DA/Buchi.lean` — `buchi_eq_finAcc_omegaLim`
- `Cslib/Computability/Automata/DA/BuchiClosure.lean` — DBA closure properties
- `Cslib/Foundations/Data/OmegaSequence/InfOcc.lean` — `infOcc`, `infOcc_finite`, `infOcc_nonempty`, `frequently_in_finite_type`
- `Cslib/Computability/Languages/OmegaRegularLanguage.lean` — `proof_wanted IsRegular.iff_da_muller` (McNaughton stub)
- `Cslib/Logics/LTL/Semantics/GNBA.lean` — existing GNBA formalization (for context)
- `Cslib/Logics/LTL/ModelChecking.lean` — NBA-based model checking (parity not yet used)

**Mathlib modules identified as relevant:**
- `Mathlib.Computability.{DFA,NFA,EpsilonNFA}` — confirmed: no omega-automata in Mathlib
- `Mathlib.Order.Filter.Cofinite` — `Nat.cofinite_eq_atTop`
- `Mathlib.GroupTheory.Perm.Card` — `Fintype.card_perm`
- `Mathlib.Algebra.Ring.Parity` — `Nat.even_or_odd`
- `Mathlib.Order.Filter.Basic` — `Filter.cofinite.limsup_set_eq`

**External references for DRA→DPA (`proof_wanted`):**
- Kupferman, O. and Vardi, M. Y. (1998). Weak alternating automata are not that weak. In *ISTCS 1997 / TOCL 2001*. (LAR construction origin)
- Zielonka, W. (1998). Infinite games on finitely coloured graphs with applications to automata on infinite trees. *Theoretical Computer Science*, 200(1-2):135-183.
- Löding, C. (1999). Methods for the transformation of omega-automata: Complexity and connection to second order logic. Diploma thesis, Christian-Albrechts-Universität zu Kiel.
- Piterman, N. (2007). From nondeterministic Büchi and Streett automata to deterministic parity automata. *LICS 2006 / LMCS 2007*. (**NBA→DPA**, not DRA→DPA — do not cite for DRA→DPA.)
- Thomas, W. (1997). Languages, automata, and logic. In *Handbook of Formal Languages*, Vol. 3. (Standard survey covering Muller/Rabin/Parity equivalences.)
