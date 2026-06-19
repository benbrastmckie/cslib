# Implementation Plan: Task #236 -- GNBA Tableau Construction

- **Task**: 236 - Complete follow-up PRs from PR #649 for Buchi automata and closure of omega-regular languages under boolean operations
- **Status**: [IMPLEMENTING]
- **Effort**: 30 hours
- **Dependencies**: None (Phases 1-2 from prior plan complete; OmegaRegular.lean exists with atom/bot/imp/next proved)
- **Research Inputs**: specs/236_follow_up_prs_buchi_omega_regular/reports/03_gnba-tableau-research.md
- **Artifacts**: plans/03_gnba-tableau-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This plan implements the standard GNBA (Generalized Nondeterministic Buchi Automaton) tableau construction for LTL formulas, following Baier-Katoen Chapter 5 / Vardi-Wolper 1986. The construction defines Fischer-Ladner closure, atoms (maximally consistent subsets), the GNBA transition relation with acceptance sets per Until subformula, GNBA-to-NBA conversion via cycling counter, and the correctness theorem equating GNBA language with LTL satisfaction semantics. This replaces the blocked structural induction approach (prior plan Phase 3b) with a self-contained global construction. The final deliverable removes the `sorry` in `Formula.isRegular` by proving `Formula.isRegular_untl` via the GNBA construction.

### Research Integration

Report `03_gnba-tableau-research.md` provides the complete mathematical specification:
- Fischer-Ladner closure definition adapted for CSLib's `neg = imp _ bot` convention (Option B: include both `psi` and `imp psi bot`, no double-negation in closure)
- Atom predicate with four consistency conditions (propositional, bot, imp, until local)
- GNBA definition with transition relation (letter consistency, next-step consistency, until expansion) and acceptance sets
- GNBA-to-NBA cycling counter construction with `Fin k` state component
- Correctness proof structure: completeness via canonical atoms `{ psi in cl(phi) | Satisfies v i psi }`, soundness via structural induction on subformulas with acceptance condition for Until
- Adversarial self-verification confirms feasibility (7 challenges verified, no fundamental flaws)

### Prior Plan Reference

Plan `02_untl-case-plan.md` (v02) established:
- Phases 1-2 completed (LTL/Temporal decoupling, OmegaExecution bridge)
- Phase 3a completed (`omegaLanguage_untl` semantic equation proved)
- Phase 3b BLOCKED: direct NBA construction for `untl` case cannot verify guard acceptance at multiple positions. All four local approaches (direct NBA, subset tracking, GNBA with toggle, fixed-point) share this fundamental difficulty. The GNBA global construction resolves it by encoding formula satisfaction directly in the state space.
- Effort calibration: semantic equation took ~2 hours; NBA constructions with language equality (atom, next) took ~1-2 hours each for simple cases. The GNBA construction is substantially more complex.

### Roadmap Alignment

No ROADMAP.md items directly reference the GNBA construction. This task advances the general LTL omega-regularity theorem which supports the broader omega-regular language infrastructure.

## Goals & Non-Goals

**Goals**:
- Define `Formula.closure` (Fischer-Ladner closure) adapted for CSLib's `neg = imp _ bot`
- Define `Formula.IsAtom` (maximally consistent subsets of closure)
- Construct the GNBA for any LTL formula with transition relation and acceptance sets
- Convert GNBA to NBA via cycling counter construction
- Prove `gnba_language_eq`: the GNBA/NBA language equals `Formula.omegaLanguage`
- Prove `Formula.isRegular_untl` and remove the `sorry` from `Formula.isRegular`
- Preserve all existing per-constructor lemmas (atomNBA, nextNBA, isRegular_atom, etc.)

**Non-Goals**:
- McNaughton's theorem (`IsRegular.iff_da_muller`) -- separate task
- Optimizing GNBA state space (correctness over minimality)
- On-the-fly GNBA construction (Gerth et al. 1995 algorithm)
- Deterministic Buchi automata
- Encodable/Countable instances for `Formula`

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Closure definition has subtle edge cases with `imp _ bot` negation encoding | H | M | Research verified Option B approach; propositional consistency condition handles it directly without double-negation |
| Atoms finiteness proof is technically involved (subsets of finite set) | M | L | Use Mathlib's `Set.Finite.finite_subsets` or `Fintype (Finset alpha)` |
| Correctness proof (especially soundness Until case) is lengthy | H | H | Decompose into small lemmas; canonical atom properties as separate lemmas; acceptance argument as dedicated lemma |
| GNBA-to-NBA cycling counter introduces product state complexity | M | M | For k=0 acceptance sets, use trivial NBA; for k>=1, use direct `Fin k` counter; avoid iterating `interNA` |
| Universe polymorphism issues (`Type` vs `Type*` in `IsRegular`) | M | L | Research confirmed: when `Atom : Type`, atoms are `Type`-level; matches `IsRegular` requirement |
| Total estimated lines (920-1280) may exceed single-phase implementation scope | H | M | Decompose into 5 focused phases of 150-300 lines each; each phase independently verifiable |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Fischer-Ladner Closure and Atoms [COMPLETED]

**Goal**: Define the Fischer-Ladner closure of an LTL formula and the atom predicate (maximally consistent subset of closure), prove closure is finite and atoms are finite.

**Tasks**:
- [ ] Create new file `Cslib/Logics/LTL/Semantics/GNBA.lean` with appropriate module doc and imports
- [ ] Define `Formula.subformulas : Formula Atom -> Set (Formula Atom)` (recursive subformula set)
- [ ] Define `Formula.closure : Formula Atom -> Set (Formula Atom)` as the set containing each subformula `psi` and its negation `imp psi bot`, plus `next (untl phi1 phi2)` for each Until subformula (Fischer-Ladner closure rule 5)
- [ ] Prove `Formula.self_mem_closure : phi in phi.closure`
- [ ] Prove `Formula.closure_finite : phi.closure.Finite` (closure is finite, independent of `Atom` finiteness -- it depends only on formula structure)
- [ ] Define `Formula.IsAtom (phi : Formula Atom) (B : Set (Formula Atom)) : Prop` with the four conditions:
  1. `B` is a subset of `phi.closure`
  2. Propositional consistency: for all `psi in phi.closure`, `psi in B <-> imp psi bot not-in B`
  3. Bot consistency: `bot not-in B`
  4. Imp closure: for all `imp psi1 psi2 in phi.closure`, `imp psi1 psi2 in B <-> (psi1 not-in B \/ psi2 in B)`
  5. Until local consistency: for all `untl psi1 psi2 in phi.closure`, `(psi2 in B -> untl psi1 psi2 in B)` and `(untl psi1 psi2 in B -> psi2 not-in B -> psi1 in B)`
- [ ] Prove `Formula.atoms_finite : { B | phi.IsAtom B }.Finite` (atoms are finite because they are subsets of a finite set)
- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 6 hours

**Depends on**: none

**Files to create/modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` (new) -- closure and atom definitions with finiteness proofs

**Verification**:
- `lean_verify` on `Formula.closure_finite` and `Formula.atoms_finite` passes (no sorry)
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors

---

### Phase 2: Canonical Atoms and Semantic Properties [NOT STARTED]

**Goal**: Define canonical atoms from semantic valuations and prove they satisfy the atom predicate. This establishes the key bridge between LTL semantics and the GNBA state space.

**Tasks**:
- [ ] Define `Formula.canonicalAtom (v : N -> (Atom -> Prop)) (i : N) (phi : Formula Atom) : Set (Formula Atom)` as `{ psi in phi.closure | Satisfies v i psi }`
- [ ] Prove `Formula.canonicalAtom_isAtom : phi.IsAtom (canonicalAtom v i phi)` -- the canonical atom is indeed an atom. This requires showing all four consistency conditions hold for sets defined by semantic satisfaction:
  - Propositional consistency: `Satisfies v i psi <-> not (Satisfies v i (imp psi bot))` (follows from classical logic `not not P <-> P`)
  - Bot consistency: `not (Satisfies v i bot)` (trivial)
  - Imp closure: `Satisfies v i (imp psi1 psi2) <-> (not (Satisfies v i psi1) \/ Satisfies v i psi2)` (follows from implication semantics)
  - Until local consistency: follows from the expansion law of Until
- [ ] Prove `Formula.canonicalAtom_mem_iff : psi in canonicalAtom v i phi <-> (psi in phi.closure /\ Satisfies v i psi)` (membership characterization)
- [ ] Prove closure membership lemmas needed for GNBA transitions:
  - `atom_mem_closure_of_atom_mem` (atomic formulas in closure)
  - `next_mem_closure_of_next_mem` (next-step closure property)
  - `untl_mem_closure_of_untl_mem` (until closure properties)
- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 6 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- add canonical atom definitions and semantic property proofs

**Verification**:
- `lean_verify` on `Formula.canonicalAtom_isAtom` passes (no sorry)
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors

---

### Phase 3: GNBA Construction and NBA Conversion [NOT STARTED]

**Goal**: Define the GNBA for an LTL formula (transition relation, initial states, acceptance sets) and convert it to an NBA using the cycling counter construction. Prove the state space is finite.

**Tasks**:
- [ ] Define the GNBA state type as `{ B : Set (Formula Atom) // phi.IsAtom B }` (subtype of atoms)
- [ ] Provide `Finite` instance for the GNBA state type (via `atoms_finite`)
- [ ] Define `Formula.gnbaTr (phi : Formula Atom) : GNBAState phi -> Set Atom -> GNBAState phi -> Prop` with the three transition conditions:
  1. Letter consistency: for all atomic `p`, `atom p in B <-> p in a` (where `a : Set Atom` is the alphabet symbol)
  2. Next-step consistency: for all `next psi in closure phi`, `next psi in B <-> psi in B'`
  3. Until expansion: for all `untl psi1 psi2 in closure phi`, `untl psi1 psi2 in B <-> (psi2 in B \/ (psi1 in B /\ untl psi1 psi2 in B'))`
- [ ] Define `Formula.gnbaStart (phi : Formula Atom) : Set (GNBAState phi)` as `{ B | phi in B.val }`
- [ ] Define acceptance sets: for each `untl psi1 psi2 in closure phi`, `{ B | untl psi1 psi2 not-in B.val \/ psi2 in B.val }`
- [ ] Enumerate Until subformulas in closure to get a finite list of acceptance sets (as `Fin k -> Set (GNBAState phi)`)
- [ ] Define the GNBA-to-NBA conversion using cycling counter:
  - NBA state type: `GNBAState phi x Fin k` (or `GNBAState phi` if k=0)
  - NBA transition: `(B, i) --a--> (B', j)` where GNBA transition holds and counter advances when current acceptance set is satisfied
  - NBA acceptance: states where counter is at position 0 (or all states if k=0)
- [ ] Package as `Formula.gnbaNBA : NA.Buchi (GNBAState phi x Fin k) (Set Atom)` (the final NBA)
- [ ] Prove `Finite` for the NBA state type
- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 8 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- add GNBA definition, acceptance sets, and NBA conversion

**Verification**:
- `lean_verify` on `Formula.gnbaNBA` definition passes (no sorry in definition)
- `Finite` instance for NBA state type verified
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors

---

### Phase 4: GNBA Correctness (Language Equality) [NOT STARTED]

**Goal**: Prove that the NBA from Phase 3 accepts exactly the omega-language of the formula: `language (gnbaNBA phi) = phi.omegaLanguage`. This is the core theorem (Baier-Katoen Theorem 5.39).

**Tasks**:
- [ ] **Completeness direction** (`phi.omegaLanguage <= language (gnbaNBA phi)`):
  Given `v` satisfying `phi`, construct an accepting run using canonical atoms.
  - Define the canonical run: `B_i = canonicalAtom v i phi`
  - Show `B_0` is a start state (since `phi in B_0` and `phi in closure phi`)
  - Show transitions hold: `B_i --v(i)--> B_{i+1}` in the GNBA by verifying:
    - Letter consistency: `atom p in B_i <-> p in v(i)` (follows from `Satisfies v i (atom p) <-> p in v(i)`)
    - Next-step consistency: `next psi in B_i <-> psi in B_{i+1}` (follows from `satisfies_shift`)
    - Until expansion: follows from the expansion law `Satisfies v i (untl psi1 psi2) <-> Satisfies v i psi2 \/ (Satisfies v i psi1 /\ Satisfies v (i+1) (untl psi1 psi2))`
  - Show the run is accepting (acceptance condition for each Until subformula):
    For each `untl psi1 psi2`, show infinitely often either `untl psi1 psi2 not-in B_i` or `psi2 in B_i`.
    Proof: if `untl psi1 psi2 in B_i` for all `i >= n` (meaning `Satisfies v i (untl psi1 psi2)` for all `i >= n`), then by the Until semantics there exists `j >= n` with `Satisfies v j psi2`, so `psi2 in B_j`.
  - Lift GNBA acceptance to NBA acceptance via the cycling counter
- [ ] **Soundness direction** (`language (gnbaNBA phi) <= phi.omegaLanguage`):
  Given an accepting NBA run, show `v` satisfies `phi`.
  - Key lemma: for all `psi in closure phi` and all `i`, `psi in B_i -> Satisfies v i psi` (by structural induction on `psi`):
    - `atom p`: follows from letter consistency
    - `bot`: follows from bot consistency in atom
    - `imp psi1 psi2`: follows from imp closure in atom + IH
    - `next psi`: follows from next-step consistency + IH
    - `untl psi1 psi2`: the hardest case. If `untl psi1 psi2 in B_i`, use the acceptance condition to find `j >= i` with `psi2 in B_j`. The Until expansion ensures `psi1 in B_k` for all `k` with `i <= k < j`. By IH, `Satisfies v j psi2` and `Satisfies v k psi1` for `i <= k < j`.
  - Since `phi in B_0` (start condition) and `phi in closure phi`, we get `Satisfies v 0 phi`
  - Lift from GNBA to NBA via cycling counter language preservation
- [ ] Prove `Formula.gnba_language_eq : language (gnbaNBA phi) = phi.omegaLanguage`
- [ ] Verify: `lake build Cslib.Logics.LTL.Semantics.GNBA`

**Timing**: 8 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- add completeness/soundness proofs and language equality theorem

**Verification**:
- `lean_verify` on `Formula.gnba_language_eq` passes (no sorry)
- `lake build Cslib.Logics.LTL.Semantics.GNBA` compiles without errors

---

### Phase 5: Derive isRegular_untl and Final Integration [NOT STARTED]

**Goal**: Prove `Formula.isRegular_untl` using the GNBA construction, remove the `sorry` from `Formula.isRegular`, update imports, and run full CI verification.

**Tasks**:
- [ ] Prove `Formula.isRegular'` (via GNBA): `phi.omegaLanguage.IsRegular` for any formula `phi` with `[Finite Atom]`, by exhibiting the GNBA/NBA with finite state space and using `gnba_language_eq`
- [ ] Prove `Formula.isRegular_untl`:
  ```lean
  theorem Formula.isRegular_untl {Atom : Type} [Finite Atom] {phi psi : Formula Atom}
      (hphi : phi.omegaLanguage.IsRegular) (hpsi : psi.omegaLanguage.IsRegular) :
      (Formula.untl phi psi).omegaLanguage.IsRegular
  ```
  This can use the GNBA construction applied to `Formula.untl phi psi` directly (the hypotheses `hphi` and `hpsi` are not needed by the global GNBA approach, but the signature must match `proof_wanted`)
- [ ] In `OmegaRegular.lean`: add `import Cslib.Logics.LTL.Semantics.GNBA`
- [ ] Replace `proof_wanted Formula.isRegular_untl` with the proved theorem (either proved in GNBA.lean and imported, or proved inline)
- [ ] Replace `sorry` in `Formula.isRegular` with `exact Formula.isRegular_untl hphi hpsi`
- [ ] Update `Cslib.lean` barrel import if needed: `lake exe mk_all --module`
- [ ] Run full CI pipeline:
  - `lake build` (full project)
  - `lake test`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
- [ ] Verify `Formula.isRegular` is sorry-free: `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular`

**Timing**: 2 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` -- add import, replace proof_wanted and sorry
- `Cslib/Logics/LTL/Semantics/GNBA.lean` -- export `isRegular_untl` (if proved there)
- `Cslib.lean` -- update barrel import (via `mk_all`)

**Verification**:
- `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular_untl` passes (no sorry)
- `lean_verify` on `Cslib.Logic.LTL.Formula.isRegular` passes (no sorry, all five cases covered)
- Full CI pipeline passes: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- No `proof_wanted` or `sorry` remains in `OmegaRegular.lean`

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Semantics.GNBA` succeeds after each phase
- [ ] `lake build` (full project) succeeds after Phase 5
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lean_verify` confirms no `sorry` in `Formula.isRegular`, `Formula.isRegular_untl`, and `Formula.gnba_language_eq`
- [ ] All existing per-constructor lemmas (`isRegular_atom`, `isRegular_bot`, `isRegular_imp`, `isRegular_next`) remain intact
- [ ] `omegaLanguage_untl` semantic equation preserved and used

## Artifacts & Outputs

- `Cslib/Logics/LTL/Semantics/GNBA.lean` (new) -- Fischer-Ladner closure, atoms, GNBA construction, correctness proof
- `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` (modified) -- sorry removed, proof_wanted replaced
- `specs/236_follow_up_prs_buchi_omega_regular/plans/03_gnba-tableau-plan.md` (this file)

## Rollback/Contingency

- **Phase 1-2**: If closure or atom definitions don't compile, simplify the closure to exclude the Until expansion rule (`next (untl phi1 phi2)`) and handle it separately. The atom definition can be simplified by removing Until local consistency for an initial version.
- **Phase 3**: If GNBA-to-NBA conversion with `Fin k` counter is too complex, use the `interNA` toggle mechanism iteratively for small `k`, or keep the GNBA definition and defer the conversion.
- **Phase 4**: This is the highest-risk phase. If the full correctness proof is too large:
  - Complete the completeness direction first (easier: constructs canonical run)
  - Leave soundness direction with `sorry` and document the gap
  - The completeness direction alone suffices for `isRegular_untl` if the soundness of the canonical run construction implies the language inclusion needed
- **Phase 5**: If phases 1-4 succeed, this phase is mechanical. If they don't fully complete, keep `proof_wanted Formula.isRegular_untl` with the existing `sorry` and the partially completed GNBA infrastructure as independently valuable.
- **Overall fallback**: The existing atom/bot/imp/next proofs and `omegaLanguage_untl` semantic equation are preserved regardless. The GNBA infrastructure is independently valuable even if the final `sorry` removal is deferred.
