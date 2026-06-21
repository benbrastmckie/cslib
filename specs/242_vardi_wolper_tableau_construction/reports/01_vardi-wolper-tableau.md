# Research Report: Vardi-Wolper Tableau Construction for LTL-to-NBA Translation

## Task 242 — vardi_wolper_tableau_construction
**Session**: sess_1750430400_orchestrate
**Status**: Construction is already fully implemented and verified

---

## Executive Summary

The Vardi-Wolper tableau construction for LTL-to-NBA translation has been **fully implemented
and verified** in CSLib. The implementation lives in `Cslib/Logics/LTL/Semantics/GNBA.lean`
(1484 lines) and `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` (343 lines). All key theorems
are sorry-free and use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Recommendation**: This task should be marked **[COMPLETED]** since the implementation target
is already achieved. No further implementation work is needed.

---

## 1. Literature Analysis: Vardi-Wolper Tableau Construction

### 1.1 The Construction (Vardi-Wolper 1986 / Baier-Katoen Ch. 5)

The Vardi-Wolper tableau construction translates an LTL formula phi into a Nondeterministic
Buchi Automaton (NBA) whose omega-language equals the set of models of phi. The construction
proceeds through several steps:

**Step 1 — Fischer-Ladner Closure**: For formula phi, compute the closure `cl(phi)` containing:
- Every subformula psi of phi
- The negation of every subformula (neg psi)
- For each Until subformula `psi1 U psi2`: `next(psi1 U psi2)` (Fischer-Ladner rule)

**Step 2 — Atoms (Elementary Sets)**: An atom B is a maximally consistent subset of `cl(phi)`:
- B is a subset of cl(phi)
- For each subformula psi: exactly one of psi, neg(psi) is in B
- bot is not in B
- B respects Boolean closure for implication
- B respects local Until consistency: if `psi2 in B` then `psi1 U psi2 in B`;
  if `psi1 U psi2 in B` and `psi2 not in B` then `psi1 in B`

**Step 3 — GNBA Construction**: Build a Generalized NBA with:
- States = atoms of phi
- Initial states = atoms containing phi
- Transition: `B --a--> B'` when:
  1. Letter consistency: `atom(p) in B iff p in a`
  2. Next consistency: `next(psi) in B iff psi in B'`
  3. Until expansion: `(psi1 U psi2) in B iff (psi2 in B) or (psi1 in B and psi1 U psi2 in B')`
- Acceptance: For each Until subformula `psi1 U psi2`, an acceptance set
  `F_{psi1 U psi2} = { B | psi1 U psi2 not in B or psi2 in B }`

**Step 4 — GNBA-to-NBA Conversion**: Use the cycling counter construction
(Baier-Katoen Lemma 4.56) to convert the GNBA with K acceptance sets into a standard NBA
with state space `GNBAState x Fin(K+1)`.

**Step 5 — Correctness**: Prove `L(NBA_phi) = { w | w |= phi }` via:
- **Soundness**: Every accepting NBA run induces satisfaction of phi (structural induction on
  closure formulas)
- **Completeness**: Every satisfying omega-word induces an accepting NBA run (via the
  "canonical run" of canonical atoms)

### 1.2 Difference from GPVW On-the-Fly Variant

The GPVW algorithm (Gerth et al. 1995) is an *on-the-fly* variant that builds the LGBA
(Labeled Generalized Buchi Automaton) incrementally using a DFS-based tableau expansion.
Key differences:

| Aspect | Vardi-Wolper (Baier-Katoen) | GPVW On-the-Fly |
|--------|---------------------------|-----------------|
| State generation | All atoms generated upfront | Nodes generated on demand via DFS |
| State representation | Subsets of closure | Nodes with Old/New/Next fields |
| Labels | On transitions (input alphabet) | On states (labeling function) |
| Efficiency | Generates all 2^|cl(phi)| atoms | Only reachable states explored |
| Correctness proof | Global (all atoms at once) | Local (per-node expansion rules) |
| CSLib approach | **This one** (Baier-Katoen Ch. 5) | Not implemented |

The CSLib implementation follows the Baier-Katoen/Vardi-Wolper "all atoms upfront" approach,
which is simpler to verify formally (no need to reason about DFS termination or node merging).

---

## 2. Existing CSLib Infrastructure

### 2.1 LTL Module (`Cslib/Logics/LTL/`)

| File | Content | Status |
|------|---------|--------|
| `Syntax/Formula.lean` | LTL formula type: `atom`, `bot`, `imp`, `next`, `untl` | Complete |
| `Semantics/Satisfies.lean` | Satisfaction relation over omega-words | Complete |
| `Semantics/GNBA.lean` | Full GNBA tableau construction + correctness | Complete (1484 lines) |
| `Semantics/OmegaRegular.lean` | Omega-regularity of LTL languages | Complete (343 lines) |
| `Semantics/OmegaExecutionSatisfies.lean` | Bridge to LTS OmegaExecution | Complete |
| `Embedding.lean` | LTL-to-Temporal embedding | Complete |

### 2.2 GNBA.lean Detailed Contents

The file implements all five phases of the construction:

**Phase 1 — Closure and Atoms** (lines 66-232):
- `Formula.subformulas` — recursive subformula set
- `Formula.closure` — Fischer-Ladner closure
- `Formula.IsAtom` — atom predicate (6 conditions)
- `Formula.atoms_finite` — finiteness of atom set
- Supporting lemmas: `subformulas_finite`, `closure_finite`, downward closure, membership

**Phase 2 — Canonical Atoms** (lines 399-539):
- `Formula.canonicalAtom v i phi` — canonical atom at position i in valuation v
- `Formula.canonicalAtom_isAtom` — canonical atoms satisfy the IsAtom predicate
- `Formula.canonicalAtom_mem_iff` — membership characterization

**Phase 3 — GNBA Construction** (lines 541-694):
- `Formula.GNBAState` — state type (subtype of sets satisfying IsAtom)
- `Formula.gnbaTr` — transition relation (3 conditions)
- `Formula.gnbaStart` — initial states
- `Formula.gnbaAcceptSet` — acceptance sets for Until subformulas
- `Formula.gnbaNBA` — the NBA via cycling counter (GNBA-to-NBA conversion)
- `Formula.GNBANBAState` — product state type with cycling counter

**Phase 4 — Correctness** (lines 695-1483):
- `Formula.gnba_language_eq` — main correctness theorem
  - Soundness direction (~280 lines): NBA accepting run implies satisfaction
  - Completeness direction (~200 lines): satisfaction implies NBA accepting run
- `Formula.canonicalAtom_gnbaTr` — canonical run transitions
- Counter sequence and stepping functions

**Phase 5 — Integration** (in OmegaRegular.lean):
- `Formula.isRegular'` — direct omega-regularity via gnbaNBA
- `Formula.isRegular_untl` — Until case using GNBA construction
- `Formula.isRegular` — main theorem by structural induction

### 2.3 Automata Infrastructure (`Cslib/Computability/Automata/`)

| Module | Content | Relevance |
|--------|---------|-----------|
| `NA/Basic.lean` | NBA/Muller automata structures | Foundation for GNBA construction |
| `NA/Emptiness.lean` | NBA emptiness (Baier-Katoen Lemma 4.41) | Complete (task 248) |
| `NA/BuchiInter.lean` | NBA intersection (product + cycling) | Complete |
| `NA/BuchiEquiv.lean` | NBA reindexing equivalence | Complete |
| `NA/Prod.lean` | NA product construction | Complete |
| `NA/Sum.lean` | NA sum (union) construction | Complete |
| `NA/Concat.lean` | NA concatenation | Complete |
| `NA/Loop.lean` | NA omega-power | Complete |
| `DA/Buchi.lean` | Deterministic Buchi automata | Complete |

### 2.4 Omega-Regular Language Infrastructure

| Module | Content | Status |
|--------|---------|--------|
| `OmegaRegularLanguage.lean` | IsRegular, closure properties | Complete |
| `OmegaLanguage.lean` | Omega-language type and operations | Complete |

Key closure results already proved:
- `IsRegular.sup` — union closure
- `IsRegular.inf` — intersection closure
- `IsRegular.compl` — complement closure (via Buchi congruences)
- `IsRegular.hmul` — concatenation with regular language
- `IsRegular.omegaPow` — omega-power of regular language
- `IsRegular.eq_fin_iSup_hmul_omegaPow` — characterization theorem

### 2.5 Mathlib Resources Used

The implementation leverages several Mathlib components:
- `Mathlib.Data.Set.Finite.*` — finite set operations
- `Mathlib.Data.Fintype.Fin` — Fin type for cycling counter
- `Mathlib.SetTheory.Cardinal.NatCard` — cardinal arithmetic
- `Filter.atTop`, `Filter.frequently_atTop` — for Buchi acceptance condition

---

## 3. Verification Status

### 3.1 Axiom Check

| Theorem | Axioms | Sorry-free |
|---------|--------|------------|
| `Formula.gnba_language_eq` | propext, Classical.choice, Quot.sound | Yes |
| `Formula.isRegular` | propext, Classical.choice, Quot.sound | Yes |
| `Formula.isRegular'` | propext, Classical.choice, Quot.sound | Yes |

### 3.2 Build Status

No sorry markers exist in any LTL file. No sorry markers exist in any Automata file.
The only `proof_wanted` in the omega-regular area is `IsRegular.iff_da_muller` (McNaughton's
Theorem), which is an independent concern unrelated to this task.

---

## 4. Assessment: Is There Remaining Work?

### 4.1 What the Task Asks For

The task description is: "Implement full Vardi-Wolper tableau construction for LTL-to-NBA
translation using direct NBA construction approach."

### 4.2 What Already Exists

Every component of this task is already implemented:

1. **Fischer-Ladner closure**: `Formula.closure` with finiteness proof
2. **Atom predicate**: `Formula.IsAtom` with 6 conditions, finiteness proof
3. **Canonical atoms**: `Formula.canonicalAtom` with `canonicalAtom_isAtom`
4. **GNBA transition relation**: `Formula.gnbaTr` with 3 conditions
5. **GNBA initial/acceptance**: `Formula.gnbaStart`, `Formula.gnbaAcceptSet`
6. **GNBA-to-NBA conversion**: `Formula.gnbaNBA` via cycling counter
7. **Language correctness**: `Formula.gnba_language_eq` (both directions)
8. **Omega-regularity**: `Formula.isRegular` by structural induction

### 4.3 Potential Extensions (NOT Required by Task)

If future work were desired, possible extensions include:

- **On-the-fly variant (GPVW)**: An incremental construction that only generates reachable
  states. This would be a separate task, not part of the Vardi-Wolper tableau.
- **Decidable transition relation**: Making `gnbaTr` decidable for executable model checking.
  Currently the transition is a Prop-valued relation.
- **State space size bound**: Proving `|GNBANBAState phi| <= 2^{O(|phi|)}` explicitly.
- **McNaughton's Theorem**: `IsRegular.iff_da_muller` (already listed as `proof_wanted`).

None of these are required by the current task description.

---

## 5. Literature Proof Structure

### Source: Baier-Katoen, Principles of Model Checking, Chapter 5 / Vardi-Wolper 1986

**Main Theorem**: For every LTL formula phi over finite atoms, there exists a finite-state
NBA whose omega-language equals the set of computations satisfying phi.

**Proof Steps** (all implemented in CSLib):

1. Define subformulas and Fischer-Ladner closure of phi
   - CSLib: `Formula.subformulas`, `Formula.closure`
   - Finiteness: `Formula.closure_finite`

2. Define atoms as maximally consistent subsets of the closure
   - CSLib: `Formula.IsAtom` (6-condition structure)
   - Finiteness: `Formula.atoms_finite`

3. Construct GNBA with atoms as states
   - CSLib: `Formula.GNBAState`, `Formula.gnbaTr`, `Formula.gnbaStart`, `Formula.gnbaAcceptSet`

4. Convert GNBA to NBA via cycling counter
   - CSLib: `Formula.gnbaNBA` (Baier-Katoen Lemma 4.56)

5. Prove correctness (language equality)
   - **Soundness** (NBA run implies satisfaction):
     - Extract GNBA run and counter from NBA run
     - Show counter visits accepting value K infinitely often
     - Show each GNBA acceptance set visited infinitely often (pigeonhole on counter)
     - Prove biconditional: `psi in B_i iff Satisfies v (drop i) psi` by induction on psi
     - CSLib: Forward direction of `Formula.gnba_language_eq`

   - **Completeness** (satisfaction implies NBA run):
     - Construct canonical run: `B_i = canonicalAtom v i phi`
     - Show canonical run satisfies GNBA transitions (`canonicalAtom_gnbaTr`)
     - Show canonical run visits each acceptance set infinitely often
     - Construct cycling counter sequence and show it reaches K infinitely often
     - CSLib: Backward direction of `Formula.gnba_language_eq`

6. Integrate into omega-regularity proof
   - CSLib: `Formula.isRegular` by structural induction (all cases)

---

## 6. Conclusion and Recommendation

**The Vardi-Wolper tableau construction for LTL-to-NBA translation is fully implemented and
verified in CSLib.** All 1827 lines across GNBA.lean and OmegaRegular.lean compile without
sorry, and the key theorems (`gnba_language_eq`, `isRegular`) use only standard axioms.

**Recommendation**: Mark task 242 as **[COMPLETED]** with the following completion summary:
"The Vardi-Wolper tableau construction was already fully implemented prior to task creation.
All components (Fischer-Ladner closure, atom predicate, GNBA construction, GNBA-to-NBA
conversion, language correctness, omega-regularity) are sorry-free and verified."

---

## Appendix: Key File Paths

- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Syntax/Formula.lean` — LTL formula type
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Semantics/Satisfies.lean` — Satisfaction
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Semantics/GNBA.lean` — GNBA construction (1484 lines)
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Semantics/OmegaRegular.lean` — Omega-regularity (343 lines)
- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/NA/Basic.lean` — NBA structure
- `/home/benjamin/Projects/cslib/Cslib/Computability/Automata/NA/Emptiness.lean` — NBA emptiness
- `/home/benjamin/Projects/cslib/Cslib/Computability/Languages/OmegaRegularLanguage.lean` — IsRegular
