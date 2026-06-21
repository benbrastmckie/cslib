# Teammate B Findings: Literature Survey and Alternative Formalization Approaches

**Task**: 236 -- Follow-up PRs from PR #649 (Buchi / omega-regular)
**Focus**: Literature sources, formalization precedents, and alternative proof approaches for GNBA-to-NBA degeneralization
**Agent**: cslib-research-agent (Teammate B -- Alternative Approaches)

---

## 1. Literature Survey

### 1.1 Primary References

#### Baier and Katoen, "Principles of Model Checking" (2008)

- **Ch. 4, Lemma 4.56**: The standard GNBA-to-NBA degeneralization construction.
  - State space: `Q' = Q x {1, ..., n}` where `n` is the number of acceptance sets
  - Transition: `(q, i) --a--> (q', j)` where `q --a--> q'` in GNBA, and `j = (i mod n) + 1` if `q in F_i`, else `j = i`
  - Acceptance: `F' = F_1 x {1}` (accept when in first acceptance set AND counter = 1)
  - **Critical design choice**: Counter cycles `1 -> 2 -> ... -> n -> 1 -> ...` with accepting value = 1 (or equivalently 0 in 0-indexed presentations)

- **Ch. 5, Def 5.37**: GNBA construction from LTL formulas using atoms as states
- **Ch. 5, Thm 5.39**: Correctness: NBA language equals LTL omega-language

The Baier-Katoen presentation is the closest match to CSLib's current construction, except:
- Baier-Katoen accepts at counter = 0 (or counter = 1 in 1-indexed form)
- CSLib accepts at counter = K (the maximum value)
- Both are mathematically equivalent; CSLib's choice avoids the "stuck counter" issue (see Section 3.2)

#### Vardi and Wolper, "An Automata-Theoretic Approach to Automatic Program Verification" (1986)

- Original paper establishing the LTL-to-NBA pipeline
- Uses a different construction than Baier-Katoen (based on Safra-style determinization)
- Less directly applicable to the CSLib formalization, but provides the theoretical foundation

### 1.2 Formalization Precedents

#### Schimpf, Merz, and Smaus (TPHOLs 2009) -- Isabelle/HOL

- **"Construction of Buchi Automata for LTL Model Checking Verified in Isabelle/HOL"**
- Published at TPHOLs 2009, LNCS vol. 5674, pp. 424-439
- Implements the algorithm by Gerth et al. (not Baier-Katoen), which produces GBA directly
- The paper focuses on the LTL-to-GBA direction; degeneralization is handled separately in the CAVA library
- PDF available at: https://members.loria.fr/SMerz/papers/tphols2009.pdf

#### AFP Entry "LTL_to_GBA" (Schimpf and Lammich, 2014)

- Archive of Formal Proofs entry: https://www.isa-afp.org/entries/LTL_to_GBA.html
- Three theory files: `LTL_to_GBA`, `LTL_to_GBA_impl`, `All_Of_LTL_to_GBA`
- Focuses on LTL -> GBA translation, not the degeneralization step
- Uses the Isabelle Refinement and Collection framework for executable code extraction
- **Key insight**: The AFP entry separates the GBA construction from the degeneralization, which is handled by the CAVA Automata Library

#### CAVA Automata Library (AFP, 2014)

- https://isa-afp.org/entries/CAVA_Automata.html
- Theory files include: `Automata`, `Digraph_Basic`, `Simulation`, `Step_Conv`, etc.
- Provides the generic automata framework used by the CAVA model checker
- The degeneralization is embedded in the full model checker pipeline (CAVA_LTL_Modelchecker AFP entry)
- **Architecture**: LTL -> GBA -> (implicit degeneralization) -> NBA -> emptiness check

#### CAVA LTL Model Checker (Esparza, Lammich, Neumann, Nipkow, Schimpf, Smaus, CAV 2013)

- "A Fully Verified Executable LTL Model Checker"
- Full pipeline from LTL to emptiness check, verified in Isabelle/HOL
- Over 4000 lines of generated ML code
- Uses Isabelle Refinement Framework for correctness proof decomposition
- **Relevant observation**: The full model checker handles degeneralization as part of the product construction with the system, not as a standalone GBA-to-NBA step

#### Brunner, Seidl, Sickert (ITP 2019) -- Isabelle/HOL

- "A Verified and Compositional Translation of LTL to Deterministic Rabin Automata"
- Uses a different pipeline: LTL -> "simple" languages -> DRA (Deterministic Rabin Automata)
- Does NOT use GBA/NBA or degeneralization at all
- Provides an alternative formalization approach that bypasses the cycling counter entirely
- https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.11

#### Jantsch and Norrish (ITP 2018) -- HOL4/CakeML

- "Verifying the LTL to Buchi Automata Translation via Very Weak Alternating Automata"
- Pipeline: LTL -> VWAA (Very Weak Alternating Automata) -> GBA -> BA
- Formalized in HOL4, compiled to verified ML via CakeML
- **Key difference from CSLib**: Goes through VWAA as intermediate step
- The GBA-to-BA step is the degeneralization; this paper does include it
- https://cakeml.org/itp18.pdf

#### Chou "AutomataTheory" (Lean 4, 2025)

- GitHub: https://github.com/ctchou/AutomataTheory
- Formalizes omega-regular languages, Buchi acceptance, McNaughton's theorem
- Does NOT include GNBA-to-NBA degeneralization
- Does NOT include LTL-to-automata translation
- Uses a different approach: proves closure properties of omega-regular languages directly
- Completed McNaughton's theorem (omega-regular iff deterministic Muller) -- September 2025

### 1.3 Literature Gap Analysis

| Aspect | Baier-Katoen | Schimpf+ (Isabelle) | CAVA (Isabelle) | Brunner+ (Isabelle) | Jantsch+ (HOL4) | Chou (Lean 4) | CSLib |
|--------|-------------|---------------------|-----------------|---------------------|-----------------|---------------|-------|
| LTL -> GBA | Ch. 5 | yes | yes | no (uses DRA) | yes (via VWAA) | no | yes |
| GBA -> NBA degeneral. | Lemma 4.56 | no (separate) | implicit | no | yes | no | yes |
| Counter cycling proof | textbook | N/A | embedded | N/A | in HOL4 | N/A | 3 sorries |
| Accept at 0 vs K | accept=1 (1-indexed) | N/A | N/A | N/A | unknown | N/A | accept=K |
| Structural induction | yes | yes | yes | N/A | yes | N/A | yes |

**No Lean 4 formalization of GNBA-to-NBA degeneralization exists anywhere.** CSLib's work is novel in this regard.

---

## 2. Alternative Formalization Approaches

### 2.1 The Acceptance Condition: accept={counter=K} vs accept={counter=0}

The standard literature (Baier-Katoen, Wikipedia) uses `accept = {counter = 0}` (or counter = 1 in 1-indexed presentations). CSLib uses `accept = {counter = K}`. Both are mathematically equivalent, but they have different proof ergonomics:

**Standard approach (accept at 0)**:
- Counter cycles `0 -> 1 -> ... -> (K-1) -> 0 -> 1 -> ...`
- Counter wraps via modular arithmetic: `j = (i + 1) mod K`
- Acceptance at counter = 0 means "completed a full cycle"
- **Proof advantage**: Counter transition is a single formula (`j = (i+1) mod K` or `j = i`)
- **Proof disadvantage**: The "stuck counter" issue -- when counter = 0 and state is NOT in acceptance set 0, the counter stays at 0, which IS the accepting value. This creates the appearance of false acceptances but is actually correct: the run must visit counter = 0 infinitely often, and between visits the counter must cycle through all values.

**CSLib approach (accept at K)**:
- Counter cycles `0 -> 1 -> ... -> K -> 0 -> 1 -> ...` (K+1 values in Fin (K+1))
- Counter at values 0..(K-1): conditional advance based on acceptance set membership
- Counter at value K: unconditional reset to 0
- Acceptance at counter = K means "just completed visiting all K acceptance sets in order"
- **Proof advantage**: Avoids the stuck-counter confusion -- counter only reaches K after genuinely visiting all acceptance sets
- **Proof advantage**: The accepting value K is distinguished from all "working" values 0..(K-1)
- **Proof disadvantage**: Requires handling the K case separately in transitions (3-way split: K=0, i<K, i=K)

**Recommendation**: CSLib's current choice of `accept = {counter = K}` is sound and arguably better for proof ergonomics. The extra case split at `i = K` is a minor inconvenience compared to the clarity of having a dedicated accepting value.

### 2.2 Counter Definition: Recursive vs Nat.rec

The current CSLib code defines `ctr` using a nested `Nat.rec` inside a `let`:

```lean
let ctr : Nat -> Fin K.succ := fun n =>
  match n with
  | 0 => ...
  | n + 1 => by exact Nat.rec ... (fun k prev => ...) (n + 1)
```

This is problematic because:
1. The `Nat.rec` inside `by exact` creates opaque terms that are hard to unfold
2. Lean cannot easily reduce `ctr (n+1)` to `step n (ctr n)` because `ctr` is defined as `fun n => match n ...` and the recursive call goes through `Nat.rec` on `n+1`, not through `ctr n`

**Alternative 1: Stream.iterate / Function.iterate**

Define `ctr` as the iteration of a step function:
```lean
def step (k : Nat) (B : Nat -> GNBAState phi) (prev : Fin K.succ) (n : Nat) : Fin K.succ := ...
let ctr := fun n => (step K B)^[n] (...initial...)
```

This does not work directly because the step function depends on the GNBA state `B n`, which varies with `n`.

**Alternative 2: Nat.rec at the top level**

Define `ctr` via `Nat.rec` directly:
```lean
let ctr : Nat -> Fin K.succ :=
  Nat.rec (motive := fun _ => Fin K.succ)
    (0 : Fin K.succ, Nat.succ_pos K)
    (fun n prev => counterStep K B n prev)
```

This is essentially what the current code does, but the ergonomics are poor for reduction lemmas.

**Alternative 3: WellFounded recursion / noncomputable def**

Extract the counter as a separate `noncomputable def` with a proper recursion equation:
```lean
noncomputable def counterSeq (phi : Formula Atom)
    (B : Nat -> GNBAState phi) : Nat -> Fin (gnbaK phi).succ
  | 0 => (0, Nat.succ_pos _)
  | n + 1 => counterStep phi B n (counterSeq phi B n)
```

Then prove the recursion equation:
```lean
lemma counterSeq_zero : counterSeq phi B 0 = (0, ...) := rfl
lemma counterSeq_succ : counterSeq phi B (n+1) = counterStep phi B n (counterSeq phi B n) := rfl
```

**Recommendation**: Alternative 3 is the cleanest approach for proof ergonomics. Extract the counter sequence and its step function as separate `noncomputable def`s with proven recursion equations. This makes the counter transition proof nearly trivial: unfold `counterSeq_succ` and match the gnbaNBA transition definition.

### 2.3 Product Automata as Alternative to Cycling Counter

Some formalizations avoid the cycling counter entirely by using a different construction:

**Simulation-based approach** (Brunner, Seidl, Sickert ITP 2019):
- Skip GBA/NBA entirely, go directly from LTL to DRA (Deterministic Rabin Automata)
- More complex construction but avoids degeneralization altogether
- Not applicable to CSLib's current architecture (CSLib has already built the GBA)

**Product automaton approach**:
- Instead of a single counter cycling through K acceptance sets, construct K copies of the GBA and chain them
- State space: Q x {1, ..., K} (same size as cycling counter)
- Copy i transitions normally until acceptance set F_i is visited, then moves to copy i+1
- Acceptance: being in copy K and visiting the acceptance condition
- **Equivalent to cycling counter** but sometimes easier to reason about because each "copy" has a fixed acceptance set to satisfy

**On-the-fly degeneralization** (Shan 2015, Hindawi):
- Track acceptance sets as part of the exploration rather than pre-constructing the product
- Not relevant for CSLib (CSLib needs the full NBA for correctness proofs, not just emptiness checking)

**Recommendation**: The cycling counter approach is standard and well-suited to CSLib's architecture. Switching to a product automaton would require rewriting the gnbaNBA definition without clear benefit.

### 2.4 Structural Induction for Soundness

The soundness proof requires showing `psi in B_i -> Satisfies v i psi` by structural induction on formulas. This is the standard approach across all formalizations examined:

- Baier-Katoen Thm 5.39: structural induction on subformulas
- Schimpf, Merz, Smaus (Isabelle): structural induction
- All Isabelle AFP entries: structural induction on the formula structure

**Alternative: Coinductive approach**

Some theoretical treatments use coinduction for omega-word properties:
- Define a bisimulation relation between NBA states and LTL satisfaction
- Show it is preserved by transitions
- Conclude language equality by coinduction

This is theoretically elegant but poorly supported in Lean 4 (Lean's coinduction support is limited compared to Isabelle/HOL). The structural induction approach is strongly preferred.

**Alternative: Well-founded induction on closure size**

Instead of structural induction on formula depth, one could use well-founded induction on the size of the closure set. This avoids potential issues with the imp case (where `imp psi bot` is not structurally smaller than `psi` when `psi` is itself an `imp`). However, the CSLib code already handles this correctly via `mem_closure_cases` which splits into three sub-cases (subformula, negation of subformula, next-until).

**Recommendation**: Structural induction on formulas, as already used in the CSLib code, is the correct approach. The existing proof (lines 986-1123) already handles all cases including the tricky `imp` case with `mem_closure_cases`. No change needed.

### 2.5 Propositional vs If-Then-Else Transition Functions

In the `gnbaNBA` definition, the counter transition uses nested `if ... then ... else`:

```lean
if h : gnbaK phi = 0 then j.val = 0
else if hi : i.val < gnbaK phi then
  if B in gnbaAcceptSet phi chi then j.val = i.val + 1
  else j = i
else j.val = 0
```

This creates propositions via `dite` (decidable if-then-else), which require `Decidable` instances.

**The Decidable instance issue**: `B in gnbaAcceptSet phi chi` is a `Prop` that may not have a decidable instance. The current code uses `open Classical` to make this work, which is fine for `noncomputable` definitions.

**Alternative: Propositional encoding**

Instead of `if B in acc then ... else ...`, encode the counter transition purely propositionally:

```lean
Tr := fun (B, i) a (B', j) =>
  gnbaTr phi B a B' /\
  ((gnbaK phi = 0 /\ j.val = 0) \/
   (i.val < gnbaK phi /\ B in gnbaAcceptSet phi chi /\ j.val = i.val + 1) \/
   (i.val < gnbaK phi /\ B not_in gnbaAcceptSet phi chi /\ j = i) \/
   (i.val = gnbaK phi /\ j.val = 0))
```

**Trade-off**:
- Propositional: no Decidable instances needed, but case splits are more verbose
- If-then-else: cleaner definition, but requires `Classical.dec` or `open Classical`

**Recommendation**: Keep the current `if-then-else` approach with `open Classical`. The `noncomputable` marker already signals that classical reasoning is used. The if-then-else structure maps directly to the textbook construction and is easier to read.

---

## 3. Analysis of the Three Sorry Markers

### 3.1 Sorry at Line 1205: Counter Transition in hss_trans

**Context**: Proving `(Formula.gnbaNBA phi).OmegaExecution ss v` where `ss n = (B n, ctr n)`.

The sorry needs to show that the counter part of the transition matches the `gnbaNBA.Tr` definition. Specifically:

```
if gnbaK phi = 0 then (ctr (n+1)).val = 0
else if (ctr n).val < gnbaK phi then
  if B n in gnbaAcceptSet phi chi_n then (ctr (n+1)).val = (ctr n).val + 1
  else ctr (n+1) = ctr n
else (ctr (n+1)).val = 0
```

**Root cause**: The `ctr` sequence is defined via `Nat.rec` but the gnbaNBA transition uses `dite` with the same conditions. The proof needs to show these are definitionally equal, but Lean cannot reduce the `Nat.rec` definition automatically.

**Solution approach**: Extract the counter step function and prove a recursion equation (Alternative 3 from Section 2.2). Then the proof becomes: unfold the recursion equation, match with the gnbaNBA transition definition.

### 3.2 Sorry at Line 1324: Counter Stays When Not in Acceptance Set

**Context**: Inside `hctr_stays`, proving that when `B (t + d')` is not in the acceptance set for `chi_m`, the counter value stays the same: `(ctr (t + d' + 1)).val = (ctr (t + d')).val`.

**Root cause**: Same as sorry 1 -- needs to unfold the counter recursion. The comment says "Needs hss_trans counter condition (blocked on hss_trans sorry)".

**This sorry is actually downstream of sorry 1**: If sorry 1 is resolved by extracting the counter step function with proven recursion equations, then this sorry reduces to applying the recursion equation and the `else` branch of the if-then-else.

### 3.3 Sorry at Line 1359: Counter Advances When in Acceptance Set

**Context**: Inside `hprogress`, proving that when `B (t + d_min)` IS in the acceptance set, the counter advances: `(ctr (t + d_min + 1)).val = m + 1`.

**Root cause**: Same as sorry 1 and 2 -- needs to unfold the counter recursion and take the `then` branch.

### 3.4 Unified Solution

All three sorries have the same root cause: the `ctr` sequence's definitional behavior cannot be easily extracted by Lean because of the `Nat.rec` / `by exact` construction.

**Recommended fix**:

1. **Extract** `counterStep` as a standalone function:
```lean
noncomputable def Formula.counterStep (phi : Formula Atom)
    (B : Nat -> GNBAState phi) (n : Nat) (prev : Fin (gnbaK phi).succ) : Fin (gnbaK phi).succ :=
  if hK : gnbaK phi = 0 then (0, by omega)
  else if hlt : prev.val < gnbaK phi then
    let chi := (untlFinset phi).toList.get (prev.val, by ...)
    if B n in gnbaAcceptSet phi chi then (prev.val + 1, by omega)
    else prev
  else (0, Nat.succ_pos _)
```

2. **Define** `counterSeq` using this step function:
```lean
noncomputable def Formula.counterSeq (phi : Formula Atom)
    (B : Nat -> GNBAState phi) : Nat -> Fin (gnbaK phi).succ
  | 0 => (0, Nat.succ_pos _)
  | n + 1 => counterStep phi B n (counterSeq phi B n)
```

3. **Prove** recursion equations:
```lean
lemma counterSeq_succ :
    counterSeq phi B (n + 1) = counterStep phi B n (counterSeq phi B n) := rfl
```

4. **Prove** the counter transition matches gnbaNBA.Tr:
```lean
lemma counterStep_matches_gnbaTr :
    counterStep phi B n prev = ... -- matches gnbaNBA's counter condition
```

With these lemmas, all three sorries reduce to applying `counterSeq_succ` and `counterStep_matches_gnbaTr`.

---

## 4. Key Findings Summary

### What the Literature Tells Us

1. **The cycling counter construction is standard and well-understood**. Baier-Katoen Lemma 4.56 is the canonical reference. No formalization has found a fundamentally different approach.

2. **No Lean 4 formalization of GNBA-to-NBA degeneralization exists**. CSLib's work is the first.

3. **Isabelle/HOL formalizations** (Schimpf+, CAVA, Brunner+) handle degeneralization either implicitly (as part of a larger pipeline) or via a separate library. None provide a standalone, pedagogically clear degeneralization proof.

4. **The HOL4/CakeML formalization** (Jantsch and Norrish 2018) is the closest precedent for a standalone GBA-to-BA step, but uses VWAA as an intermediate and is in HOL4, not Lean.

### What the Code Analysis Tells Us

5. **All three sorries have the same root cause**: inability to unfold a `Nat.rec`-defined counter sequence. Extracting the counter step function as a standalone definition with proven recursion equations resolves all three.

6. **CSLib's `accept = {counter = K}` design is sound** and arguably cleaner than the standard `accept = {counter = 0}` for proof purposes, because the accepting value is distinguished from all working values.

7. **The soundness direction (lines 810-1127) is already complete** -- no sorries. Only the completeness direction has sorries, and those are purely about the counter sequence definition, not about the mathematical content of the proof.

8. **The existing proof structure is correct** and follows the standard literature approach. No architectural changes are needed -- only a technical fix to the counter sequence definition.

---

## 5. Recommended Approach

**Confidence Level**: HIGH

The recommended approach is:

1. **Extract** `counterStep` and `counterSeq` as standalone noncomputable definitions outside the proof (or as `let`-bindings with explicit recursion equations)
2. **Prove** the recursion equation `counterSeq_succ` (should be `rfl`)
3. **Prove** the matching lemma showing `counterStep` produces values consistent with `gnbaNBA.Tr`'s counter condition
4. **Apply** these lemmas to discharge all three sorries

**Estimated effort**: 30-60 lines of new code (definitions + recursion equations + matching lemmas), replacing the current `let ctr` block and the three sorries.

**Risk**: LOW. The mathematical content is correct; this is purely a Lean definitional equality / reduction issue.

---

## Sources

- [Baier and Katoen, Principles of Model Checking (2008)](https://mitpress.mit.edu/9780262026499/principles-of-model-checking/)
- [Schimpf, Merz, Smaus (TPHOLs 2009)](https://inria.hal.science/inria-00408950)
- [AFP LTL_to_GBA (Schimpf, Lammich 2014)](https://www.isa-afp.org/entries/LTL_to_GBA.html)
- [CAVA Automata Library (AFP)](https://isa-afp.org/entries/CAVA_Automata.html)
- [CAVA LTL Model Checker (Esparza+ CAV 2013)](https://www21.in.tum.de/~nipkow/pubs/cav13.html)
- [Brunner, Seidl, Sickert (ITP 2019)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.11)
- [Jantsch, Norrish (ITP 2018)](https://cakeml.org/itp18.pdf)
- [Chou, AutomataTheory (Lean 4)](https://github.com/ctchou/AutomataTheory)
- [Wikipedia: Generalized Buchi automaton](https://en.wikipedia.org/wiki/Generalized_B%C3%BCchi_automaton)
- [Wikipedia: Buchi automaton](https://en.wikipedia.org/wiki/B%C3%BCchi_automaton)
- [Shan (2015), Degeneralization Algorithm for GBA](https://www.hindawi.com/journals/jam/2015/516104/)
