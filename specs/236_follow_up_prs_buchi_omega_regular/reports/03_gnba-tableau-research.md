# Research Report: GNBA/Tableau Construction for LTL Omega-Regularity

**Task**: 236 -- Follow-up PRs from PR #649 (Buchi / omega-regular)
**Focus**: Standard GNBA construction to prove `Formula.isRegular_untl`
**Session**: sess_1781853529_5eda3c
**Reference Grounding Tier**: 1 (literature-backed)

---

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [VardiWolper1986] Theorem 1 | LTL -> NBA, p.337 | `Formula.isRegular` | `(φ : Formula Atom) -> φ.omegaLanguage.IsRegular` | sorry (untl case) |
| [VardiWolper1986] Def. | Closure, p.335 | `Formula.closure` | `Formula Atom -> Set (Formula Atom)` | pending |
| [VardiWolper1986] Def. | Atoms, p.335 | `Formula.IsAtom` | `Set (Formula Atom) -> Formula Atom -> Prop` | pending |
| Baier-Katoen Ch.5 | Def. 5.37 | `Formula.gnba` | `Formula Atom -> NA.Buchi ...` | pending |
| Baier-Katoen Ch.5 | Def. 5.37 transition | `gnba.Tr` | `Atom -> Set Atom -> Atom -> Prop` | pending |
| Baier-Katoen Ch.5 | Def. 5.37 acceptance | `gnba.accept` | `Set Atom` (one per Until subformula) | pending |
| Baier-Katoen Ch.5 | Thm. 5.39 | `gnba_language_eq` | `language gnba = φ.omegaLanguage` | pending |
| Baier-Katoen Ch.5 | Lem. 5.40 | GNBA-to-NBA | Uses `interNA`-like toggle | pending |
| [VardiWolper1986] Theorem 1 | untl case | `Formula.isRegular_untl` | `(untl φ ψ).omegaLanguage.IsRegular` | pending |

**BibKey verification**: `VardiWolper1986` verified in `/home/benjamin/Projects/cslib/references.bib` at line 727. Baier-Katoen not present in `references.bib` (needs addition).

---

## 1. The Standard GNBA Construction

The standard construction translating an LTL formula into a Generalized Nondeterministic
Buchi Automaton (GNBA) is well-documented in multiple sources. The definitive textbook
treatment is Baier and Katoen, "Principles of Model Checking", Chapter 5, Definition 5.37.
The original automata-theoretic approach is [VardiWolper1986]. The construction was verified
in Isabelle/HOL by Schimpf, Merz, and Smaus (2009), who formalized the Gerth et al. (1995)
on-the-fly algorithm.

### 1.1 Closure

**Definition** (Closure). For an LTL formula `phi`, the closure `cl(phi)` is the smallest
set of formulas satisfying:

1. `phi in cl(phi)`
2. If `psi in cl(phi)`, then `neg psi in cl(phi)` (identifying `neg (neg psi)` with `psi`)
3. If `imp phi1 phi2 in cl(phi)`, then `phi1, phi2 in cl(phi)`
4. If `next phi1 in cl(phi)`, then `phi1 in cl(phi)`
5. If `untl phi1 phi2 in cl(phi)`, then `phi1, phi2 in cl(phi)` AND `next (untl phi1 phi2) in cl(phi)`

The last rule is the key addition beyond simple subformulas: the Until expansion law
`phi1 U phi2 <-> phi2 \/ (phi1 /\ X(phi1 U phi2))` requires `X(phi1 U phi2)` to be in the
closure.

**Size**: `|cl(phi)| = O(|phi|)` (linear in formula size).

**CSLib adaptation**: In CSLib, `neg phi = imp phi bot`. The closure must therefore include
both `psi` and `imp psi bot` for each subformula `psi`. The identification of `neg (neg psi)`
with `psi` requires noting that `imp (imp psi bot) bot` is NOT syntactically equal to `psi`,
but is semantically equivalent. This creates a design choice:

- **Option A**: Work with sets of formulas modulo semantic equivalence.
- **Option B**: Include both `psi` and `imp psi bot` in the closure, and define consistency
  conditions that handle the relationship explicitly.
- **Option C**: Add a `neg` constructor to Formula (not recommended; changes the syntax type).

**Recommendation**: Option B. The closure includes `psi` and `imp psi bot` for each
subformula. The consistency condition requires: `psi in B <-> imp psi bot not-in B`.

### 1.2 Atoms (Elementary Sets / Maximally Consistent Subsets)

**Definition** (Atom/Elementary Set). A subset `B` of `cl(phi)` is an **atom** (or
**elementary set**) if ALL of the following hold:

1. **Propositional consistency**: For all `psi in cl(phi)`:
   - `psi in B` if and only if `imp psi bot not-in B`
   (Exactly one of `psi` and its negation is in B.)

2. **Boolean closure for imp**: For all `imp psi1 psi2 in cl(phi)`:
   - `imp psi1 psi2 in B` if and only if (`psi1 not-in B` or `psi2 in B`)
   (Classical implication semantics.)

3. **Bot consistency**:
   - `bot not-in B`

4. **Local consistency for Until**: For all `untl psi1 psi2 in cl(phi)`:
   - If `psi2 in B`, then `untl psi1 psi2 in B`
   (If the event holds now, Until is satisfied.)
   - If `untl psi1 psi2 in B` and `psi2 not-in B`, then `psi1 in B`
   (If Until holds but the event doesn't hold yet, the guard must hold now.)

The set of all atoms of `phi` is denoted `At(phi)`.

**Key property**: `At(phi)` is finite (since `cl(phi)` is finite, there are at most
`2^|cl(phi)|` subsets, and atoms are a subset of these).

### 1.3 GNBA Definition

**Definition** (GNBA for LTL formula). Given an LTL formula `phi` over atoms `Atom`,
define the GNBA `G_phi = (Q, 2^Atom, delta, Q_0, F)` where:

- **States**: `Q = At(phi)` (the atoms of phi)
- **Alphabet**: `Sigma = Set Atom` (equivalently `2^AP`)
- **Initial states**: `Q_0 = { B in At(phi) | phi in B }`
- **Transition relation**: `delta(B, a) = { B' in At(phi) | ... }` where `B --a--> B'` iff:
  1. `B` is **consistent with `a`**: for all atomic propositions `p`:
     `atom p in B <-> p in a`
  2. **Next-step consistency**: for all `next psi in cl(phi)`:
     `next psi in B <-> psi in B'`
  3. **Until expansion**: for all `untl psi1 psi2 in cl(phi)`:
     `untl psi1 psi2 in B <-> (psi2 in B \/ (psi1 in B /\ untl psi1 psi2 in B'))`

- **Acceptance sets** (one per Until subformula): For each `untl psi1 psi2 in cl(phi)`:
  `F_{psi1 U psi2} = { B in At(phi) | untl psi1 psi2 not-in B \/ psi2 in B }`

  The acceptance condition ensures that every pending Until obligation is eventually
  fulfilled: if `untl psi1 psi2 in B` persists, then infinitely often either the Until
  is discharged (`not-in B`) or the event occurs (`psi2 in B`).

### 1.4 GNBA-to-NBA Conversion

A GNBA with `k` acceptance sets `F_1, ..., F_k` is converted to an NBA by the standard
**cycling counter construction**:

- **States**: `Q' = Q x {1, ..., k}` (or `Q x Fin k`)
- **Transitions**: `(q, i) --a--> (q', j)` where `q --a--> q'` in the GNBA, and:
  - If `q in F_i`, then `j = (i mod k) + 1` (advance counter)
  - If `q not-in F_i`, then `j = i` (stay at same counter)
- **Initial states**: `Q_0' = Q_0 x {1}`
- **Acceptance set**: `F' = { (q, 1) | q in F_1 }` (accept when counter cycles back to 1)

**Special case**: If `k = 0` (no Until subformulas), the GNBA accepts all runs. The NBA
has `F' = Q'` (all states accepting).

**Special case**: If `k = 1`, no conversion is needed; the GNBA is already an NBA.

### 1.5 Correctness Theorem

**Theorem** (Baier-Katoen, Theorem 5.39). `L(G_phi) = L(phi)`, i.e., the GNBA `G_phi`
accepts exactly the omega-words satisfying `phi`.

The proof has two directions:

**Soundness** (`L(G_phi) subseteq L(phi)`): Given an accepting run `B_0 B_1 B_2 ...` of
`G_phi` on `v`, show `v` satisfies `phi`. The key step is proving by structural induction
on subformulas: for all `psi in cl(phi)` and all `i >= 0`:
  `psi in B_i <-> Satisfies v i psi`

The Until case uses the acceptance condition: if `untl psi1 psi2 in B_i` for all `i >= n`,
then some `F_{psi1 U psi2}` is visited infinitely often, so `psi2 in B_j` for some `j >= n`,
meaning the event eventually occurs.

**Completeness** (`L(phi) subseteq L(G_phi)`): Given `v` satisfying `phi`, construct an
accepting run. Define `B_i = { psi in cl(phi) | Satisfies v i psi }`. Verify:
- `B_i` is an atom (this uses the semantic properties of LTL connectives)
- `phi in B_0` (since `v` satisfies `phi`)
- `B_0 B_1 B_2 ...` is a valid run (transition conditions follow from LTL semantics)
- The run is accepting (each acceptance set is visited infinitely often)

---

## 2. Mapping to CSLib Infrastructure

### 2.1 Existing Infrastructure to Reuse

| CSLib Component | Used For | Location |
|-----------------|----------|----------|
| `NA.Buchi` | Final NBA type | `NA/Basic.lean` |
| `ωLanguage.IsRegular` | Target property | `OmegaRegularLanguage.lean` |
| `Formula.omegaLanguage` | Language definition | `OmegaRegular.lean` |
| `Satisfies` | Semantics | `Satisfies.lean` |
| `satisfies_shift` | Shift lemma | `OmegaRegular.lean` |
| `mem_omegaLanguage_drop` | Drop/shift bridge | `OmegaRegular.lean` |
| `omegaLanguage_untl` | Semantic equation for untl | `OmegaRegular.lean` |
| `ωLanguage.mem_ext` | Language equality proofs | `OmegaLanguage.lean` |
| `Formula` with `DecidableEq` | Enables set membership | `Formula.lean` |
| `Set.Finite.finite_subsets` | Atoms are finite | Mathlib |
| `Set.Finite.to_subtype` | Convert Finite set to Finite type | Mathlib |

### 2.2 CSLib BuchiInter as GNBA-to-NBA Alternative

CSLib already has the `interNA` construction in `NA/BuchiInter.lean` which intersects two
Buchi automata using a toggle-history mechanism. This construction is fundamentally the same
as the GNBA-to-NBA conversion for `k = 2` acceptance sets. For `k > 2`, iterating `interNA`
would work but would introduce unnecessary state space blowup.

**Recommendation**: For the general GNBA-to-NBA conversion with arbitrary `k`, build a
direct construction using `Fin k` as the counter type, rather than iterating `interNA`.
However, the key insight is that we do NOT need the general GNBA-to-NBA conversion at all
for the `isRegular_untl` proof, because the construction can be structured differently.

### 2.3 Why the Full GNBA Construction Is the Wrong Granularity for `isRegular_untl`

The `proof_wanted` signature is:

```lean
proof_wanted Formula.isRegular_untl {Atom : Type} [Finite Atom] {φ ψ : Formula Atom}
    (hφ : φ.omegaLanguage.IsRegular) (hψ : ψ.omegaLanguage.IsRegular) :
    (Formula.untl φ ψ).omegaLanguage.IsRegular
```

This receives NBA recognizers for `L(phi)` and `L(psi)` as **hypotheses** (via `IsRegular`).
It does NOT need to construct the GNBA for the entire formula from scratch.

The full GNBA construction builds an automaton for ANY formula `phi` directly from the formula
syntax. But `isRegular_untl` only needs the `untl` case, given that the subformula NBAs
already exist. This is the structural induction approach that the file already uses.

**Critical realization**: The GNBA construction is a GLOBAL construction (one automaton for
the entire formula). The structural induction approach is LOCAL (one step per constructor).
These are complementary, not alternatives:

- **Global GNBA**: Replaces the entire `Formula.isRegular` theorem with a single construction.
  No need for the atom/bot/imp/next cases individually.
- **Local (structural induction)**: Proves `isRegular_untl` composing existing NBAs.
  The atom/bot/imp/next cases are already proved.

### 2.4 Two Implementation Strategies

#### Strategy A: Global GNBA (replaces structural induction)

Replace the current `Formula.isRegular` proof entirely with:
1. Define `Formula.closure`
2. Define `Formula.IsAtom` (elementary set predicate)
3. Define `Formula.gnba` (the GNBA construction)
4. Prove `gnba_language_eq : language (gnba phi) = phi.omegaLanguage`
5. Show `gnba` has finite state space (atoms of a finite closure are finite)
6. Convert GNBA to NBA

**Pros**: Self-contained, follows the literature exactly, no dependency on closure operations.
**Cons**: Discards the already-proved atom/bot/imp/next cases (~300 lines). Large proof
surface (~800-1200 lines estimated). The GNBA correctness proof is substantial.

#### Strategy B: Local NBA for `untl` (completes structural induction)

Build a custom NBA for `untl phi psi` using the GIVEN NBAs for phi and psi (from `hφ` and
`hψ`). This follows the pattern of `atomNBA` and `nextNBA` already in the file.

The key challenge (identified in report 02) is that the guard condition `phi holds at each
position k < j` requires verifying that the NBA for phi ACCEPTS the suffix at each position,
not just that it has a run. The GNBA construction resolves this globally by tracking
subformula membership in atoms.

**Hybrid approach**: Use the GNBA IDEA (atoms track which formulas hold) but apply it
locally. The state space of the untl NBA encodes:
- Whether we are in "guard mode" (phi must hold, event psi not yet seen) or "event mode"
  (psi has been witnessed, now need psi's NBA to accept)
- In guard mode: track the atom corresponding to the current position (which subformulas
  of `untl phi psi` hold here)

This reduces to: the state space is `Set (Formula Atom) x Option S_psi` where `Set (Formula Atom)` ranges over atoms of `untl phi psi` (finite set).

**However**, this hybrid still requires defining atoms and proving their properties, which
is most of the work of the global construction.

### 2.5 Recommended Strategy: Global GNBA Construction

**Rationale**: The full GNBA construction is the standard, well-documented approach. Both
Isabelle/HOL formalizations (Schimpf et al. 2009 and the AFP entry LTL_to_GBA from 2014)
take this approach. A local NBA construction for the `untl` case is non-standard, harder to
verify against the literature, and still requires defining atoms and closure. The global
approach has the additional benefit of being independently valuable: it is the canonical
LTL-to-automata translation.

The already-proved cases (atom, bot, imp, next) can be PRESERVED as independent lemmas
and used as sanity checks. The main `Formula.isRegular` theorem would be reproved via
the GNBA construction instead of structural induction.

---

## 3. Detailed Lean Implementation Plan

### 3.1 New Definitions Required

```
-- 1. Closure
def Formula.closure : Formula Atom → Set (Formula Atom)

-- 2. Closure is finite
theorem Formula.closure_finite : (φ : Formula Atom) → φ.closure.Finite

-- 3. Atom predicate (elementary set)
def Formula.IsAtom (φ : Formula Atom) (B : Set (Formula Atom)) : Prop :=
  B ⊆ φ.closure ∧
  -- Propositional consistency: ψ ∈ B ↔ imp ψ bot ∉ B
  (∀ ψ ∈ φ.closure, ψ ∈ B ↔ .imp ψ .bot ∉ B) ∧
  -- Bot consistency
  .bot ∉ B ∧
  -- Imp closure: imp ψ₁ ψ₂ ∈ B ↔ (ψ₁ ∉ B ∨ ψ₂ ∈ B)
  (∀ ψ₁ ψ₂, .imp ψ₁ ψ₂ ∈ φ.closure → (.imp ψ₁ ψ₂ ∈ B ↔ (ψ₁ ∉ B ∨ ψ₂ ∈ B))) ∧
  -- Until local consistency
  (∀ ψ₁ ψ₂, .untl ψ₁ ψ₂ ∈ φ.closure →
    (ψ₂ ∈ B → .untl ψ₁ ψ₂ ∈ B) ∧
    (.untl ψ₁ ψ₂ ∈ B → ψ₂ ∉ B → ψ₁ ∈ B))

-- 4. Type of atoms
def Formula.Atoms (φ : Formula Atom) : Set (Set (Formula Atom)) :=
  { B | φ.IsAtom B }

-- 5. Atoms are finite
theorem Formula.atoms_finite (φ : Formula Atom) : φ.Atoms.Finite

-- 6. GNBA construction
-- State type: the atoms (subtype of Set (Formula Atom))
-- Since atoms are a finite subset of powerset of closure, they form a finite type
def Formula.gnbaTr (φ : Formula Atom) :
    { B // φ.IsAtom B } → Set Atom → { B // φ.IsAtom B } → Prop

def Formula.gnbaStart (φ : Formula Atom) : Set { B // φ.IsAtom B }

def Formula.gnbaAccept (φ : Formula Atom) (ψ₁ ψ₂ : Formula Atom) :
    Set { B // φ.IsAtom B }
-- One acceptance set per Until subformula in cl(φ)

-- 7. GNBA-to-NBA (cycling counter or use interNA pattern)
-- For k acceptance sets, states are { B // φ.IsAtom B } × Fin k

-- 8. Language equality
theorem Formula.gnba_language_eq (φ : Formula Atom) :
    language (gnba φ) = φ.omegaLanguage

-- 9. Main theorem (reproved)
theorem Formula.isRegular' [Finite Atom] (φ : Formula Atom) :
    φ.omegaLanguage.IsRegular
```

### 3.2 Key Proof Obligations

**P1: Atoms exist (non-empty for satisfiable formulas)**.
For the completeness direction, given `v` satisfying `phi` at position `i`, define
`B_i = { psi in cl(phi) | Satisfies v i psi }` and show it is an atom. This requires:
- Satisfies respects propositional consistency (e.g., `Satisfies v i (imp psi bot)` iff
  `not (Satisfies v i psi)`)
- Satisfies respects Until local consistency (follows from the expansion law)

**P2: Transition conditions hold for the canonical run**.
Given the canonical atoms `B_i`, show `B_i --v(i)--> B_{i+1}` in the GNBA. This requires:
- Atom letter consistency: `atom p in B_i <-> p in v(i)` (immediate from definition)
- Next-step consistency: `next psi in B_i <-> psi in B_{i+1}` (follows from `Satisfies v i (next psi) <-> Satisfies v (i+1) psi`)
- Until expansion: follows from the expansion law for Until

**P3: The acceptance condition holds for the canonical run**.
For each Until subformula `untl psi1 psi2 in cl(phi)`: show that infinitely often
either `untl psi1 psi2 not-in B_i` or `psi2 in B_i`. This follows from: if
`untl psi1 psi2 in B_i` for all `i >= n`, then the event `psi2` must eventually
occur (otherwise `psi1` would hold forever without `psi2` ever holding, contradicting
the Until semantics).

**P4: Soundness (GNBA run implies satisfaction)**.
Given an accepting run `B_0 B_1 ...`, prove `psi in B_i -> Satisfies v i psi` for all
`psi in cl(phi)` by structural induction on `psi`. The hard case is Until:
if `untl psi1 psi2 in B_i`, use the acceptance condition to find `j >= i` with
`psi2 in B_j`, then by IH `Satisfies v j psi2` and `Satisfies v k psi1` for `i <= k < j`.

### 3.3 Universe and Type Considerations

**Universe polymorphism**: `Formula Atom : Type u` when `Atom : Type u`. The closure
`cl(phi)` and atoms are subsets of `Formula Atom`, so they live in `Type u`. The GNBA
state space is a subtype of `Set (Formula Atom)`, which lives in `Type u`. The NBA state
space after GNBA-to-NBA conversion is `Atom_phi x Fin k`, still in `Type u`.

The `IsRegular` definition requires `State : Type` (universe 0). But `isRegular_iff`
provides universe polymorphism:
```
p.IsRegular ↔ ∃ (σ : Type v) (_ : Finite σ) (na : NA.Buchi σ Symbol), language na = p
```
So we need `Atom : Type` (not `Type*`) for the final theorem. This matches the existing
`proof_wanted` signature which requires `{Atom : Type}`.

**`[Finite Atom]` constraint**: The `proof_wanted` has `[Finite Atom]`. This is needed
because `Set Atom` (the alphabet) must be a valid alphabet, and the NBA acceptance requires
`Finite State`. The closure is finite regardless of `Atom`'s finiteness, but `Set Atom`
is only `Finite` when `Atom` is `Finite` (via `Set.Finite` from `Fintype Atom`). Actually,
the atoms of the GNBA do NOT depend on `Atom` being finite -- they depend only on the
formula structure. So `Finite Atom` is needed only for the `IsRegular` definition (which
requires the state type to be finite), not for the GNBA construction itself.

Wait -- the state type of the GNBA is `{ B // phi.IsAtom B }`, which is a subtype of
`Set (Formula Atom)`. Since `phi.closure` is finite (proved above, independent of `Atom`),
and atoms are subsets of `phi.closure`, the number of atoms is at most `2^|cl(phi)|`, which
is finite. So `Finite { B // phi.IsAtom B }` follows from `Formula.atoms_finite` which is
proved using `Set.Finite.finite_subsets` applied to `Formula.closure_finite`. No `[Finite Atom]`
is needed for this!

The `[Finite Atom]` constraint is needed for the `IsRegular` definition which requires
`State : Type` and `Finite State`, and for the existing `OmegaRegular.lean` infrastructure.

### 3.4 The Negation Problem (CSLib-Specific Challenge)

In CSLib, `neg phi = imp phi bot` is an abbreviation, not a constructor. This means:

1. `neg (neg phi) = imp (imp phi bot) bot` which is NOT definitionally equal to `phi`.
2. The standard closure condition "identify `neg (neg psi)` with `psi`" requires semantic
   equivalence, not syntactic equality.

**Resolution**: The consistency condition in `IsAtom` is stated as:
```
∀ ψ ∈ φ.closure, ψ ∈ B ↔ .imp ψ .bot ∉ B
```
This directly handles the negation: an atom contains `ψ` iff it does not contain `imp ψ bot`.
We do NOT need to handle double negation elimination because the closure is defined to contain
`ψ` and `imp ψ bot` for each subformula `ψ`, but NOT `imp (imp ψ bot) bot`. The atom
consistency condition ensures that exactly one of `{ψ, imp ψ bot}` is in each atom.

This means that in the proof, when we encounter `imp (imp ψ bot) bot` in the semantics,
we need to show it is semantically equivalent to `ψ` and handle the translation. This is
straightforward: `Satisfies v i (imp (imp ψ bot) bot) ↔ ¬¬(Satisfies v i ψ) ↔ Satisfies v i ψ`
by classical double negation elimination (available in Lean 4's classical logic).

### 3.5 Handling `untl` Argument Order

CSLib uses `untl guard event`:
```
| .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```
where `ψ` is the guard (first arg) and `φ` is the event (second arg).

The `proof_wanted` uses `{φ ψ : Formula Atom}` where `φ` is the guard and `ψ` is the event:
```
proof_wanted Formula.isRegular_untl {Atom : Type} [Finite Atom] {φ ψ : Formula Atom}
    (hφ : φ.omegaLanguage.IsRegular) (hψ : ψ.omegaLanguage.IsRegular) :
    (Formula.untl φ ψ).omegaLanguage.IsRegular
```

So `untl φ ψ` means: guard = `φ`, event = `ψ`. This is consistent with the standard
LTL convention `φ U ψ` where `φ` is the guard and `ψ` is the event.

In the GNBA construction, the acceptance set for `untl φ ψ` is:
```
F_{φ U ψ} = { B | untl φ ψ ∉ B ∨ ψ ∈ B }
```
(Either the Until obligation is not active, or the event has occurred.)

### 3.6 Reflexive Until (j >= i, not j > i)

CSLib uses `∃ j ≥ i, ...` which means the event can occur at `j = i` (immediately).
This is the reflexive version of Until. The guard condition `∀ k, i ≤ k → k < j → ...`
is vacuously true when `j = i`.

The GNBA construction handles this correctly: the Until local consistency condition says
"if `psi2 in B` then `untl psi1 psi2 in B`", which captures the `j = i` case (event
holds now implies Until is satisfied immediately).

---

## 4. Estimated Proof Complexity and Phasing

### Phase 1: Closure and Atoms (~150-200 lines)
- `Formula.closure` definition (already prototyped, verified it compiles)
- `Formula.closure_finite` (already prototyped, verified)
- `Formula.IsAtom` predicate
- `Formula.atoms_finite` (via `Set.Finite.finite_subsets` on `closure_finite`)
- `Formula.self_mem_closure` (formula is in its own closure)
- Various closure membership lemmas

### Phase 2: Canonical Atoms (~150-200 lines)
- `Formula.canonicalAtom v i φ` = `{ ψ ∈ cl(φ) | Satisfies v i ψ }`
- Proof that `canonicalAtom v i φ` is an atom (requires semantic properties)
- Key lemma: `canonicalAtom_mem_iff`: `ψ ∈ canonicalAtom v i φ ↔ (ψ ∈ cl(φ) ∧ Satisfies v i ψ)`

### Phase 3: GNBA Construction (~200-300 lines)
- `Formula.gnba` definition (transition, start, acceptance sets)
- Transition relation definition with the three conditions
- Acceptance sets definition
- State space finiteness

### Phase 4: GNBA-to-NBA (~100-150 lines)
- Cycling counter construction (or leverage `interNA` for k=2 case)
- For general k: define `gnbaNBA` with state space `Atom_phi x Fin k`
- Language equivalence between GNBA and NBA

### Phase 5: Correctness (~300-400 lines)
- **Completeness**: canonical run is a valid accepting GNBA run
  - Transition validity (requires `satisfies_shift`)
  - Acceptance (requires Until eventuality argument)
- **Soundness**: GNBA run implies satisfaction
  - By structural induction on subformulas
  - Until case uses acceptance condition + well-foundedness

### Phase 6: Main Theorem (~20-30 lines)
- `Formula.isRegular_untl` via the GNBA construction
- Alternative: reprove `Formula.isRegular` entirely via GNBA
- Update the `sorry` in `Formula.isRegular`

**Total estimated**: 920-1280 lines of Lean code.

---

## 5. Alternative: Simpler Local Construction

If the full GNBA construction is deemed too large, a simpler approach is possible for
JUST the `isRegular_untl` case. The idea:

```
L(untl φ ψ) = ⋃_{j≥0} (⋂_{k<j} shift^k(L(φ))) ∩ shift^j(L(ψ))
```

where `shift^k(L) = { v | v.drop k ∈ L }`.

Each finite intersection `⋂_{k<j} shift^k(L(φ))` is omega-regular (finite intersection
of omega-regular languages, since `shift` preserves omega-regularity via `isRegular_next`).
And `shift^j(L(ψ))` is omega-regular.

The problem is that this is a COUNTABLE union. But we can show that `L(untl φ ψ)` is
the omega-language of the concatenation of a regular finite-word language with an omega-regular
language, using the `IsRegular.hmul` and `IsRegular.omegaPow` infrastructure.

Specifically:
```
L(untl φ ψ) = L_guard * L(ψ)   (approximately)
```
where `L_guard` is the set of finite words `[a_0, ..., a_{j-1}]` such that `φ` holds at
positions 0, ..., j-1 for any continuation.

**Problem**: `L_guard` depends on the INFINITE continuation (whether φ holds at position k
depends on the entire future). So this is NOT a standard finite-word language.

This confirms that the direct local construction requires essentially the same technology
as the GNBA (tracking subformula satisfaction), and there is no shortcut.

---

## 6. Adversarial Self-Verification

### Challenge 1: Does the closure handle CSLib's `neg = imp _ bot` correctly?

**Verified**: The closure includes `ψ` and `imp ψ bot` for each subformula. The atom
consistency condition `ψ ∈ B ↔ imp ψ bot ∉ B` handles this directly. Double negation
(`imp (imp ψ bot) bot`) is NOT in the closure; it is handled semantically when needed
via classical `¬¬ψ ↔ ψ`.

### Challenge 2: Does the construction work with `[Finite Atom]` (not `[Fintype Atom]`)?

**Verified**: `[Finite Atom]` provides `Finite (Set Atom)` via `Set.finite` when `Atom` is
finite. The `IsRegular` definition requires `Finite State`, not `Fintype State`. The atoms
of the GNBA are finite by `closure_finite` + `finite_subsets`, independent of `Atom`'s
finiteness. The NBA state space is `Atom_phi x Fin k`, which is finite since both
components are finite. So `[Finite Atom]` suffices.

### Challenge 3: Does `isRegular_untl` actually need the full GNBA, or can we use a simpler NBA?

**Verified (challenge stands)**: Report 02 exhaustively analyzed simpler alternatives
(direct NBA, compositional, saturation, fixed-point). All have the same fundamental
difficulty: verifying that the guard formula ACCEPTS at each intermediate position.
The GNBA construction resolves this by encoding formula satisfaction directly in the
state space (atoms), bypassing the need to compose NBAs. No simpler construction has
been identified that avoids this.

### Challenge 4: Is the acceptance condition correctly formulated for reflexive Until?

**Verified**: The acceptance set `F_{φ U ψ} = { B | untl φ ψ ∉ B ∨ ψ ∈ B }` handles
the reflexive case. When `j = i` (event immediately), `ψ ∈ B_i` so `B_i ∈ F_{φ U ψ}`.
The guard condition is vacuously satisfied. This is consistent with CSLib's `∃ j ≥ i`.

### Challenge 5: Universe polymorphism -- does the GNBA construction produce a Type-level state?

**Verified**: When `Atom : Type` (universe 0), `Formula Atom : Type`. The closure is
`Set (Formula Atom) : Type`. Atoms are `Set (Set (Formula Atom))`, but the STATE TYPE
is `{ B : Set (Formula Atom) // IsAtom B }`, which is a subtype of `Set (Formula Atom) : Type`.
After GNBA-to-NBA, states are `{ B // IsAtom B } x Fin k : Type`. This matches
`IsRegular`'s requirement of `State : Type`.

### Challenge 6: Does the existing `interNA` help with the GNBA-to-NBA step?

**Partially**: `interNA` handles exactly 2 acceptance sets (using `Bool`). For `k`
acceptance sets, we would need to generalize to `Fin k`. The `interNA` approach uses a
toggle-history mechanism. For `k > 2`, a cycling counter (`Fin k`) is cleaner. For `k = 0`
or `k = 1`, the conversion is trivial. A dedicated GNBA-to-NBA construction with `Fin k`
counter is recommended rather than iterating `interNA`.

### Challenge 7: Can the existing atom/bot/imp/next proofs be preserved alongside the GNBA?

**Yes**: The GNBA construction proves `Formula.isRegular` directly (not by structural
induction). The existing `isRegular_atom`, `isRegular_bot`, `isRegular_imp`, `isRegular_next`
remain as independent lemmas. They serve as:
- Sanity checks (should be derivable from the GNBA result)
- Simpler alternatives for specific formula patterns
- Educational value (direct NBA constructions)

The `sorry` in `Formula.isRegular` can be replaced either by:
- (a) Completing the structural induction: `| untl φ ψ hφ hψ => exact isRegular_untl hφ hψ`
- (b) Replacing the entire proof with the GNBA result

Option (a) requires proving `isRegular_untl` which IS the hard part. Option (b) bypasses
the structural induction entirely.

**Recommendation**: Use option (a) -- prove `isRegular_untl` via the GNBA construction.
This preserves the existing proof structure and adds the GNBA as supporting infrastructure.

### Verification Outcome

All 7 challenges verified or addressed. No fundamental flaws identified. The GNBA
construction is feasible and well-grounded in the literature.

---

## 7. Revised Recommendations (Consolidated)

1. **Implement the full GNBA construction** following Baier-Katoen Def. 5.37, adapted
   for CSLib's `neg = imp _ bot` convention.

2. **New file**: `Cslib/Logics/LTL/Semantics/GNBA.lean` containing:
   - `Formula.closure` and `closure_finite`
   - `Formula.IsAtom` and `atoms_finite`
   - `Formula.canonicalAtom` and its properties
   - The GNBA definition (`gnbaTr`, `gnbaStart`, `gnbaAccept`)
   - GNBA-to-NBA conversion
   - `gnba_language_eq` (correctness)

3. **Modify**: `Cslib/Logics/LTL/Semantics/OmegaRegular.lean`:
   - Add `import Cslib.Logics.LTL.Semantics.GNBA`
   - Replace `proof_wanted Formula.isRegular_untl` with the proved theorem
   - Replace `sorry` in `Formula.isRegular` with `exact Formula.isRegular_untl hφ hψ`

4. **Preserve**: All existing lemmas (`atomNBA`, `nextNBA`, `isRegular_atom`, etc.)

5. **Add to `references.bib`**: BibKey for Baier-Katoen textbook (not currently present).

6. **Estimated effort**: 920-1280 lines across 6 phases, approximately 25-35 hours of
   implementation work.

---

## 8. References

- [VardiWolper1986] Vardi, M. Y. and Wolper, P. "An Automata-Theoretic Approach to
  Automatic Program Verification." LICS 1986, pp. 332-344. BibKey verified in
  `references.bib` line 727.

- Baier, C. and Katoen, J.-P. "Principles of Model Checking." MIT Press, 2008.
  Chapter 5, Definitions 5.37-5.39. BibKey NOT in `references.bib` (needs addition).

- Schimpf, A., Merz, S., and Smaus, J.-G. "Construction of Buchi Automata for LTL
  Model Checking Verified in Isabelle/HOL." TPHOLs 2009, LNCS 5674, pp. 424-439.
  BibKey NOT in `references.bib` (needs addition).

- Gerth, R., Peled, D., Vardi, M. Y., and Wolper, P. "Simple On-the-fly Automatic
  Verification of Linear Temporal Logic." PSTV 1995, pp. 3-18.
  BibKey NOT in `references.bib` (needs addition).

- Archive of Formal Proofs: "Converting Linear-Time Temporal Logic to Generalized
  Buchi Automata." Isabelle/HOL formalization (2014).
  URL: https://www.isa-afp.org/entries/LTL_to_GBA.html
