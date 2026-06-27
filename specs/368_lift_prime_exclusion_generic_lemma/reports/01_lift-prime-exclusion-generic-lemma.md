# Research Report: Lift Prime-Exclusion Machinery to a Generic Foundations Lemma

**Task**: 368 — `lift_prime_exclusion_generic_lemma`
**Session**: sess_1782560395_aeb7ef_368
**Type**: cslib
**Status**: researched

## 1. Summary

The intuitionistic (`IntLindenbaum.lean`) and minimal (`MinLindenbaum.lean`) prime-exclusion
constructions share ~70% identical Zorn + orE + chain-union logic. The shared structure can be
lifted to **one generic file at `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`**,
parameterized over a `Metalogic.DerivationSystem F` (not over the concrete `PL.Proposition` /
`DerivationTree` types). This respects the Foundations-below-Logics layering and mirrors the
**existing** generic Lindenbaum template in `Cslib/Foundations/Logic/Metalogic/Consistency.lean`
(`ConsistentSupersets`, `finite_list_in_chain_member`, `consistent_chain_union`, `set_lindenbaum`).

The only genuine difference between the two call sites — intuitionistic threads an **EFQ
consistency check** — is isolated into two small parameters: an **optional consistency predicate
`Cons` (default `fun _ => True`)** and an **EFQ-bridge witness** that is vacuous in the minimal
case. No new axioms; both proofs stay sorry-free.

## 2. Reuse Check (reuse-first protocol)

| Candidate already in Foundations | Found? | Reuse decision |
|---|---|---|
| `Metalogic.DerivationSystem F` (Deriv/weakening/assumption/mp) | YES (`Consistency.lean:56`) | **Reuse as the abstraction vehicle** |
| `Metalogic.finite_list_in_chain_member` | YES (`Consistency.lean:115`) | Reuse (both files already call it) |
| `Metalogic.consistent_chain_union` | YES (`Consistency.lean:142`) | Reuse for `Cons`-chain-closure in the int case |
| `Metalogic.SetConsistent D S` | YES (`Consistency.lean:77`) | `PropSetConsistent Ax = SetConsistent (propDerivationSystem Ax)` (`MCS.lean:47`) — direct |
| Generic Lindenbaum/Zorn template (`ConsistentSupersets`, `base_mem_*`, `set_lindenbaum`) | YES (`Consistency.lean:87,107,157`) | **Pattern to mirror exactly** |
| `HasImp` / `HasBot` / `HasOr` typeclasses | YES (`Connectives.lean:80,85,137`) | Reuse — gives generic `⟶`, `⊥`, `⊔` |
| Generic orE axiom schema | YES (`Foundations/Logic/Axioms.lean:133`, over `HasOr`/`HasImp`) | Reference; supply orE as a `Deriv []` hypothesis |
| Existing prime-exclusion in Foundations | NO | New file `PrimeExclusion.lean` justified |

**Layering note**: `Cslib/Foundations/` never imports `Cslib/Logics/` within the Logic/Metalogic
subtree (the only Foundations→Logics edges are in `Foundations/Order/HilbertAlgebra/`). The
generic lemma therefore must NOT mention `PL.Proposition`, `DerivationTree`, `IntPropAxiom`, or
`propDerivationSystem`. It is stated purely over `F : Type*` + `DerivationSystem F`, exactly like
`set_lindenbaum`. The concrete instantiation lives back in the two Logics files.

## 3. Exact Shared Structure (line-level)

Five declarations are duplicated between the files (int / min):

| Role | IntLindenbaum.lean | MinLindenbaum.lean | Diff |
|---|---|---|---|
| Zorn domain def | `IntPrimeExcludingSupersets` (267) | `MinPrimeExcludingSupersets` (228) | predicate `IntDCCS` vs `MinTheory` only |
| base membership | `int_excluding_base_mem` (273) | `min_excluding_base_mem` (234) | identical mod predicate |
| chain union | `int_excluding_chain_union` (282) | `min_excluding_chain_union` (243) | int has extra consistency clause (296–298) |
| maximal ⇒ prime | `int_maximal_is_prime` (315) | `min_maximal_is_prime` (272) | int has EFQ `by_cases` branches (336–355, 366–382) |
| Zorn application | `int_prime_exclusion` (427) | `min_prime_exclusion` (358) | identical mod names |

**Byte-identical core** inside `*_maximal_is_prime`: the final orE combination
(`Int:386–418` ≡ `Min:316–351`) — build `(A⟶φ)⟶((B⟶φ)⟶((A⊔B)⟶φ))` from `[]`, weaken to
`ctx := L' ++ L'' ++ [A.or B]`, three `modus_ponens`, then close via the theory's
deductive-closure clause. The `obtain ⟨L', …⟩ := *_deriv_imp_of_union …` calls (Int:357–358,
383–385; Min:297–298, 313–315) are identical.

**The sole structural difference** is *how* `φ ∈ cl(T ∪ {A})` is obtained:
- **Min** (290–295): `cl(T∪{A})` is unconditionally a `MinTheory` (`minDeductiveClosure_is_theory`),
  so maximality forces `φ ∈ cl(T∪{A})`.
- **Int** (329–355): `by_cases` on `PropSetConsistent IntPropAxiom (T∪{A})`. Consistent ⇒ same
  maximality argument (using `intDeductiveClosure_is_dccs h_cons_A`). Inconsistent ⇒ EFQ
  (`.ax [] _ (.efq φ)` + weakening + MP from `⊥`) puts `φ` in the closure directly.

## 4. Recommended Generic Design

New file `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean`
(`namespace Cslib.Logic.Metalogic`, `import Cslib.Init` + `Consistency`).

```lean
variable {F : Type*} [HasImp F] [HasBot F] [HasOr F]

/-- Generic deductively-closed-set predicate for a derivation system. -/
def DeductivelyClosed (D : DerivationSystem F) (S : Set F) : Prop :=
  ∀ (L : List F) (φ : F), (∀ x ∈ L, x ∈ S) → D.Deriv L φ → φ ∈ S

/-- A theory is admissible when it satisfies the (optional) consistency predicate
    and is deductively closed.  `Cons := fun _ => True` recovers the minimal case. -/
def Admissible (D : DerivationSystem F) (Cons : Set F → Prop) (S : Set F) : Prop :=
  Cons S ∧ DeductivelyClosed D S

/-- The φ-excluding admissible supersets of `S`; the Zorn domain. -/
def PrimeExcludingSupersets (D : DerivationSystem F) (Cons : Set F → Prop)
    (S : Set F) (phi : F) : Set (Set F) :=
  {T | S ⊆ T ∧ Admissible D Cons T ∧ phi ∉ T}

/-- Disjunction property over admissible sets. -/
def PrimeAdmissible (D : DerivationSystem F) (Cons : Set F → Prop) (S : Set F) : Prop :=
  Admissible D Cons S ∧ ∀ A B : F, HasOr.or A B ∈ S → A ∈ S ∨ B ∈ S
```

### 4.1 Main lemma signature (`maximal_is_prime`)

```lean
theorem prime_maximal_is_prime
    (D : DerivationSystem F) (Cons : Set F → Prop)
    {S : Set F} {phi : F} {T : Set F}
    -- orE schema available as an empty-context derivation:
    (hOrE : ∀ A B χ : F,
        D.Deriv [] (HasImp.imp (HasImp.imp A χ)
                      (HasImp.imp (HasImp.imp B χ) (HasImp.imp (HasOr.or A B) χ))))
    -- deductive-closure operator + its laws (instantiated by int/minDeductiveClosure):
    (cl : Set F → Set F)
    (cl_subset : ∀ X, X ⊆ cl X)
    (cl_mem_imp : ∀ {X ψ}, ψ ∈ cl X → ∃ L, (∀ x ∈ L, x ∈ X) ∧ D.Deriv L ψ)
    (cl_admissible_of_cons : ∀ {X}, Cons X → Admissible D Cons (cl X))
    -- the ONLY place the consistency check is threaded (vacuous when Cons = fun _ => True):
    (phi_mem_cl_of_not_cons : ∀ {X}, ¬ Cons X → phi ∈ cl X)
    -- the cut / deduction witness (= int/min_deriv_imp_of_union):
    (hCut : ∀ {U : Set F} {L : List F} {a b : F},
        (∀ x ∈ L, x ∈ insert a U) → D.Deriv L b →
        ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (HasImp.imp a b))
    (hmax : Maximal (· ∈ PrimeExcludingSupersets D Cons S phi) T) :
    PrimeAdmissible D Cons S T
```

Proof body (≈ both current proofs, with the int/min split now internal):
`refine ⟨hmax.prop.2.1.2-shaped …⟩`; `intro A B h_or; by_contra; obtain ⟨hA,hB⟩`; for each
disjunct prove `phi ∈ cl (insert A T)` via
```lean
by_cases hc : Cons (insert A T)
· -- maximality argument (shared): Admissible (cl …) from cl_admissible_of_cons hc
  by_contra hnp
  have hmem : cl (insert A T) ∈ PrimeExcludingSupersets D Cons S phi :=
    ⟨hmax.prop.1.trans (cl_subset _ ∘ Set.subset_insert …), cl_admissible_of_cons hc, hnp⟩
  exact hA ((hmax.eq_of_ge hmem (subset)).symm ▸ cl_subset _ (mem_insert ..))
· exact phi_mem_cl_of_not_cons hc        -- EFQ bridge (vacuous in min case)
```
then `cl_mem_imp` + `hCut` give `L' ⊆ T, D.Deriv L' (A ⟶ phi)`; the **orE combination** block
(currently `Int:386–418`/`Min:316–351`) is reproduced once here using only
`D.weakening` / `D.assumption` / `D.mp` / `hOrE`; the final `φ ∈ T` step uses the deductive-closure
clause `hmax.prop.2.1.2 : DeductivelyClosed D T`.

### 4.2 Supporting generic lemmas

```lean
theorem prime_excluding_base_mem (D) (Cons) {S} (hS : Admissible D Cons S) {phi}
    (h_not : phi ∉ S) : S ∈ PrimeExcludingSupersets D Cons S phi :=
  ⟨Set.Subset.refl S, hS, h_not⟩

/-- Deductive closure is preserved by nonempty chain unions (generic; uses
    `finite_list_in_chain_member`). Mirrors Int:299–303 / Min:254–260 verbatim. -/
theorem deductivelyClosed_chain_union (D) {C} (hchain) (hCne)
    (h : ∀ T ∈ C, DeductivelyClosed D T) : DeductivelyClosed D (⋃₀ C) := …

theorem prime_excluding_chain_union (D) (Cons) {S phi C}
    (hCsub : C ⊆ PrimeExcludingSupersets D Cons S phi)
    (hchain) (hCne)
    -- Cons preserved under chain union (int: `consistent_chain_union`; min: trivial):
    (hConsChain : Cons (⋃₀ C)) :
    (⋃₀ C) ∈ PrimeExcludingSupersets D Cons S phi := …

/-- Zorn application, mirrors `set_lindenbaum`. -/
theorem prime_exclusion (D) (Cons) {S} (hS : Admissible D Cons S) {phi} (h_not : phi ∉ S)
    (hOrE) (cl) (cl_subset) (cl_mem_imp) (cl_admissible_of_cons)
    (phi_mem_cl_of_not_cons) (hCut)
    (hConsChain : ∀ C, IsChain (· ⊆ ·) C → C.Nonempty →
        C ⊆ PrimeExcludingSupersets D Cons S phi → Cons (⋃₀ C)) :
    ∃ T, S ⊆ T ∧ PrimeAdmissible D Cons S T ∧ phi ∉ T := …
```

## 5. Call-Site Re-derivation Sketch

### 5.1 Minimal (`MinLindenbaum.lean`)
- `D := propDerivationSystem MinPropAxiom`, `Cons := fun _ => True`.
- `Admissible D Cons S ↔ MinTheory S` (the `Cons` conjunct is `True`); keep `MinTheory`,
  `MinPrimeTheory` as thin `abbrev`s over the generic predicates (or a one-line iff).
- Instantiations: `cl := minDeductiveClosure`; `cl_subset := min_subset_deductive_closure`;
  `cl_mem_imp := fun h => h` (definitional — `minDeductiveClosure` is literally
  `{φ | ∃ L, … ∧ Deriv L φ}`); `cl_admissible_of_cons := fun _ => ⟨trivial, minDeductiveClosure_is_theory _⟩`;
  `phi_mem_cl_of_not_cons := fun h => absurd trivial h` (**vacuous**);
  `hCut := @min_deriv_imp_of_union` (note `insert a U` vs `U ∪ {a}` — `Set.union_comm`/`insert` defeq, one rewrite);
  `hOrE := fun A B χ => ⟨.weakening … (.ax [] _ (.orE A B χ)) …⟩` (or directly the `Deriv` form);
  `hConsChain := fun _ _ _ _ => trivial`.
- `min_prime_exclusion` becomes a ~10-line wrapper calling `prime_exclusion`.

### 5.2 Intuitionistic (`IntLindenbaum.lean`)
- `D := propDerivationSystem IntPropAxiom`, `Cons := SetConsistent (propDerivationSystem IntPropAxiom)`
  (= `PropSetConsistent IntPropAxiom`, by `MCS.lean:47`).
- `Admissible D Cons S ↔ IntDCCS S` (consistency ∧ closure) — `IntDCCS`, `IntPrimeDCCS` become
  thin wrappers.
- Instantiations: `cl := intDeductiveClosure`; `cl_admissible_of_cons := fun hc => intDeductiveClosure_is_dccs hc`;
  `phi_mem_cl_of_not_cons := ` the **EFQ block** currently at `Int:344–355` (unfold inconsistency,
  `.efq`, weaken, MP from `⊥`) — lifted unchanged;
  `hCut := @int_deriv_imp_of_union`; `hConsChain := consistent_chain_union` (Foundations).
- `int_prime_exclusion` becomes a ~10-line wrapper.

## 6. Verification Notes (symbols confirmed by source read)

- `DerivationSystem F` fields `Deriv/weakening/assumption/mp` — `Consistency.lean:56–64`.
- `finite_list_in_chain_member`, `consistent_chain_union`, `set_lindenbaum`, `ConsistentSupersets`,
  `base_mem_consistent_supersets` — `Consistency.lean:115,142,157,87,107`.
- `HasImp/HasBot/HasOr` — `Connectives.lean:80,85,137`; generic orE schema — `Axioms.lean:133`.
- `PropSetConsistent Ax S = SetConsistent (propDerivationSystem Ax) S` — `MCS.lean:47`.
- `IntPropAxiom.orE` / `MinPropAxiom.orE` constructors — `Axioms.lean:115,149`; `IntPropAxiom.efq` — `Axioms.lean:97`.
- `int/min_deriv_imp_of_union` — `IntLindenbaum.lean:133` / `MinLindenbaum.lean:116` (signature uses `S ∪ {φ}`).
- `int/minDeductiveClosure(_is_dccs/_is_theory/subset_)` — `IntLindenbaum.lean:193,199,223` / `MinLindenbaum.lean:175,181,188`.
- `Maximal.prop`, `Maximal.eq_of_ge`, `zorn_subset_nonempty` — Mathlib, used identically in both files.

## 7. Risks / Watch-Items for Planning

1. **`insert a U` vs `U ∪ {a}`**: `hCut` (generic) uses `insert`; the existing witnesses use `S ∪ {φ}`.
   `insert a U = {a} ∪ U` and `Set.union_comm` — a one-line adapter per call site, not a blocker.
2. **`cl_mem_imp` is definitional** for both closures (`{φ | ∃ L, … ∧ Deriv L φ}`), so it is `id`/`fun h => h`.
3. **Parameter count**: the main lemma takes ~8 structural parameters. To keep call sites tidy,
   bundle them into a `structure PrimeExclusionData D Cons phi` (optional polish, not required).
4. **Keep `IntDCCS`/`MinTheory` public names** (downstream `StrongCompleteness` depends on them) —
   re-express as `abbrev`/iff over `Admissible`, do not delete.
5. **CI**: after refactor run `lake build`, `lake test`, `lake exe checkInitImports`,
   `lake exe lint-style`, `lake shake …`. New file needs `import Cslib.Init` and a docstring on
   every new declaration (docBlame); Prop-valued defs that are propositions must stay `def` only if
   used as data — `DeductivelyClosed`/`Admissible` are `Prop` predicates (use `def`, consistent with
   `SetConsistent`). Add to `Cslib.lean` barrel via `lake exe mk_all --module`.
6. **Net reduction**: ~150 lines (two ~80-line `*_maximal_is_prime` + duplicated chain/base/Zorn
   collapse to one generic copy + ~10-line wrappers each). Confirmed achievable.

## 8. Recommended Next Action

Proceed to `/plan`. Suggested phases: (1) create `PrimeExclusion.lean` with the generic
defs + `prime_excluding_base_mem` + `deductivelyClosed_chain_union` + `prime_excluding_chain_union`;
(2) generic `prime_maximal_is_prime` + `prime_exclusion` (the orE block is the heavy part);
(3) re-derive `min_*` (simplest, `Cons = True`); (4) re-derive `int_*` (EFQ bridge); (5) CI + shake.
