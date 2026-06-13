# Teammate C (Critic) Findings — Task 186: Hilbert/ND Equivalence Refactor

## Overview

This report identifies gaps, potential problems, and open questions in the proposed refactoring
of the Hilbert / ND extensional equivalence. It is based on a close reading of:

- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (current implementation)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (ND system definition)
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` (Hilbert system definition)
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` (MinPropAxiom / IntPropAxiom / PropositionalAxiom)
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (deductionTheorem signature)
- `Cslib/Logics/Propositional/Defs.lean` (MPL, IPL, CPL definitions)

---

## Key Findings

### 1. The List ↔ Finset Round-Trip: Not Perfectly Symmetric

**The core asymmetry**: The two conversion directions yield different results:
- `hilbertToND`: starts with `Γ : List`, produces ND derivation over `Γ.toFinset`
- `ndToHilbert`: starts with `Γ : Finset`, produces Hilbert derivation over `Γ.toList`

This means the round-trips are:
- `Hilbert Γ → ND Γ.toFinset → Hilbert Γ.toFinset.toList`
- `ND Γ → Hilbert Γ.toList → ND Γ.toList.toFinset`

**Are these round-trips safe?** Let's check what Mathlib says:

- `Finset.toList_toFinset`: `s.toList.toFinset = s` (SYMMETRIC — round-trip is identity)
- `List.toFinset_toList`: only `Perm` holds (not equality) when the list has duplicates

This means:
- `Γ.toFinset.toList` is a **permutation** of a deduplication of `Γ`, NOT necessarily equal to `Γ`
- `s.toList.toFinset = s` always (the Finset round-trip is exact)

**Consequence**: The `hilbert_iff_nd` theorem works at the *empty context* level, where this
round-trip issue does not arise (both sides use `∅`). But the context-parameterized theorems
`hilbert_to_nd_deriv` and `nd_to_hilbert_deriv` have **mismatched context types**:

- `hilbert_to_nd_deriv`: takes `Deriv Axioms Γ φ` and gives `DerivableIn T (Γ.toFinset ⊢ φ)`
- `nd_to_hilbert_deriv`: takes `DerivableIn T (Γ ⊢ φ)` and gives `Deriv Axioms Γ.toList φ`

These are one-directional bridges, NOT round-trips on the same context. The stated task is to
strengthen `hilbert_iff_nd` to work with non-empty contexts. **This is harder than it looks**:
a statement like `Deriv Axioms Γ φ ↔ DerivableIn T (Γ.toFinset ⊢ φ)` would work, but the
reverse direction would produce `Deriv Axioms Γ.toFinset.toList φ`, not `Deriv Axioms Γ φ`.

**Actual risk**: Low for empty-context results, but non-trivial for context-level equivalence.
The forward bridge `hilbertToND` handles the Finset context correctly via weakening.
The backward bridge `ndToHilbert` outputs `Γ.toList`, which differs from `Γ` when `Γ` has
duplicates or a non-canonical ordering (which a List can have). However, since the Hilbert
system has explicit weakening, `Deriv Axioms Γ.toList φ → Deriv Axioms Γ φ` can be bridged
iff membership is equivalent — which it is: `x ∈ Γ.toList ↔ x ∈ Γ.toFinset` iff `x ∈ Γ`.

**Conclusion**: The round-trip problem does NOT block the proof, but it does mean the most
natural statement — `Deriv Axioms Γ φ ↔ DerivableIn T (Γ.toFinset ⊢ φ)` — requires careful
Hilbert weakening at the end of the backward direction to convert from `Γ.toFinset.toList`
back to `Γ`. The current `hilbert_iff_nd` achieves this via `weakening_deriv` with an explicit
emptiness check. A non-empty context version will need an analogous argument.

---

### 2. EFQ in `ndToHilbert`: Is It Really Needed?

**Current status**: `ndToHilbert` takes `h_EFQ` as an explicit parameter. The question is
whether EFQ is actually necessary for the translation.

**Examining the current code carefully**: `h_EFQ` appears as a *parameter* to `ndToHilbert`
but is NOT directly used in the match branches of `ndToHilbert` itself. Instead, it is passed
down recursively to every sub-call. The `botE` case in the ND system is NOT a primitive
constructor of `Theory.Derivation` — it is a **derived rule** defined in `DerivedRules.lean`
that requires `[IsIntuitionistic T]`.

**Key insight from Basic.lean line 92-93**: The `Theory.Derivation` inductive has 10 primitive
constructors. There is NO `botE` constructor. Bottom elimination is derived via `impE` +
`ax (IsIntuitionistic.efq A)`.

**Therefore**: When `ndToHilbert` pattern-matches on `Theory.Derivation`, there is **no `botE`
branch** to handle, since `botE` is not a constructor. Any ND derivation that uses explosion
does so through `ax` (pulling `⊥ → A` from the theory) followed by `impE`. The `ax` branch of
`ndToHilbert` handles this: it uses the theory membership to produce `Axioms φ`, which produces
a Hilbert axiom application. So if `⊥ → A ∈ AxiomTheory Axioms`, then `Axioms (⊥ → A)` holds,
which means `h_EFQ A` is exactly what we need for the `ax` branch.

**The problem**: `h_EFQ` is passed as a parameter but is never directly called inside `ndToHilbert`.
The `ax` branch handles the EFQ-like cases because when `h_mem : φ ∈ AxiomTheory Axioms`, we get
`Axioms φ` by `mem_axiomTheory.mp h_mem`, and produce `.ax Γ.toList φ (...)`. The EFQ axiom
in the theory becomes a Hilbert axiom instance automatically — NO separate `h_EFQ` witness needed!

**Conclusion**: `h_EFQ` is **entirely redundant** in `ndToHilbert`. Every use of EFQ in an ND
derivation over `AxiomTheory Axioms` routes through the `ax` constructor, which is handled
uniformly by `mem_axiomTheory.mp h_mem`. The `h_EFQ` parameter can and should be removed.
This unblocks a `hilbert_iff_nd_min` corollary for MinPropAxiom.

**However**: Verify this claim by checking whether `h_EFQ` is passed to any helper function that
*does* directly use it. In `HilbertDerivedRules.lean`, `hilbertOrE` calls `impI` (the deduction
theorem), and `impI` only needs K and S. The `hilbertOrE` path in `ndToHilbert` takes `h_K`,
`h_S`, `h_orE` but NOT `h_EFQ`. So `h_EFQ` propagates to subrecursions but is never consumed
— confirming it is unused.

---

### 3. The MinPropAxiom / AxiomTheory Semantic Mismatch — The Critical Issue

**This is the most important finding in this report.**

The task description mentions adding `hilbert_iff_nd_min`. But there is a fundamental conceptual
problem with what this theorem would state.

**What MPL means in the ND system**:
- `MPL : Theory Atom := ∅` (defined in `Defs.lean` line 149)
- MPL = the empty theory; no axioms at all
- A formula is MPL-derivable iff it can be proved using only the 10 primitive ND rules with no
  axiom appeals

**What AxiomTheory MinPropAxiom means**:
- `AxiomTheory MinPropAxiom = { φ | MinPropAxiom φ }`
- This includes K-axioms `φ → (ψ → φ)`, S-axioms, and/or axioms in the theory
- An ND derivation over this theory can use `.ax` to import any K, S, andI, andE1, andE2,
  orI1, orI2, orE instance

**These are NOT the same strength**:
- `DerivableIn MPL (∅ ⊢ φ)` means: provable using only the 10 primitive ND rules and NO axiom
  instances (since the theory is empty)
- `DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)` means: provable using ND rules PLUS the
  entire K/S/andI/andE1/andE2/orI1/orI2/orE schema as axiom instances

The second is at least as strong as the first, and the first is actually WEAKER — it corresponds
to a purely structural proof without any axiom appeals whatsoever. This is not the standard
definition of minimal propositional logic.

**What is MinPropAxiom-Hilbert?**
The Hilbert system `Derivable MinPropAxiom φ` means: provable from K, S, andI, andE1, andE2,
orI1, orI2, orE using modus ponens only. This IS the standard Hilbert formulation of minimal
logic.

**What should the minimal logic ND theory be?**
The correct ND counterpart to `Derivable MinPropAxiom φ` is NOT `DerivableIn MPL` (empty theory)
and NOT `DerivableIn (AxiomTheory MinPropAxiom)` (too many axioms). It is... just the ND system
with no additional axiom appeals. The 10 primitive rules of `Theory.Derivation` already include
andI, andE1, andE2, orI1, orI2, orE, impI, impE — so `DerivableIn MPL (∅ ⊢ φ)` is already a
complete statement of minimal logic via ND, using only the 10 rules.

**Is `Derivable MinPropAxiom φ ↔ DerivableIn MPL (∅ ⊢ φ)` true?**
Yes, this should be provable, and it would be the correct `hilbert_iff_nd_min`. But it does NOT
go through the current `hilbert_iff_nd` framework, which uses `AxiomTheory Axioms`. The current
framework can only prove:
- `Derivable MinPropAxiom φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)`

This second form is less natural and harder to interpret as "minimal logic equivalence."

**The proposed `hilbert_iff_nd_min` theorem**: If the task intends to prove the equivalence with
`AxiomTheory MinPropAxiom` as the ND theory (which is what the current framework gives), then
the theorem is mathematically valid but conceptually misleading. If the task intends to relate
Hilbert-MinPropAxiom to ND-MPL (empty theory), that is a fundamentally DIFFERENT proof that
does NOT go through the current `hilbert_iff_nd` machinery.

**Recommendation**: The task description is ambiguous about which formulation of minimal logic
ND it targets. This must be resolved before implementation.

---

### 4. Context-Level Equivalence vs. Closed-Derivability Only

**Current limitation**: `hilbert_iff_nd` and its corollaries only state equivalence for the
empty context (closed formulas). The task description says "stronger result that Gamma ND-proves
phi iff Gamma Hilbert-proves phi."

**What would a context-level statement look like?**

Option A (natural):
```
theorem hilbert_iff_nd_ctx {Γ : List ...} {φ} :
  Deriv Axioms Γ φ ↔ DerivableIn (AxiomTheory Axioms) (Γ.toFinset ⊢ φ)
```

Option B (alternative):
```
theorem hilbert_iff_nd_ctx {Γ : Finset ...} {φ} :
  Deriv Axioms Γ.toList φ ↔ DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)
```

**The backward direction problem for Option A**: `nd_to_hilbert_deriv` gives
`Deriv Axioms Γ.toList φ`, not `Deriv Axioms Γ φ`. To close the gap:

```
Deriv Axioms Γ.toList φ → Deriv Axioms Γ φ
```

This requires: for all `x ∈ Γ.toList`, `x ∈ Γ` — which is true since `Finset.mem_toList`.
But `Γ` here is a List, and `Γ.toList` is `Γ.toFinset.toList`, which may be a permutation of
`Γ` with duplicates removed. So the implication `x ∈ Γ.toFinset.toList → x ∈ Γ` holds (by
`Finset.mem_toList → mem toFinset → mem original list`). The weakening step is legitimate.

**Conclusion**: Context-level equivalence IS provable with the current framework. The statement
should be Option A or its equivalent. The backward direction needs one extra weakening step.
This is not a blocker, but it adds a proof obligation.

---

### 5. The `orE` Branch: Hidden Dependency on Context Bridge Correctness

In `ndToHilbert`, the `orE` branch:
```
ihA : DerivationTree (insert A G).toList C
```
is weakened to `A :: G.toList` via `finset_insert_toList_mem_cons`. Let's verify this is correct:
- `(insert A G).toList` lists the elements of `insert A G` in some order
- The bridge lemma says: `x ∈ (insert A G).toList → x ∈ A :: G.toList`
- This relies on: if `x ∈ insert A G` then `x = A ∨ x ∈ G`
- Both directions of the bridge lemma use `simp [Finset.mem_toList, List.mem_cons]`

**Risk**: `(insert A G).toList` contains all elements of `insert A G` (since `Finset.mem_toList`
is equivalent to finset membership). So every element of `(insert A G).toList` is either A or
in G.toList. The bridge is correct.

**But**: The bridge `finset_insert_toList_mem_cons` is only one direction (→). For `ndToHilbert`
we also need the fact that the resulting weakened derivation has context `A :: G.toList`,
which is then used as the argument to `hilbertOrE`. Let's check what `hilbertOrE` expects:

```
(dA : DerivationTree Axioms (A :: Γ) C)
(dB : DerivationTree Axioms (B :: Γ) C)
```

So `hilbertOrE` needs `A :: G.toList` and `B :: G.toList`. The weakened `ihA'` and `ihB'` have
exactly these types. The proof appears correct.

---

### 6. Noncomputability and `Classical.propDecidable`

`ndToHilbert` is `noncomputable` because `deductionTheorem` uses `Classical.propDecidable`
(for the `by_cases` in the weakening case). The task description acknowledges this.

**Is this acceptable?** Yes — the ND system's `Theory.Derivation` is itself `Type u` (computable),
but the translation uses non-constructive reasoning. Since the goal is classical propositional
logic equivalence (where excluded middle holds), `noncomputable` is appropriate.

**However**: If a user wants a *constructive* proof of the equivalence (e.g., for minimal or
intuitionistic logic where EFQ-free), the `noncomputable` tag is a signal that the current
proof strategy may be non-optimal. The deduction theorem uses `Classical.propDecidable` because
it needs `by_cases hA : A ∈ Γ'` in the weakening case. This case analysis IS constructive if
`Γ'` is finite and `A` has decidable equality — which it does, since `[DecidableEq Atom]` is
in context. So there may be a constructive version available.

**Concrete risk**: If the refactoring removes `h_EFQ` to enable `hilbert_iff_nd_min`, but the
`noncomputable` tag persists, then the minimal logic equivalence will be noncomputable. This is
philosophically odd for minimal logic but not a mathematical error.

---

### 7. Signature Bloat in `ndToHilbert`

The current `ndToHilbert` has 9 explicit axiom parameters (h_K, h_S, h_EFQ, h_andI, h_andE1,
h_andE2, h_orI1, h_orI2, h_orE). This is unwieldy for the generic generic theorem.

**The question**: Can these be bundled via a typeclass? The existing `HasHilbertTree` typeclass
(defined in `DeductionTheorem.lean`) covers K, S, assumption, mp, weakening. But it does NOT
cover the and/or axioms. A refactoring that introduces a `HasFullHilbert` typeclass bundling all
9 parameters would clean this up significantly.

**Risk**: Introducing a new typeclass might conflict with the zero-debt policy if the typeclass
requires instances that don't yet exist for MinPropAxiom. Need to verify MinPropAxiom covers all
9 parameters (it does: K, S, andI, andE1, andE2, orI1, orI2, orE — all 8 match, no EFQ).
Classical PropositionalAxiom covers all 9 including EFQ. IntPropAxiom covers all 9.

---

### 8. `hilbert_iff_nd_cl`: Redundancy with `hilbert_iff_nd_int`

Both `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` use the same 9 proof witnesses. Classical
logic (PropositionalAxiom) adds only Peirce's law over IntPropAxiom, but the current
`hilbert_iff_nd` framework makes no use of Peirce — it only needs K, S, EFQ, and the 6 and/or
axioms. So the distinction between `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` is minimal in
the current proof: both are just applications of `hilbert_iff_nd` with witnesses.

**Risk for refactoring**: If the goal is to state `hilbert_iff_nd` in a more informative way
showing what makes classical vs. intuitionistic vs. minimal logic different, the current
approach is not revealing. A more informative architecture would distinguish:
- The `impI` case needing only K and S
- The `orE` case needing K, S, and orE
- No case needing EFQ (for the non-empty context version)

---

### 9. Literature References and Docstrings

The current docstring references are sparse and mostly self-referential (pointing to other CSLib
files). The module header says `## References` but lists only other CSLib files, not external
sources. For a contribution to CSLib at publication quality, the equivalence should cite:

- The standard result (e.g., Prawitz 1965 Chapter 2, or Troelstra-van Dalen 1988)
- Specifically: the fact that Hilbert-style and Gentzen ND are equivalent for propositional
  logic is classical but specific citation depends on the exact formulation

**Risk**: If the task requires BibKey citation (`[Prawitz1965]`, `[TroelstraVanDalen1988]`),
the implementer must check that these keys exist in `references.bib`.

---

## Gaps Identified

1. **No `hilbert_iff_nd_min` currently**: Exists as a gap by design (EFQ required). Fixing this
   requires (a) removing `h_EFQ` from `ndToHilbert`, (b) clarifying which ND theory corresponds
   to minimal Hilbert logic.

2. **No context-level equivalence**: The current `hilbert_iff_nd` only covers empty contexts.
   The task description calls for "Gamma ND-proves phi iff Gamma Hilbert-proves phi" but the
   current architecture only delivers this as two separate one-directional wrappers
   (`hilbert_to_nd_deriv`, `nd_to_hilbert_deriv`) with mismatched context types.

3. **`h_EFQ` is unused but still required**: This is a latent code smell. Removing it is safe
   and necessary for minimal logic.

4. **The `list_cons_mem_finset_insert_toList` lemma**: This bridge lemma is defined but may not
   be used in `ndToHilbert` itself. If unused, it should be removed or marked private.

5. **No proof that `AxiomTheory MinPropAxiom ≠ MPL`**: The conceptual gap between these two
   theories is undocumented. A user reading the code might not realize they are different.

---

## Questions That Should Be Asked

1. **Which ND theory corresponds to minimal logic?** Is the target `DerivableIn MPL` or
   `DerivableIn (AxiomTheory MinPropAxiom)`? These require different proof strategies and state
   different mathematical results.

2. **Is context-level equivalence the goal, or only closed derivability?** The task says "Gamma
   ND-proves phi iff Gamma Hilbert-proves phi" but the current architecture treats contexts
   differently. A context-level theorem is achievable but requires specifying whether Γ is a
   List or Finset on each side.

3. **Should `h_EFQ` be removed from `ndToHilbert`?** This is the key change enabling
   `hilbert_iff_nd_min`, and appears safe, but needs verification that no helper function
   in the recursive calls actually uses `h_EFQ`.

4. **Should the 9 explicit axiom parameters be bundled into a typeclass?** This affects the
   public API and downstream users of `hilbert_iff_nd`.

5. **Is `noncomputable` acceptable for `hilbert_iff_nd_min`?** For minimal logic, a
   constructive proof would be more faithful. Is there a constructive version of the deduction
   theorem for the minimal case?

6. **What do "review proof style" and "proper literature references" mean concretely?** Do they
   imply specific BibKey citations? If so, which entries in `references.bib` apply?

---

## Confidence Level

| Issue | Confidence |
|-------|------------|
| h_EFQ is redundant in ndToHilbert | High — no branch directly uses it |
| AxiomTheory MinPropAxiom ≠ MPL conceptually | High — confirmed by Defs.lean |
| Round-trip is safe for empty context | High — confirmed by Mathlib lemmas |
| Round-trip for non-empty context needs one more weakening | Medium-High |
| hilbert_iff_nd_min is achievable after removing h_EFQ | Medium — needs test |
| Constructive deduction theorem is available | Low — requires deeper investigation |
| All 9 parameters can be bundled cleanly | Medium — requires new typeclass |

Overall assessment: The core equivalence proofs are mathematically sound. The main risks are
(1) the semantic mismatch between `AxiomTheory MinPropAxiom` and `MPL` for the minimal logic
corollary, and (2) the underspecification of whether the context-level equivalence should use
List or Finset on the Hilbert side. These are conceptual/design questions, not proof obstacles.
