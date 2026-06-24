# Research Report: LJ Cut Admissibility (Task 330)

## Session

- **Session ID**: sess_1750817400_a3b7c1_330
- **Date**: 2026-06-24
- **Task**: Fill the sorry in `cutAdmissibility` at `LJ/CutElimination.lean:103`

## Problem Statement

The function `Cslib.Logic.PL.cutAdmissibility` at line 98-103 of
`Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` has a sorry
placeholder. Its signature is:

```lean
noncomputable def cutAdmissibility (A : Proposition Atom) (Γ : Ctx Atom)
    (C : Proposition Atom)
    (d₁ : CutFreeLJProof (Γ ⊢ A))
    (d₂ : CutFreeLJProof (insert A Γ ⊢ C)) :
    CutFreeLJProof (Γ ⊢ C)
```

This is the **only sorry** in the LJ sequent calculus module. Filling it completes
`LJProof.cutElim` (line 114), which uses `cutAdmissibility` at line 149 to handle
the cut constructor case.

## Existing Infrastructure

### LJ Proof System (LJ/Basic.lean)

- `LJProof`: inductive with 11 constructors: `ax`, `botL`, `andL`, `andR`, `orL`,
  `orR1`, `orR2`, `impL`, `impR`, `weakL`, `cut`
- `LJProof.height`: proof tree depth
- `LJProof.mono`: left-side weakening (single argument, since single conclusion)
- `LJCutFree`: recursive predicate (`False` at `cut`, `True` at leaves, conjunction at branching)
- `CutFreeLJProof`: subtype `{ d : LJProof seq // LJCutFree d }`

### Already Proved (LJ/CutElimination.lean)

- `LJCutFree.mono` (line 54): cut-freeness preserved under `LJProof.mono`
- `CutFreeLJProof.mono` (line 82): monotonicity for cut-free proofs
- `LJProof.cutElim` (line 114): structural induction using `cutAdmissibility` --
  compiles modulo the sorry in `cutAdmissibility`

### LK Reference Implementation (LK/CutElimination.lean)

The classical LK cut elimination is fully proved and provides a template:
- `CutIH` type alias for subformula induction hypothesis (line 96)
- Three standalone self-recursive helpers (lines 138-575):
  `cutAdm_right_andR`, `cutAdm_right_orR`, `cutAdm_right_impR`
- Mutual block (lines 584-885): `cutAdm_right` / `cutAdm_left`
- Top-level `cutAdmissibility` by WF recursion on `sizeOf C` (line 892)
- `LKProof.cutElim` (line 906)

## Key Structural Differences: LJ vs LK

| Feature | LK | LJ |
|---------|----|----|
| Sequent type | `Finset ⊢ₛ Finset` (multi-conclusion) | `Finset × Proposition` (single conclusion) |
| Right weakening | `weakR` constructor | Not needed (no succedent set) |
| Right disjunction | Single `orR` with membership proof | Two rules: `orR1`, `orR2` |
| Right conjunction | `andR` with membership proof | `andR` without membership (conclusion is the formula) |
| Right implication | `impR` with membership proof | `impR` without membership |
| Left implication | `impL`: left sub-proof `Γ ⊢ₛ insert A Δ` | `impL`: left sub-proof `Γ ⊢ A` (single conclusion) |
| Subset hypotheses in helpers | Both `hant : Γ ⊆ ...` and `hsuc : Δ ⊆ ...` | Only `hant : Γ ⊆ ...` (no succedent set) |
| Principal or cases | One orR case, one orL case | Two orR cases (orR1, orR2), one orL case |

The single-conclusion constraint significantly simplifies the proof:
1. No `hsuc` subset hypothesis needed anywhere
2. No `weakR` cases to handle
3. No membership proofs for right-introduction rules
4. Context management only on the antecedent side
5. The `ljCutAdm_right` helper does not need to track succedent changes

However, `orR1`/`orR2` splitting adds one extra case in the `ljCutAdm_left` function.

## Recommended Proof Architecture

### Overview

Follow the LK decomposition pattern, adapted for single-conclusion sequents:

```
cutAdmissibility (top-level, WF on sizeOf A)
  └─ ljCutAdm_left (structural on d₁, calls principal helpers)
       └─ ljCutAdm_right (structural on d₂, calls ljCutAdm_left for left-decomposition of A)
            └─ ljCutAdm_left (mutual call)

ljCutAdm_principal_andR (standalone, structural on d₂)
ljCutAdm_principal_orR1 (standalone, structural on d₂)
ljCutAdm_principal_orR2 (standalone, structural on d₂)
ljCutAdm_principal_impR (standalone, structural on d₂)
```

### Component 1: LJCutIH Type Alias

```lean
noncomputable abbrev LJCutIH (A : Proposition Atom) : Type u :=
  ∀ (B : Proposition Atom), sizeOf B < sizeOf A →
    ∀ (Γ : Ctx Atom) (C : Proposition Atom),
    CutFreeLJProof (Γ, B) →
    CutFreeLJProof (insert B Γ, C) →
    CutFreeLJProof (Γ, C)
```

### Component 2: Standalone Principal Helpers

Each helper handles one principal connective case. They are self-recursive
(structural recursion on d₂) and use `ih : LJCutIH A` for the actual principal case.

**ljCutAdm_principal_andR**: Principal case where `A = P ∧ Q`.
- Inputs: `P Q`, `Γ₀`, `d₁p : CutFreeLJProof (Γ₀, P)`, `d₁q : CutFreeLJProof (Γ₀, Q)`,
  `ih : LJCutIH (P ∧ Q)`, `d₂ : LJProof (Γ, C)`, `hcf₂`, `hant : Γ ⊆ insert (P∧Q) Γ₀`
- Output: `CutFreeLJProof (Γ₀, C)`
- Principal case (d₂ = andL P Q): recurse on d', then cut P and Q via ih
- Non-principal cases: reconstruct the rule, recurse on sub-proofs

**ljCutAdm_principal_orR1** and **ljCutAdm_principal_orR2**: Principal cases where
`A = P ∨ Q` and d₁ ends with orR1 (proving P) or orR2 (proving Q).
- Note: these could be merged into a single `ljCutAdm_principal_orR` that takes
  `d₁sub : CutFreeLJProof (Γ₀, X)` where X is P (for orR1) or Q (for orR2),
  along with the appropriate sizeOf bound.
- Principal case (d₂ = orL P Q): recurse on d₂'s sub-proofs, then cut X via ih
- Actually the LK approach uses a single helper `cutAdm_right_orR` that takes
  the combined sub-proof. For LJ, a single helper can work:

```lean
noncomputable def ljCutAdm_principal_orR
    (P Q : Proposition Atom) (Γ₀ : Ctx Atom)
    (d₁sub : CutFreeLJProof (Γ₀, X))  -- X = P or X = Q
    (hX : sizeOf X < sizeOf (P ∨ Q))
    (ih : LJCutIH (P ∨ Q))
    ...
```

Wait, actually for the or case the principal interaction is:
- d₁ = orR1 P Q dp (gives (Γ₀, P)) OR d₁ = orR2 P Q dq (gives (Γ₀, Q))
- d₂ has orL P Q (giving sub-proofs for P case and Q case)

In the principal case when d₂ = orL P Q:
- If d₁ was orR1: we have dp : (Γ₀, P) and d₂_P : (insert P Γ, C) (after cleaning).
  Cut on P (sizeOf P < sizeOf (P∨Q)): ih P gives (Γ₀, C).
- If d₁ was orR2: we have dq : (Γ₀, Q) and d₂_Q : (insert Q Γ, C) (after cleaning).
  Cut on Q: ih Q gives (Γ₀, C).

So two separate helpers (or one parameterized by which disjunct) is fine.

Actually, looking at the LK code more carefully, `cutAdm_right_orR` takes
`d₁' : CutFreeLKProof (Γ₀ ⊢ₛ insert A (insert B Δ₀))` which has BOTH A and B
in the succedent. This is specific to LK's multi-conclusion. For LJ, d₁ proves
exactly one of P or Q, not both. So the LJ helper is genuinely simpler.

I recommend a single parameterized helper that handles both orR1 and orR2:

```lean
noncomputable def ljCutAdm_principal_or
    (P Q : Proposition Atom) (Γ₀ : Ctx Atom)
    (whichDisjunct : Bool)  -- true = left (P), false = right (Q)
    (d₁sub : CutFreeLJProof (Γ₀, if whichDisjunct then P else Q))
    (ih : LJCutIH (P ∨ Q))
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d₂ : LJProof (Γ, C)) (hcf₂ : LJCutFree d₂)
    (hant : Γ ⊆ insert (P ∨ Q) Γ₀) :
    CutFreeLJProof (Γ₀, C)
```

Or more simply, two separate helpers following the LK pattern.

**ljCutAdm_principal_impR**: Principal case where `A = P → Q`.
- Inputs: `P Q`, `Γ₀`, `d₁' : CutFreeLJProof (insert P Γ₀, Q)`,
  `ih : LJCutIH (P → Q)`, `d₂ : LJProof (Γ, C)`, `hcf₂`, `hant`
- Principal case (d₂ = impL P Q):
  - d₂'s left sub-proof: `(insert (P→Q) Γ, P)` -- recurse to get `(Γ₀, P)`
    (actually `(Γ₀, P)` after recursion strips P→Q from context)
  - Wait, this needs careful thinking. When d₂ = impL P Q hPQ d₂a d₂b:
    - d₂a : LJProof (Γ, P) with Γ ⊆ insert (P→Q) Γ₀
    - d₂b : LJProof (insert Q Γ, C) with insert Q Γ ⊆ insert (P→Q) (insert Q Γ₀)
  - Recurse on d₂a to get `ra : CutFreeLJProof (Γ₀, P)`
  - Recurse on d₂b to get `rb : CutFreeLJProof (insert Q Γ₀, C)`
  - Cut P: from d₁' : (insert P Γ₀, Q) and ra : (Γ₀, P), use ih P to get (Γ₀, Q)
  - Cut Q: from (Γ₀, Q) and rb : (insert Q Γ₀, C), use ih Q to get (Γ₀, C)

### Component 3: Mutual Block

```lean
mutual

noncomputable def ljCutAdm_right
    (A : Proposition Atom) (Γ₀ : Ctx Atom)
    (d₁ : CutFreeLJProof (Γ₀, A)) (ih : LJCutIH A)
    {Γ : Ctx Atom} {C : Proposition Atom}
    (d₂ : LJProof (Γ, C)) (hcf₂ : LJCutFree d₂)
    (hant : Γ ⊆ insert A Γ₀) :
    CutFreeLJProof (Γ₀, C)

noncomputable def ljCutAdm_left
    (A : Proposition Atom) (Γ₀ : Ctx Atom) (C₀ : Proposition Atom)
    (d₂ : CutFreeLJProof (insert A Γ₀, C₀)) (ih : LJCutIH A)
    {Γ : Ctx Atom}
    (d₁ : LJProof (Γ, A)) (hcf₁ : LJCutFree d₁)
    (hant : Γ ⊆ Γ₀) :
    CutFreeLJProof (Γ₀, C₀)

end -- mutual
```

### Component 4: Top-Level

```lean
noncomputable def cutAdmissibility (A : Proposition Atom) (Γ : Ctx Atom)
    (C : Proposition Atom)
    (d₁ : CutFreeLJProof (Γ ⊢ A))
    (d₂ : CutFreeLJProof (insert A Γ ⊢ C)) :
    CutFreeLJProof (Γ ⊢ C) :=
  ljCutAdm_left A Γ C d₂
    (fun B _ Γ' C' d₁' d₂' => cutAdmissibility B Γ' C' d₁' d₂')
    d₁.1 d₁.2 (Finset.Subset.refl _)
termination_by sizeOf A
```

## Detailed Case Analysis

### ljCutAdm_right Cases (structural on d₂)

| d₂ last rule | A is principal? | Action |
|--------------|----------------|--------|
| `ax phi` | phi = A | Use d₁ (already proves Γ₀ ⊢ A = Γ₀ ⊢ phi) |
| `ax phi` | phi /= A | phi ∈ Γ₀ (from subset), reconstruct ax |
| `botL` | bot = A | Switch to ljCutAdm_left |
| `botL` | bot /= A | bot ∈ Γ₀ (from subset), reconstruct botL |
| `andL A' B'` | A'∧B' = A | Recurse on d', build d₂_new, switch to ljCutAdm_left |
| `andL A' B'` | A'∧B' /= A | A'∧B' ∈ Γ₀, recurse on d' (widened context) |
| `andR A' B'` | N/A (right rule) | Recurse on both sub-proofs |
| `orL A' B'` | A'∨B' = A | Recurse on sub-proofs, build d₂_new, switch to ljCutAdm_left |
| `orL A' B'` | A'∨B' /= A | A'∨B' ∈ Γ₀, recurse on sub-proofs |
| `orR1 A' B'` | N/A (right rule) | Recurse on sub-proof |
| `orR2 A' B'` | N/A (right rule) | Recurse on sub-proof |
| `impL A' B'` | A'→B' = A | Recurse on sub-proofs, build d₂_new, switch to ljCutAdm_left |
| `impL A' B'` | A'→B' /= A | A'→B' ∈ Γ₀, recurse on sub-proofs |
| `impR A' B'` | N/A (right rule) | Recurse on sub-proof (context extended with A') |
| `weakL A'` | N/A | Recurse with narrowed subset |
| `cut` | N/A | Impossible (hcf₂ = False) |

### ljCutAdm_left Cases (structural on d₁)

| d₁ last rule | Principal? | Action |
|--------------|-----------|--------|
| `ax phi` | phi = A | A ∈ Γ₀ (from subset), d₂ weakened via mono |
| `ax phi` | N/A (always A) | A ∈ Γ ⊆ Γ₀, weaken d₂ |
| `botL` | N/A | bot ∈ Γ₀, construct botL directly |
| `andL A' B'` | N/A (left rule, not introducing A) | Widen d₂ context, recurse on d' |
| `andR P Q` | YES: A = P∧Q | Delegate to ljCutAdm_principal_andR |
| `orL A' B'` | N/A (left rule) | Recurse on both sub-proofs |
| `orR1 P Q` | YES: A = P∨Q | Delegate to ljCutAdm_principal_or (left disjunct) |
| `orR2 P Q` | YES: A = P∨Q | Delegate to ljCutAdm_principal_or (right disjunct) |
| `impL A' B'` | N/A (left rule) | Recurse on both sub-proofs |
| `impR P Q` | YES: A = P→Q | Delegate to ljCutAdm_principal_impR |
| `weakL A'` | N/A | Recurse with narrowed subset |
| `cut` | N/A | Impossible (hcf₁ = False) |

Note: for `andR`, `orR1`, `orR2`, `impR` in ljCutAdm_left, these ARE always principal
because d₁ concludes A, and these rules introduce A on the right. There is no
non-principal variant for right-introduction rules in the left analysis.

## Termination Arguments

### Standalone Helpers

Each standalone helper terminates by structural recursion on `d₂` (measured by `sizeOf d₂`).
This is the same as LK. The `termination_by sizeOf d₂` annotation should suffice.

### Mutual Block

- `ljCutAdm_right` is structurally recursive on `d₂`. Calls to `ljCutAdm_left` pass
  a reconstructed `d₂_new` (same or smaller size) along with `d₁` at the same size.
  Termination is by `sizeOf d₂` within the mutual block.
- `ljCutAdm_left` is structurally recursive on `d₁`. Calls to standalone helpers
  pass `d₂` (external to the mutual block). Calls to `ljCutAdm_right` pass sub-proofs
  of `d₁` (smaller) along with `d₂`.

The mutual termination measure is `sizeOf d₂ + sizeOf d₁` (or a suitable joint measure).
However, Lean 4's mutual recursion checker should accept this with appropriate
`termination_by` annotations since each function decreases on its primary argument.

### Top-Level

`cutAdmissibility` terminates by `sizeOf A` (well-founded on Nat). The `ih` closure
only calls `cutAdmissibility` on formulas `B` with `sizeOf B < sizeOf A`.

## Finset Lemmas Required

The following Finset lemmas are used extensively (all available in Mathlib):

| Lemma | Usage |
|-------|-------|
| `Finset.mem_insert` | Branch on `x ∈ insert a s` |
| `Finset.mem_of_mem_insert_of_ne` | Extract `x ∈ s` from `x ∈ insert a s` and `x /= a` |
| `Finset.subset_insert` | `s ⊆ insert a s` |
| `Finset.insert_subset_insert` | Lift subset through insert |
| `Finset.insert_subset` | `insert a s ⊆ t` from `a ∈ t` and `s ⊆ t` |
| `Finset.mem_insert_self` | `a ∈ insert a s` |
| `Finset.mem_insert_of_mem` | `x ∈ s → x ∈ insert a s` |
| `Finset.Subset.refl` | `s ⊆ s` |

Additionally, the LK module defines `mem_of_ne_head` as a convenience wrapper;
the LJ module should define its own copy or import it.

## Heartbeat Considerations

The LK mutual block uses `set_option maxHeartbeats 200000`. For LJ:
- Fewer cases overall (no weakR, no succedent membership proofs)
- Simpler subset management (antecedent only)
- Estimated: 200000 should be sufficient for the mutual block
- Standalone helpers: default heartbeats should suffice (they are simpler than LK's
  due to no succedent Finset management)

The LK proof originally required 800000 heartbeats before the standalone helpers
were extracted. Extracting helpers halved this to 200000. The same extraction
strategy is recommended for LJ.

## Estimated Implementation Effort

| Component | Lines (est.) | Complexity |
|-----------|-------------|------------|
| `LJCutIH` type alias | 5 | Trivial |
| `ljCutAdm_principal_andR` | 60-80 | Medium (follows LK pattern) |
| `ljCutAdm_principal_or` | 60-80 | Medium (two disjunct variants) |
| `ljCutAdm_principal_impR` | 60-80 | Medium (follows LK pattern) |
| Mutual block (`ljCutAdm_right` + `ljCutAdm_left`) | 150-200 | High (many cases) |
| Top-level `cutAdmissibility` | 5-10 | Trivial |
| Helper lemmas (`mem_of_ne_head` etc.) | 10-15 | Trivial |
| **Total** | **350-470** | |

## Risk Assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Heartbeat overflow in mutual block | Medium | Extract all principal cases to standalone helpers |
| Finset equation failure in pattern matching | Medium | Use generic-sequent parameters (as LK does) |
| Termination checker rejection | Low | The LK pattern has proven termination measures |
| `noncomputable` propagation | None | Already declared `noncomputable` |
| or case complexity (orR1/orR2 split) | Low | Handle as two separate calls to a unified helper |

## Recommendation

**Approach**: Direct adaptation of the LK cut elimination architecture to single-conclusion
sequents. The proof follows the same decomposition (standalone principal helpers +
mutual structural recursion + WF top-level) with the following simplifications:

1. Remove all succedent-related code (no `hsuc`, no `Δ`, no `weakR` cases)
2. Remove all right-side membership proofs from constructor calls
3. Replace `orR` with `orR1`/`orR2` handling
4. Simplify `impL` left sub-proof (single conclusion `A`, not `insert A Δ`)

The LK code at `LK/CutElimination.lean` (lines 96-942) serves as a direct template.
Each LK function maps to an LJ analogue with the structural simplifications above.

**No blockers identified.** The proof is technically challenging but follows a
well-established pattern that has already been verified in the LK module. The
key mathematical content (double induction on formula size and proof height) is
identical; only the Lean encoding differs due to the single-conclusion constraint.

## References

- Negri, S. and von Plato, J. (2001). *Structural Proof Theory*. Theorem 2.4.3.
- Troelstra, A.S. and Schwichtenberg, H. (2000). *Basic Proof Theory*. Theorem 4.1.1.
- CSLib LK cut elimination: `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean`
