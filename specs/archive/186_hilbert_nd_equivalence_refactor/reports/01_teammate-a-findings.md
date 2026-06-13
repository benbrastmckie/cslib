# Teammate A: Primary Approach — Context-Based Equivalence

## Summary

The infrastructure for full context-based equivalence is almost entirely in place. The
`hilbert_to_nd_deriv` and `nd_to_hilbert_deriv` theorems already handle arbitrary
contexts. The only gaps are: (1) a missing top-level `hilbert_iff_nd_ctx` theorem
wrapping the context-based iff, (2) a missing minimal-logic corollary that drops the
`h_EFQ` parameter, and (3) a documentation update to `Defs.lean` which still describes
the bridge as "extensional equivalence" (closed-context only).

---

## Key Findings

### Finding 1: Context-aware lemmas already exist

Both directions of the bridge are already proven at the context level:

- `hilbert_to_nd_deriv` (line 132–139 of `Equivalence.lean`):
  ```
  {Γ : List (PL.Proposition Atom)} {φ}
  (h : Deriv Axioms Γ φ) :
  DerivableIn (AxiomTheory Axioms) ((Γ.toFinset : Ctx Atom) ⊢ φ)
  ```
- `nd_to_hilbert_deriv` (line 219–236 of `Equivalence.lean`):
  ```
  {Γ : Ctx Atom} {φ}
  (h : DerivableIn (AxiomTheory Axioms) ((Γ : Ctx Atom) ⊢ φ)) :
  Deriv Axioms Γ.toList φ
  ```

These already cross the List/Finset boundary. The gap is purely at the top-level iff
theorem, which currently only states the empty-context (`Derivable`) version.

### Finding 2: The canonical statement form

The canonical statement taking Finset as primary (matching the ND system's native type)
is:

```lean
theorem hilbert_iff_nd_ctx {Axioms} {Γ : Ctx Atom} {φ} ... :
    Deriv Axioms Γ.toList φ ↔ DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)
```

This form is preferable because:
- It avoids `Γ.toFinset.toList ≠ Γ` problems (we never go `Finset → List → Finset`)
- The ND side naturally produces `Finset` contexts, and `Γ.toFinset.toList` would
  introduce spurious reordering/dedup issues
- `Γ.toList` on a `Finset Γ` followed by `List.toFinset` is trivially `Γ` (round-trip
  in this direction is identity by `List.toFinset_toList`)
- The closed-context corollary `hilbert_iff_nd` follows by specialising to `Γ = ∅`
  since `(∅ : Ctx Atom).toList = []`

### Finding 3: Proof by direct composition

The proof of `hilbert_iff_nd_ctx` reduces to exactly:
```lean
constructor
· intro h
  exact hilbert_to_nd_deriv h  -- needs: Γ.toFinset.toList = Γ.toList... wait
```

Wait — there is a type mismatch to inspect. `hilbert_to_nd_deriv` takes
`Deriv Axioms Γ φ` with `Γ : List` and produces `DerivableIn ... ((Γ.toFinset) ⊢ φ)`.
But `hilbert_iff_nd_ctx` starts from `Deriv Axioms Γ.toList φ` where `Γ : Ctx Atom =
Finset`. So the forward direction needs:

```
  exact hilbert_to_nd_deriv h  -- h : Deriv Axioms Γ.toList φ
  -- produces: DerivableIn ... (Γ.toList.toFinset ⊢ φ)
  -- need:     DerivableIn ... (Γ ⊢ φ)
  -- bridge:   Finset.toList_toFinset : Γ.toList.toFinset = Γ
```

This is the one non-trivial step: we need `Finset.toList_toFinset` (or equivalent) to
rewrite `Γ.toList.toFinset` back to `Γ`.

The key lemma is:
```lean
-- In Mathlib: Finset.toList_toFinset
theorem Finset.toList_toFinset {α} [DecidableEq α] (s : Finset α) :
    s.toList.toFinset = s
```

Once we have this, the forward direction is:
```lean
· intro h
  have := hilbert_to_nd_deriv h
  rwa [Finset.toList_toFinset] at this
```

The backward direction is `nd_to_hilbert_deriv h_K ... h_EFQ ... h` directly.

### Finding 4: The existing `hilbert_iff_nd` is subsumed

The current closed theorem:
```lean
theorem hilbert_iff_nd ... {φ} :
    Derivable Axioms φ ↔ DerivableIn (AxiomTheory Axioms) ((∅ : Ctx Atom) ⊢ φ)
```

This is derivable from `hilbert_iff_nd_ctx` by specialising `Γ := ∅`:
- `(∅ : Ctx Atom).toList = []`
- `Deriv Axioms [] φ = Derivable Axioms φ`

So `hilbert_iff_nd` can be a one-line corollary of `hilbert_iff_nd_ctx`. Currently it
has a self-contained proof; the refactor should replace it.

### Finding 5: The minimal logic case — no EFQ needed

The key question is whether `ndToHilbert` can drop `h_EFQ`. Looking at the ND
constructors:

- `Theory.Derivation` has no `botE` as a primitive constructor.
- `botE` is a **derived rule** in `DerivedRules.lean`, and it requires `[IsIntuitionistic T]`.
- For `AxiomTheory MinPropAxiom`, there is no EFQ axiom, so `IsIntuitionistic` does not hold.
- The ND derivation under `AxiomTheory MinPropAxiom` genuinely cannot use `botE` (it's blocked
  by the typeclass guard).

This means: if we have a `Theory.Derivation (AxiomTheory MinPropAxiom) Γ φ`, the proof
term never contains a `botE` node (since `botE` requires `[IsIntuitionistic T]` which
`AxiomTheory MinPropAxiom` does not satisfy). Therefore `ndToHilbert` does not actually
use `h_EFQ` when translating a minimal-logic derivation.

However, `ndToHilbert` currently takes `h_EFQ` as an explicit parameter regardless
(because it's written generically). Two options:

**Option A (minimal refactor)**: Keep `ndToHilbert` with all 9 parameters. The minimal
corollary instantiates with any proof of `MinPropAxiom (⊥ → φ)` — but `MinPropAxiom`
has no `efq` constructor! So we cannot produce `h_EFQ` for `MinPropAxiom`. This means
we cannot use the current `nd_to_hilbert_deriv` / `ndToHilbert` for minimal logic as-is.

**Option B (split ndToHilbert)**: Create `ndToHilbertMin` that does not take `h_EFQ`
(and does not handle `botE` nodes, since they cannot appear for `MinPropAxiom`). The
type `Theory.Derivation (AxiomTheory MinPropAxiom) Γ φ` structurally cannot contain
a `botE` — but since `botE` is a *derived rule* (not a constructor), it simply unfolds
to `impE (ax ...) d`. So actually any derivation under `AxiomTheory MinPropAxiom` that
uses `botE` would require the `ax` case to provide `IsIntuitionistic.efq A ∈
AxiomTheory MinPropAxiom`, which fails. Since the ND type system prevents this at
typeclass resolution time, there is no case to handle.

**Option C (cleanest)**: Parameterize `ndToHilbert` differently. Notice that the only
use of `h_EFQ` in `ndToHilbert` is... none directly! Look at the match arms:
`botE` is not a constructor of `Theory.Derivation`; it is a derived rule that expands
to `impE (ax ...) (...)`. So the `ax` arm handles it: `ax h_mem` where `h_mem` is
membership in the theory. When the theory is `AxiomTheory MinPropAxiom`, membership
means `MinPropAxiom φ`. There is no `MinPropAxiom.efq` constructor, so the `ax` arm
receives `MinPropAxiom.andI ...` etc. The `ndToHilbert` function's `ax` arm correctly
handles this by constructing `.ax ... h_mem`. 

**Key insight**: `h_EFQ` in `ndToHilbert` is only used in the `impI` case, which calls
`deductionTheorem`. The deduction theorem only needs `h_K` and `h_S`. The `h_EFQ`
parameter in `ndToHilbert` is actually **never used** in any match arm!

Let me re-examine... Looking at `ndToHilbert` in `Equivalence.lean` lines 157–215:
- `.ax h_mem` → uses nothing (constructs axiom node)
- `.ass h_mem` → uses nothing
- `.andI` → calls recursive `ndToHilbert` (passes all params), then `hilbertAndI h_andI`
- `.andE1` → similar
- `.andE2` → similar
- `.orI1` → similar
- `.orI2` → similar
- `.orE` → calls `ndToHilbert` recursively, then `hilbertOrE h_K h_S h_orE`
- `.impE` → modus ponens, no params
- `.impI` → calls `ndToHilbert` recursively, then `deductionTheorem h_K h_S`

The `h_EFQ` parameter is passed through recursive calls but never **consumed** directly.
This is because `botE` is not a constructor — it expands to `impE (ax ...) (...)` and
the `ax` arm handles the `MinPropAxiom (⊥ → A)` membership test, which fails for
`MinPropAxiom` but succeeds for `IntPropAxiom`/`PropositionalAxiom`. In the EFQ case
for int/cl logic, the `ax h_mem` arm constructs the Hilbert `ax` node directly, not
through `h_EFQ`.

**Conclusion**: `h_EFQ` in `ndToHilbert` is entirely redundant — it is passed through
but never used! This is a defect to fix.

### Finding 6: The minimal corollary is easy

Since `h_EFQ` is unused in `ndToHilbert`, we can add a version without it. More
precisely, the refactor should:

1. Remove `h_EFQ` from `ndToHilbert` and `nd_to_hilbert_deriv` (it's unused).
2. This allows `hilbert_iff_nd` to also drop `h_EFQ`.
3. A minimal corollary `hilbert_iff_nd_min` can then be stated.

After the EFQ removal, the axiom witness list for `ndToHilbert` goes from 9 to 8:
`h_K`, `h_S`, `h_andI`, `h_andE1`, `h_andE2`, `h_orI1`, `h_orI2`, `h_orE`.

### Finding 7: The toList/toFinset round-trip

The critical Mathlib lemmas we need:

```lean
-- Finset.toList_toFinset (DecidableEq required)
Finset.toList_toFinset : ∀ {α} [DecidableEq α] (s : Finset α), s.toList.toFinset = s
```

This makes the forward direction of `hilbert_iff_nd_ctx` trivial via `rwa`.

---

## Recommended Approach

### Step 1: Remove `h_EFQ` from `ndToHilbert`

Remove the `h_EFQ` parameter from `ndToHilbert`, `nd_to_hilbert_deriv`, and all
callers. This is a pure cleanup — the parameter is provably unused.

To verify: add `exact h_EFQ` as the first line of each match arm and observe that Lean
reports it unused in every single arm. (The `andI`, `andE2`, `orI1`, `orI2`, `orE`,
`impI` arms all pass it recursively but no arm uses it at the leaf level for
`botE`-related purposes because `botE` is not a constructor.)

### Step 2: Add `hilbert_iff_nd_ctx`

```lean
/-- **Context-based generic equivalence**: Γ ⊢_Hilbert φ iff Γ ⊢_ND φ.

The context on the Hilbert side is `Γ.toList` and on the ND side is `Γ`.
This is the stronger form of `hilbert_iff_nd` (which is the empty-context special case). -/
theorem hilbert_iff_nd_ctx
    {Axioms : PL.Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (ψ.imp (φ.and ψ))))
    (h_andE1 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp φ))
    (h_andE2 : ∀ (φ ψ : PL.Proposition Atom), Axioms ((φ.and ψ).imp ψ))
    (h_orI1 : ∀ (φ ψ : PL.Proposition Atom), Axioms (φ.imp (φ.or ψ)))
    (h_orI2 : ∀ (φ ψ : PL.Proposition Atom), Axioms (ψ.imp (φ.or ψ)))
    (h_orE : ∀ (φ ψ χ : PL.Proposition Atom),
      Axioms ((φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))))
    {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv Axioms Γ.toList φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom) ((Γ : Ctx Atom) ⊢ φ) := by
  constructor
  · intro h
    have := hilbert_to_nd_deriv h
    rwa [Finset.toList_toFinset] at this
  · intro h
    exact nd_to_hilbert_deriv h_K h_S h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h
```

Note: `Finset.toList_toFinset` rewrites `(Γ.toList).toFinset = Γ`, so `rwa` closes the
goal after applying `hilbert_to_nd_deriv`.

### Step 3: Refactor `hilbert_iff_nd` as a corollary

```lean
theorem hilbert_iff_nd ... {φ} :
    Derivable Axioms φ ↔ DerivableIn (AxiomTheory Axioms) ((∅ : Ctx Atom) ⊢ φ) := by
  have := @hilbert_iff_nd_ctx ... (∅ : Ctx Atom) φ
  simp [Finset.toList_empty, Derivable, Deriv] at this
  exact this
```

Or more precisely: `Derivable Axioms φ = Deriv Axioms [] φ` and
`(∅ : Ctx Atom).toList = []`, so `hilbert_iff_nd` is exactly
`hilbert_iff_nd_ctx` at `Γ = ∅` with `Finset.toList_empty : (∅ : Finset α).toList = []`.

### Step 4: Add corollaries for min, int, cl

```lean
/-- Minimal equivalence: Hilbert + MinPropAxiom iff ND + AxiomTheory MinPropAxiom (context). -/
theorem hilbert_iff_nd_ctx_min {Γ : Ctx Atom} {φ} :
    Deriv MinPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom)) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)

/-- Intuitionistic equivalence (context-based). -/
theorem hilbert_iff_nd_ctx_int {Γ : Ctx Atom} {φ} :
    Deriv IntPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@IntPropAxiom Atom)) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)

/-- Classical equivalence (context-based). -/
theorem hilbert_iff_nd_ctx_cl {Γ : Ctx Atom} {φ} :
    Deriv PropositionalAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom)) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
```

Also keep the old closed-context `hilbert_iff_nd_int` and `hilbert_iff_nd_cl` for
backward compatibility, but make them corollaries of the context versions.

### Step 5: Update the module docstring

Update the `/-! # Equivalence ... -/` header to describe the context-based versions as
primary, and the closed-context versions as corollaries. Update `Defs.lean` which says
"extensional equivalence" to say "context-based extensional equivalence".

---

## Evidence: Forward Direction Requires `Finset.toList_toFinset`

The key dependency is:

```lean
#check @Finset.toList_toFinset
-- Finset.toList_toFinset : {α : Type u_1} → [inst : DecidableEq α] →
--   (s : Finset α) → s.toList.toFinset = s
```

Instantiating with `Γ : Finset (PL.Proposition Atom)` and using the existing `DecidableEq`
instance (from `[DecidableEq Atom]` and `DecidableEq (Proposition Atom)` from `deriving`),
this gives `Γ.toList.toFinset = Γ` exactly what is needed.

The existing `hilbert_iff_nd` proof (lines 264–268) already uses `List.toFinset_nil`
for the empty-context case:
```lean
  rwa [List.toFinset_nil] at this
```

The context-based version uses the analogous `Finset.toList_toFinset`:
```lean
  rwa [Finset.toList_toFinset] at this
```

---

## Evidence: `h_EFQ` Redundancy in `ndToHilbert`

Examining all 10 match arms in `ndToHilbert` (lines 173–215 of `Equivalence.lean`):

| Arm | Uses `h_EFQ`? | Evidence |
|-----|---------------|---------|
| `.ax h_mem` | No | Constructs `.ax ... h_mem` directly |
| `.ass h_mem` | No | Constructs `.assumption ...` directly |
| `.andI` | No (recursive only) | Calls `ndToHilbert ...` then `hilbertAndI h_andI` |
| `.andE1` | No (recursive only) | Calls `ndToHilbert ...` then `hilbertAndE1 h_andE1` |
| `.andE2` | No (recursive only) | Similar |
| `.orI1` | No (recursive only) | Similar |
| `.orI2` | No (recursive only) | Similar |
| `.orE` | No (recursive only) | Calls `hilbertOrE h_K h_S h_orE` |
| `.impE` | No (recursive only) | Builds `.modus_ponens` |
| `.impI` | No (recursive only) | Calls `deductionTheorem h_K h_S` |

`botE` does not appear as a constructor because it is a derived rule (not in the
`Theory.Derivation` inductive). The EFQ case in ND derivations using int/cl logic
arrives as `.ax h_mem` where `h_mem : (⊥ → φ) ∈ AxiomTheory IntPropAxiom`, handled
by the `ax` arm without needing `h_EFQ`.

---

## Theorem Architecture (Final Proposal)

Listed in dependency order:

1. `hilbertToND` (existing, no change)
2. `ndToHilbert` (remove `h_EFQ` parameter — it's unused)
3. `hilbert_to_nd_deriv` (existing, no change)
4. `nd_to_hilbert_deriv` (remove `h_EFQ` parameter)
5. **NEW** `hilbert_iff_nd_ctx` — generic context-based iff (8 axiom witnesses)
6. `hilbert_iff_nd` — refactor as corollary of (5) at `Γ = ∅`
7. **NEW** `hilbert_iff_nd_ctx_min` — minimal instantiation of (5)
8. **NEW** `hilbert_iff_nd_ctx_int` — intuitionistic instantiation of (5)
9. **NEW** `hilbert_iff_nd_ctx_cl` — classical instantiation of (5)
10. `hilbert_iff_nd_int` — refactor as corollary of (8) at `Γ = ∅`
11. `hilbert_iff_nd_cl` — refactor as corollary of (9) at `Γ = ∅`

---

## Docstring Update for `Equivalence.lean`

The `## Main Definitions` and `## Main Results` sections should be updated to list
`hilbert_iff_nd_ctx` as the primary theorem and the closed-context versions as
corollaries.

The `Defs.lean` docstring says:
> **Bridge**: `NaturalDeduction/Equivalence.lean` establishes extensional equivalence
> between the two proof systems for all three logic strengths.

This should be updated to:
> **Bridge**: `NaturalDeduction/Equivalence.lean` establishes context-based extensional
> equivalence `Γ ⊢_Hilbert φ ↔ Γ ⊢_ND φ` between the two proof systems for all three
> logic strengths, with closed-context derivability as a corollary.

---

## Confidence Level

**Very high** (>95%) that:
- `h_EFQ` is genuinely unused in `ndToHilbert` (structural argument: `botE` is not a
  constructor, so no match arm can pattern-match on it)
- `Finset.toList_toFinset` is the correct bridge lemma for the forward direction
- The theorem statement `Deriv Axioms Γ.toList φ ↔ DerivableIn ... (Γ ⊢ φ)` is
  the correct canonical form with `Γ : Ctx Atom = Finset`
- The proofs are one-line applications of existing lemmas

**Moderate** (80%) that Lean accepts the `rwa [Finset.toList_toFinset]` rewrite
directly without additional simp lemmas about `Sequent`/`DerivableIn` unfolding.
The sequent `(Γ ⊢ φ)` is notation for `(⟨Γ, φ⟩ : Sequent)`, and `DerivableIn T (Γ ⊢ φ)`
is definitionally `T.Derivation Γ φ`, so the rewrite should go through. If not,
`simp [Finset.toList_toFinset]` or `convert` will close it.

---

## Files to Modify

1. `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
   - Remove `h_EFQ` from `ndToHilbert` and `nd_to_hilbert_deriv`
   - Add `hilbert_iff_nd_ctx`
   - Refactor `hilbert_iff_nd`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` as corollaries
   - Add `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`
   - Update module docstring

2. `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Defs.lean`
   - Update Bridge description in docstring (one line)
