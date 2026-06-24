# Cut Elimination Rewrite Research Report

Task: 314 -- LK Classical Sequent Calculus
Session: sess_1782245580_188995_314
Agent: cslib-research-hard-agent
Reference Grounding Tier: 1 (literature-backed)

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [TroelstraSchwichtenberg2000] | Theorem 4.1.5, p. 93 | `Cslib.Logic.PL.cutAdmissibility` | `(A : Proposition Atom) -> ... -> CutFreeLKProof (G ⊢s D)` | blocked (rewrite needed) |
| [TroelstraSchwichtenberg2000] | Definition 4.1.1, p. 92 | `Cslib.Logic.PL.LKProof.height` | `LKProof seq -> Nat` | transcribed |
| [TroelstraSchwichtenberg2000] | Corollary (cut elim) | `Cslib.Logic.PL.LKProof.cutElim` | `LKProof seq -> Nonempty (CutFreeLKProof seq)` | pending |
| [NegriVonPlato2001*] | Theorem 3.2.3, p. 54 | `Cslib.Logic.PL.cutAdmissibility` | (same as above) | blocked (rewrite needed) |
| [NegriVonPlato2001*] | Theorem 3.2.1, p. 53 | `Cslib.Logic.PL.LKProof.mono` | `LKProof (G ⊢s D) -> LKProof (G' ⊢s D')` | transcribed |
| [NegriVonPlato2001*] | Theorem 3.2.2, p. 53 | (height-pres. contraction) | (not needed for G3cp-style) | not applicable |

*NegriVonPlato2001 BibKey is NOT in `references.bib` -- needs to be added.

## BibKey Verification

- `TroelstraSchwichtenberg2000`: **Verified** at line 811 of `references.bib`.
- `NegriVonPlato2001`: **NOT FOUND** in `references.bib`. The file references this source via `[NegriVonPlato2001]` in docstrings but the BibKey entry is missing. Must be added before PR.

## Findings

### 1. Root Cause Analysis of Build Failures

The current `CutElimination.lean` (873 lines) has approximately 100 build errors. These stem from three interconnected architectural problems, all relating to how Lean 4 handles dependent elimination on `Finset` (a quotient type).

**Problem A: Dependent elimination on Finset indices fails.**

When the tactic `cases d₂_raw` is applied where `d₂_raw : LKProof (insert A Gamma ⊢s Delta)`, Lean needs to solve equations of the form:

```
Quot.lift (fun l => (List.insert A l)) ... Gamma.val
  = Quot.lift (fun l => (List.insert B l)) ... Gamma'.val
```

This equation involves quotient internals that Lean's equation solver cannot handle. The error message is: "Dependent elimination failed: Failed to solve equation." This is confirmed by minimal reproduction: any `cases` on an inductive indexed by a `Finset` with `insert` in the index triggers this failure, regardless of whether the target type is `Type` or `Prop`.

This affects EVERY case where the proof does `cases d₂_raw` after destructuring `d₂ : CutFreeLKProof (insert A Gamma ⊢s Delta)` -- which is the inner induction on the right proof in every compound formula case (imp, and, or).

**Problem B: CutFree preservation through mono.**

The code writes `⟨d₁a.mono ... , hd₁.1⟩` but `hd₁.1 : CutFree d₁a`, while the anonymous constructor needs `CutFree (d₁a.mono ...)`. These are not definitionally equal. The fix is to use `CutFree.mono` (which already exists and builds successfully) instead of passing `hd₁.1` directly.

**Problem C: Finset.insert commutativity.**

`insert A (insert B S)` is not definitionally equal to `insert B (insert A S)`. The existing code uses `Finset.insert_comm A B S ▸ Finset.Subset.refl _` as a transport, which works in SOME positions but fails in others where the rewrite target is inside a structure constructor. The fix is to use `LKProof.mono` with appropriate subset proofs instead of direct rewriting.

### 2. Why `LKProof.mono` Works But `cutAdmissibility` Fails

`LKProof.mono` is defined as a term-mode recursive `def` that pattern-matches on `(d : LKProof (Gamma ⊢s Delta))` where `Gamma` and `Delta` are FREE implicit variables:

```lean
def LKProof.mono {Gamma Delta Gamma' Delta'} (hL : Gamma ⊆ Gamma') (hR : Delta ⊆ Delta') :
    LKProof (Gamma ⊢s Delta) -> LKProof (Gamma' ⊢s Delta')
  | .ax A _ _ hA hB => ...
  | .weakL A d => ...
```

When Lean matches `.weakL A d : LKProof (insert A Gamma_inner ⊢s Delta_inner)` against the function parameter `LKProof (Gamma ⊢s Delta)`, it simply unifies `Gamma = insert A Gamma_inner`. This works because `Gamma` is a free variable.

In contrast, `cutAdmissibility` passes `d₂ : CutFreeLKProof (insert cutF Gamma ⊢s Delta)` where `insert cutF Gamma` is a STRUCTURED expression, not a free variable. When `cases d₂_raw` tries to match `.weakL B d' : LKProof (insert B Gamma' ⊢s Delta')`, Lean must solve `insert cutF Gamma = insert B Gamma'`, which is a Finset quotient equation that fails.

### 3. Recommended Architecture: Generic-Sequent Helper Pattern

The solution is to define the inner case analysis as a helper function that takes its proof argument with a FREE (universally quantified) sequent parameter, then invoke it with the specific structured sequent:

```lean
-- Helper: generic sequent parameter (seq is FREE)
private noncomputable def cutAdmissibility_left
    (A : Proposition Atom) (Gamma0 Delta0 : Finset (Proposition Atom))
    (d2 : CutFreeLKProof (insert A Gamma0 ⊢s Delta0))
    {seq1 : LKSequent Atom} (d1_raw : LKProof seq1)
    (hcf1 : CutFree d1_raw)
    (hant : seq1.ant = Gamma0) (hsuc : seq1.suc = insert A Delta0) :
    CutFreeLKProof (Gamma0 ⊢s Delta0) :=
  match d1_raw with
  | .ax phi _G _D hphiL hphiD => ...  -- works: _G and _D are unified with seq1 fields
  | .weakL B d1' => ...                -- works: seq1.ant = insert B G' (free unification)
  ...
```

The caller invokes:
```lean
cutAdmissibility_left A Gamma Delta d2 d1.1 d1.2 rfl rfl
```

This pattern works because:
1. `{seq1 : LKSequent Atom}` is a free variable during pattern matching.
2. Lean unifies constructor outputs with `seq1` freely (no Finset equations).
3. The `hant`/`hsuc` proof obligations connect the generic sequent to the specific one.
4. After matching, `hant` and `hsuc` provide the equalities needed to construct the result.

This is confirmed by successful compilation of a minimal reproduction (see test in research session).

### 4. Recommended Return Type

Two options were investigated:

**Option A: Return `CutFreeLKProof (Gamma ⊢s Delta)` (Type)**
- Pro: No `Classical.choice` needed; recursive calls produce values directly.
- Pro: `if heq : phi = A then ... else ...` (DecidableEq) works for Type targets.
- Con: Cannot use `rcases` on `Or` (e.g., `Finset.mem_insert`); must use `if` instead.
- Con: More complex CutFree evidence threading.

**Option B: Return `Nonempty (CutFreeLKProof (Gamma ⊢s Delta))` (Prop)**
- Pro: Can use `rcases` on `Or` freely inside the proof.
- Con: Still suffers dependent elimination failure on Finset (tested and confirmed).
- Con: Recursive calls require `Classical.choice` for extraction; `noncomputable`.

**Recommendation: Option A (Type return) with DecidableEq-based branching.**

The `Nonempty` approach does NOT fix the dependent elimination problem (tested), so it provides no advantage. The DecidableEq-based branching (`if heq : phi = A then ... else ...`) already works correctly for Type targets and is already used in the existing (broken) code. The real fix is the generic-sequent helper pattern, not the return type.

For `cutElim` (the final theorem), use `Nonempty` as the LJ file does:
```lean
theorem LKProof.cutElim : LKProof seq -> Nonempty (CutFreeLKProof seq)
```
This works because `cutElim` uses structural induction on the proof tree (no `insert` in the index during matching), and `Nonempty` allows clean `obtain` patterns.

### 5. Induction/Termination Strategy

**Literature strategy**: [TroelstraSchwichtenberg2000] Theorem 4.1.5, p. 93 uses a main induction on cut rank (formula complexity) with a sub-induction on level (height sum). [NegriVonPlato2001] Theorem 3.2.3, p. 54 uses the same structure.

**Recommended Lean 4 strategy**: Structural recursion on the formula `A` (via `match A with`) combined with well-founded recursion via `termination_by`.

The formula `Proposition Atom` has five constructors: `atom`, `bot`, `imp`, `and`, `or`. For the atom and bot cases, the proof proceeds by induction on d₁ only (structural recursion). For compound cases (imp, and, or), the non-principal subcases recurse on `A` (same formula, smaller proof), and the principal subcases recurse on strict subformulas.

Termination measure options:
1. **`sizeOf A`** alone -- sufficient if non-principal subcases are handled via `mono` + weakening rather than explicit recursion on height.
2. **Lexicographic `(sizeOf A, d₁.height + d₂.height)`** -- needed if non-principal subcases require height decrease.

For the generic-sequent helper approach, option (1) is viable: the non-principal subcases use `cutAdmissibility_left` recursively with the SAME formula `A` but pass it through the generic helper which matches on the proof structure without explicit height tracking. The key observation from [NegriVonPlato2001] (G3cp presentation): in the all-additive formulation, non-principal subcases can be handled by a single recursive call with the same cut formula on a subproof, and the recursion terminates because the proof tree is structurally smaller.

However, the generic-sequent helper complicates the structural recursion story because the proof arguments are not direct subterms. The recommended approach:

```lean
noncomputable def cutAdmissibility
    (A : Proposition Atom) (Gamma Delta : Finset (Proposition Atom))
    (d1 : CutFreeLKProof (Gamma ⊢s insert A Delta))
    (d2 : CutFreeLKProof (insert A Gamma ⊢s Delta)) :
    CutFreeLKProof (Gamma ⊢s Delta) := by
  match A with
  | .atom x => exact cutAdm_atom x Gamma Delta d1 d2
  | .bot => exact cutAdm_bot Gamma Delta d1 d2
  | .imp phiA phiB =>
    exact cutAdm_imp phiA phiB Gamma Delta d1 d2
      (fun A' _ G D d1' d2' => cutAdmissibility A' G D d1' d2')
  | .and phiA phiB => ...
  | .or phiA phiB => ...
termination_by sizeOf A
```

Where `cutAdm_imp` takes a "continuation" for recursive calls on subformulas, and the `termination_by sizeOf A` handles well-foundedness.

For the atom/bot base cases, `cutAdm_atom` and `cutAdm_bot` use the generic-sequent helper pattern to match on `d₁` without Finset equation issues. These are structural (no recursion on formula).

### 6. CutFree: Recursive def vs Inductive

The current `CutFree` is a recursive `def`:
```lean
def CutFree : LKProof seq -> Prop
  | .cut _ _ _ => False
  | .andR _ _ _ d1 d2 => CutFree d1 ∧ CutFree d2
  | ...
```

**Should it be an inductive?** No. Making it an inductive would:
- Allow anonymous constructor `⟨...⟩` syntax (slight convenience).
- BUT: require an inductive predicate with 11 constructors mirroring LKProof.
- Not solve any of the three fundamental problems identified above.
- Add maintenance burden (two parallel inductive types).

The recursive `def` approach works correctly. The anonymous constructor issue (`⟨_, _⟩` fails on `CutFree` goals) is minor and can be worked around by explicitly providing the evidence:
- For one-subproof rules: provide `hcf` directly (it IS the CutFree evidence).
- For two-subproof rules: provide `⟨hcf₁, hcf₂⟩` which constructs `And`.
- Use `CutFree.mono` for threading CutFree evidence through `LKProof.mono`.

### 7. Finset.insert Commutativity Strategy

`Finset.insert_comm` provides: `insert a (insert b s) = insert b (insert a s)`.

The recommended strategy:
1. **Primary**: Use `LKProof.mono` with subset proofs to move between contexts. Since `mono` already works, this avoids direct rewriting of Finset expressions.
2. **When direct rewriting is needed**: Use `Finset.insert_comm a b s ▸ expr` for simple cases.
3. **For subset proofs**: `Finset.insert_subset_insert _ (Finset.subset_insert _ _)` and similar combinators, which are already used successfully in the existing code.
4. **Avoid**: Using `simp [Finset.insert_comm]` as it can loop or fail to terminate.

### 8. Changes Needed to Basic.lean

No changes to the definitions in `Basic.lean` are needed. Specifically:
- `LKProof` inductive: correct as-is.
- `CutFree` recursive def: correct as-is.
- `CutFreeLKProof` subtype: correct as-is.
- `LKProof.mono`: correct and building.
- `CutFree.mono`: correct and building.
- `CutFreeLKProof.mono`: correct and building.

### 9. Concrete Code Sketch: Atom Case

```lean
/-- Cut admissibility for atomic cut formula. -/
private noncomputable def cutAdm_atom
    (x : Atom) (Gamma Delta : Finset (Proposition Atom))
    (d1 : CutFreeLKProof (Gamma ⊢s insert (.atom x) Delta))
    (d2 : CutFreeLKProof (insert (.atom x) Gamma ⊢s Delta)) :
    CutFreeLKProof (Gamma ⊢s Delta) :=
  cutAdm_atom_left x Gamma Delta d2 d1.1 d1.2 rfl rfl

/-- Generic-sequent helper matching on d1 for atom case. -/
private noncomputable def cutAdm_atom_left
    (x : Atom) (G0 D0 : Finset (Proposition Atom))
    (d2 : CutFreeLKProof (insert (.atom x) G0 ⊢s D0))
    {seq : LKSequent Atom} (d1_raw : LKProof seq) (hcf : CutFree d1_raw)
    (hant : seq.ant = G0) (hsuc : seq.suc = insert (.atom x) D0) :
    CutFreeLKProof (G0 ⊢s D0) :=
  match d1_raw, hcf with
  | .ax phi _G _D hphiL hphiD, _ =>
    if heq : phi = .atom x then
      heq ▸ hant ▸ hsuc ▸
        d2.mono (Finset.insert_subset_iff.mpr ⟨hant ▸ hphiL, Finset.Subset.refl _⟩)
               (Finset.Subset.refl _)
    else
      ⟨.ax phi G0 D0 (hant ▸ hphiL)
         ((Finset.mem_insert.mp (hsuc ▸ hphiD)).resolve_left heq),
       trivial⟩
  | .botL _G _D hbot, _ =>
    ⟨.botL G0 D0 (hant ▸ hbot), trivial⟩
  | .andL A B hAB d', hcf' =>
    let d2' := d2.mono
      (Finset.insert_subset_insert _
        (Finset.insert_subset_insert _ (hant ▸ Finset.Subset.refl _)))
      (Finset.Subset.refl _)
    let ⟨r, hr⟩ := cutAdm_atom_left x
      (insert A (insert B G0)) D0 d2'
      d' hcf' rfl (hsuc)  -- ant of d' is insert A (insert B _G) = insert A (insert B G0)
    ⟨.andL A B (hant ▸ hAB) r, hr⟩
  | .weakL A d', hcf' =>
    let d2' := d2.mono
      (Finset.insert_subset_insert _ (hant ▸ Finset.Subset.refl _))
      (Finset.Subset.refl _)
    let ⟨r, hr⟩ := cutAdm_atom_left x G0 D0 d2' d' hcf' sorry hsuc
    ⟨r.mono (Finset.subset_insert _ _) (Finset.Subset.refl _) |>.1,
     sorry⟩  -- CutFree evidence via CutFree.mono
  | .cut _ _ _, hcf' => absurd hcf' (by simp [CutFree])
  -- ... remaining cases follow the same pattern
```

Note: The actual implementation will need careful tracking of `hant` and `hsuc` evidence through each case. The `sorry` markers in the sketch indicate places where subset manipulation and CutFree threading need to be filled in.

### 10. Concrete Code Sketch: Imp Principal Case

The principal case for `A = phiA -> phiB` is the most complex. Following [NegriVonPlato2001] Theorem 3.2.3, case 5.3, p. 57:

Given:
- `d1 = impR`: `d1' : insert phiA Gamma ⊢s insert phiB Delta` (from impR, cut-free)
- `d2 = impL`: `d2a : insert (phiA -> phiB) Gamma ⊢s insert phiA Delta` (from impL left)
                `d2b : insert phiB (insert (phiA -> phiB) Gamma) ⊢s Delta` (from impL right)

The transformation produces:
1. Cut `phiA -> phiB` from `d1_impR` and `d2a` (same formula, smaller proof): gives `Gamma ⊢s insert phiA Delta`
2. Cut `phiA` from step1 and `d1'` using IH for phiA: gives `Gamma ⊢s insert phiB Delta`
3. Rearrange `d2b` and cut `phiA -> phiB` from `d1_impR` and `d2b` (same formula, smaller proof): gives `insert phiB Gamma ⊢s Delta`
4. Cut `phiB` from step2 and step3 using IH for phiB: gives `Gamma ⊢s Delta`

Steps 1 and 3 recurse on the SAME formula (`phiA -> phiB`) with structurally smaller proofs.
Steps 2 and 4 recurse on SUBFORMULAS (`phiA` and `phiB`), handled by the continuation.

### 11. Existing CSLib Cut Elimination Patterns

**LJ (Propositional/SequentCalculus/LJ/)**: Uses the same architecture as LK but with single-conclusion sequents. `cutAdmissibility` is stated but uses `sorry`. `cutElim` returns `Nonempty (CutFreeLJProof seq)` and IS proved (assuming `cutAdmissibility`). The LJ file demonstrates that the `Nonempty`-based `cutElim` pattern works.

**CLL (LinearLogic/CLL/)**: `CutFreeProof` is defined but `cutAdm` and `cut_elim` are commented out as TODOs.

Neither provides a completed cut admissibility proof to use as a template. The LK implementation would be the first complete cut elimination in CSLib.

### 12. Estimated Complexity

The rewrite requires:
- Approximately 5 case-specific helper functions (atom, bot, imp, and, or).
- Each helper uses the generic-sequent pattern.
- For compound cases (imp, and, or), a second level of helpers for the inner case analysis on d₂.
- Total estimated LOC: 400-600 (compared to the current 873 lines, but building correctly).
- The code will be `noncomputable` (required for the `if` branching on DecidableEq producing data).

## Adversarial Self-Verification

### Challenged Claims

1. **Claim: The generic-sequent helper pattern solves the dependent elimination problem.**
   - Verified by successful compilation of minimal reproduction. The pattern was tested with `SP2` indexed by `SQ` (struct with two Finset fields), matching `.weakL` and `.ax` constructors. Term-mode match on a generically-quantified `{sq : SQ}` parameter avoids the Finset quotient equation.
   - Confidence: **high (0.95)**.

2. **Claim: `Nonempty` does NOT fix the dependent elimination failure.**
   - Verified by direct test: `cases d` where `d : SP2 ⟨insert A Gamma, Delta⟩` fails with the same "Failed to solve equation" error regardless of whether the target is `Type`, `Prop`, or `Nonempty`.
   - Confidence: **high (0.95)**.

3. **Claim: DecidableEq-based `if` branching works for Type targets.**
   - Verified: `if heq : phi = A then ... else ...` compiles when the branches produce `CutFreeLKProof` (a Type). `Or.resolve_left` works to extract `phi ∈ Delta` in the else branch.
   - Confidence: **high (0.95)**.

4. **Claim: No changes to Basic.lean are needed.**
   - Verified: `LKProof`, `CutFree`, `CutFreeLKProof`, `LKProof.mono`, `CutFree.mono` all build successfully. The problems are entirely in `CutElimination.lean`.
   - Confidence: **high (0.9)**. One caveat: the implementation may benefit from adding helper lemmas to `Basic.lean` (e.g., a combined `CutFreeLKProof.mono` that threads both `LKProof.mono` and `CutFree.mono`), but this is additive, not a change.

5. **Claim: Structural recursion on formula + well-founded recursion via `termination_by sizeOf A` suffices.**
   - Verified: `sizeOf a < sizeOf (a.imp b)` and `sizeOf b < sizeOf (a.imp b)` are both provable by `omega`. The compound cases' principal subcases recurse on subformulas (smaller sizeOf), and non-principal subcases recurse on same formula with structurally smaller proofs (handled by the generic-sequent helper's pattern matching).
   - Risk: The non-principal subcases may require an explicit height measure if the generic-sequent helper complicates Lean's structural recursion checker. Fallback: use `termination_by (sizeOf A, d1.1.height + d2.1.height)` with lexicographic ordering.
   - Confidence: **medium (0.7)**.

### Uncertain Claims

- The exact threading of `hant`/`hsuc` evidence through nested recursive calls in the generic-sequent helper may require additional lemmas. The code sketch uses `sorry` for some of these points. Implementation difficulty is estimated as moderate.
- Confidence in the 400-600 LOC estimate: **medium (0.6)**. The principal cases for `and` and `or` involve 4 steps each (similar to `imp`), and each non-principal subcase involves ~5 lines of context manipulation.

### Reuse Check Protocol

1. **CSLib Foundations**: Checked `Cslib.Foundations.*` -- no cut elimination infrastructure. The `InferenceSystem` typeclass is used but doesn't provide cut elimination machinery.
2. **Typeclass hierarchy**: `LTS`, `HasImp`, etc. are not relevant to sequent calculus cut elimination.
3. **Notation typeclasses**: The `⊢s` notation is already defined and correct.
4. **Mathlib**: `lean_leansearch "cut elimination sequent calculus"` returned no relevant results. Mathlib does not contain propositional sequent calculus.
5. **Logics/Languages namespaces**: LJ's `cutAdmissibility` uses `sorry`; CLL's is commented out. No completed template exists.

## Recommendations

### Immediate Next Steps

1. **Rewrite `CutElimination.lean` from scratch** using the generic-sequent helper pattern.
2. **Structure**: Five case-specific modules (atom, bot, imp, and, or) with a top-level `cutAdmissibility` function that dispatches by `match A with`.
3. **Add `NegriVonPlato2001` to `references.bib`** before PR.
4. **Mark as `noncomputable`** throughout (required for DecidableEq branching into Type).

### Implementation Priority

1. Start with atom and bot cases (simplest, no principal case).
2. Implement imp case (most complex principal case, provides template for and/or).
3. Implement and and or cases (symmetric to each other, follow imp pattern).
4. Wire up `cutElim` (straightforward, follow LJ pattern).

### Zero-Debt Compliance

No `sorry` deferral is recommended. The generic-sequent helper pattern should enable a complete proof. If any case proves intractable during implementation, the task should be marked [BLOCKED] with the specific failing case documented, NOT papered over with `sorry`.

## References

- [TroelstraSchwichtenberg2000] A. S. Troelstra and H. Schwichtenberg, *Basic Proof Theory*, 2nd ed., Cambridge Tracts in Theoretical Computer Science 43, Cambridge University Press, 2000. Ch. 4, Theorem 4.1.5, pp. 92--99.
- [NegriVonPlato2001] S. Negri and J. von Plato, *Structural Proof Theory*, Cambridge University Press, 2001. Ch. 3, Theorem 3.2.3, pp. 54--57. **BibKey needs to be added to `references.bib`.**
