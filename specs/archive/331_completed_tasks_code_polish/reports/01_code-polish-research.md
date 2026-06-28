# Research Report: Code Polish for Tasks 310, 312, 322

**Task**: 331 — Polish code from recently completed tasks
**Session**: sess_1750817400_a3b7c1_331
**Status**: Researched

## Summary

Three polish items across three files. All are straightforward docstring and parameter cleanup
with no proof logic changes. No blockers. The implementation should be a single phase with
mechanical edits.

---

## Item 1: Cross-Reference Docstrings (ConservativeChain / MplConservativeChain)

### Files

- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`

### Current State

MplConservativeChain.lean already mentions ConservativeChain.lean in several places:
- Module docstring (lines 41, 63-67) has a "Relationship to ConservativeChain.lean" section
- Individual theorem docstrings reference the IPL-routed counterparts (lines 131-133, 151-152, 186-187)

ConservativeChain.lean makes **zero** mention of MplConservativeChain.lean. The IPL-routed
proofs (`hilbertMplConservativeOverImp`, `hilbertMplConservativeOverConjImp`) have no "See also"
referencing their direct-algebraic counterparts (`_direct` variants).

### Theorem Cross-Reference Map

| ConservativeChain.lean (IPL-routed) | MplConservativeChain.lean (direct algebraic) |
|--------------------------------------|-----------------------------------------------|
| `hilbertMplConservativeOverConjImp` (line 237) | `hilbertMplConservativeOverConjImp_direct` (line 154) |
| `hilbertMplConservativeOverImp` (line 216) | `hilbertMplConservativeOverImp_direct` (line 188) |
| `GHAValid_implies_BrouwerianValid_orBotFree` (line 156) | `GHAValid_implies_BrouwerianValid_direct` (line 136) |
| `hilbertConjImpConservativeOverImp_direct` (line 199) | _(no counterpart; this is a thin alias)_ |

### Recommended Edits

**ConservativeChain.lean** — add "See also" lines to docstrings for:

1. `hilbertMplConservativeOverConjImp` (line 232-240): Add
   `See also \`hilbertMplConservativeOverConjImp_direct\` in \`MplConservativeChain.lean\` for the direct algebraic route that avoids IPL.`

2. `hilbertMplConservativeOverImp` (line 204-219): Add
   `See also \`hilbertMplConservativeOverImp_direct\` in \`MplConservativeChain.lean\` for the direct algebraic route.`

3. `GHAValid_implies_BrouwerianValid_orBotFree` (line 149-161): Add
   `See also \`GHAValid_implies_BrouwerianValid_direct\` in \`MplConservativeChain.lean\` for the direct algebraic proof via \`LowerSet B\`.`

4. Module docstring: Add a note in the "Inter-Fragment" section (around line 38-45) mentioning that
   `MplConservativeChain.lean` provides alternative direct-algebraic proofs for the MPL steps
   that do not route through IPL.

**MplConservativeChain.lean** — strengthen existing references to use `See also` format:

5. `GHAValid_implies_BrouwerianValid_direct` docstring (line 132-133) already says
   "Compare with `GHAValid_implies_BrouwerianValid_orBotFree` in `ConservativeChain.lean`...".
   Consider upgrading to `See also` format for consistency with the added ConservativeChain references.

6. Similarly for `hilbertMplConservativeOverConjImp_direct` (line 151) and
   `hilbertMplConservativeOverImp_direct` (line 186).

---

## Item 2: Thin Alias `hilbertConjImpConservativeOverImp_direct`

### File

`Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean`, lines 199-202

### Current Definition

```lean
theorem hilbertConjImpConservativeOverImp_direct {Atom : Type u} {φ : PL.Proposition Atom}
    (hITO : φ.IsImpTopOnly = true) (h : Derivable (@ConjImpAxiom Atom) φ) :
    Derivable (@ImpAxiom Atom) φ :=
  hilbertConjImpConservativeOverImp hITO h
```

### Analysis

This is literally `hilbertConjImpConservativeOverImp hITO h` with no additional logic. The
`_direct` suffix is misleading because it suggests a different proof route (like the `_direct`
variants in MplConservativeChain.lean), but it uses exactly the same proof as the original.

**Usage**: Never referenced anywhere else in the codebase (zero callers).

**Name collision concern**: MplConservativeChain.lean has `hilbertMplConservativeOverImp_direct`
and `hilbertMplConservativeOverConjImp_direct`, which are genuinely different proofs using the
direct algebraic route. The `_direct` suffix on this alias could confuse readers into thinking
there is an alternative algebraic proof for the ConjImp-over-Imp step, when there is not.

### Recommendation: Keep with clarifying docstring

**Rationale for keeping** (over inlining):

1. **API naming symmetry**: ConservativeChain.lean has `hilbertConjImpConservativeOverImp_viaIpl`
   (line 227) which proves the same result but routing through IPL. Having `_direct` alongside
   `_viaIpl` makes the API surface explicit about the two proof routes being available, even
   though the `_direct` route for this particular step is trivially identical to the base lemma.

2. **Module docstring references it** in the bullet list at line 40.

3. **Zero callers means removal is safe** but the alias is harmless and costs nothing.

**Recommended edit**: Add a clarifying docstring that explicitly states this is a naming-convention
alias and not an alternative proof route:

```lean
/-- **API alias**: `hilbertConjImpConservativeOverImp` restated under the `_direct` naming
convention used in this module. Unlike the `_direct` variants in `MplConservativeChain.lean`,
this is definitionally equal to the base lemma — the ConjImp→Imp conservativity step has only
one proof route (via the free Brouwerian semilattice).

See also `hilbertConjImpConservativeOverImp_viaIpl` for the alternative routing through IPL. -/
```

---

## Item 3: Unused `_hφ` Parameter in `hilbertEmbeddingLemma`

### File

`Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean`, lines 418-427

### Current Signature

```lean
theorem hilbertEmbeddingLemma {Atom : Type*} {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (φ : Proposition Atom) (_hφ : φ.IsImpTopOnly = true) :
    HilbertEvaluate v φ = ⊤ ↔ principal (HilbertEvaluate v φ) = (⊥ : HilbertFilter H) := by
```

### Analysis

The proof body:
```lean
  constructor
  · intro h; rw [h]; exact principal_top
  · intro h; apply principal_injective; rw [h, principal_top]
```

This proof operates entirely on `principal` and `principal_injective`. It never references `_hφ`.
The biconditional `HilbertEvaluate v φ = ⊤ ↔ principal (HilbertEvaluate v φ) = ⊥` holds for
**any** formula, not just `IsImpTopOnly` ones. The proof only uses the algebraic fact that
`principal` is injective and `principal ⊤ = ⊥`.

**Callers**: `hilbertEmbeddingLemma` is **never called anywhere** in the codebase currently.
It is declared but unreferenced (the module is imported but the lemma is not used downstream).

**Why it exists**: The docstring (line 49) and module description advertise it as part of the
Diego embedding theorem's consequence for evaluation. The `IsImpTopOnly` guard was likely added
to match the context where the lemma would eventually be applied (the embedding only preserves
semantics for `IsImpTopOnly` formulas), even though this particular lemma does not need it.

### Recommendation: Remove `_hφ` parameter

**Rationale**:

1. The parameter is genuinely unused in the proof — the `_` prefix confirms intentional suppression.
2. The lemma has zero callers, so removing the parameter is a non-breaking API change.
3. Keeping an unused parameter creates a false dependency: callers would need to supply an
   `IsImpTopOnly` proof that is never used, making the API misleadingly restrictive.
4. If a future caller needs the `IsImpTopOnly` guard, it can be added at the call site.
5. The CSLib lint rules flag unused variables (`unusedSectionVars`); while `_hφ` is a function
   parameter rather than a section variable, removing it follows the same spirit.

**Alternative (document-and-keep)**: If the parameter is retained for "semantic documentation"
(signaling that the lemma is intended for use only with `IsImpTopOnly` formulas), add a
docstring explaining this. However, this is the weaker option because Lean has no way to
enforce "intended use" through an unused parameter — it just clutters the signature.

### Recommended edit

Remove `(_hφ : φ.IsImpTopOnly = true)` from the signature:

```lean
theorem hilbertEmbeddingLemma {Atom : Type*} {H : Type*} [HilbertAlgebra H]
    (v : Atom → H) (φ : Proposition Atom) :
    HilbertEvaluate v φ = ⊤ ↔ principal (HilbertEvaluate v φ) = (⊥ : HilbertFilter H) := by
```

Update the docstring to note that while the biconditional holds for all formulas, its primary
application is to `IsImpTopOnly` formulas in the context of the Diego embedding.

---

## Implementation Plan Sketch

**Single phase** — all edits are docstring additions or parameter removal, no proof logic changes.

1. ConservativeChain.lean: Add "See also" cross-references to module docstring and three theorem
   docstrings (items 1.1-1.4 above).
2. ConservativeChain.lean: Replace docstring of `hilbertConjImpConservativeOverImp_direct`
   with API-alias clarification (item 2).
3. MplConservativeChain.lean: Upgrade "Compare with" to "See also" format in three theorem
   docstrings (items 1.5-1.6 above).
4. DiegoEmbedding.lean: Remove `_hφ` parameter from `hilbertEmbeddingLemma` signature and
   update docstring (item 3).
5. Verify: `lake build` to confirm no breakage.

**Estimated effort**: Low. Pure docstring and signature edits, no proof changes.

**Risk**: Essentially zero. The `_hφ` removal is the only structural change, and the lemma has
zero callers.
