# Teammate B (Alternative Approaches) Research Findings
## Task 268: Add @[simp, scoped grind =] Normalization Tags to Hilbert System Definitional Lemmas

---

## Key Findings

### 1. Mathlib Conventions for simp/grind Co-Tagging

Mathlib does not use `@[scoped grind =]` itself (it predates or parallel-tracks the grind tactic
development). Searching Mathlib for this combined attribute returned no hits. The CSLib co-tagging
convention is therefore an **intra-CSLib standard**, not a Mathlib import.

The relevant Mathlib precedents are:

**Mathlib `@[simp]` discipline**: Mathlib tags a lemma `@[simp]` when it:
1. Rewrites a "complex" LHS to a simpler normal form
2. Has the form `f (constructor x) = ...` (structural equation)
3. Is an iff (`X ↔ Y`) where X is a defined predicate and Y is a logical statement

CSLib's `@[simp, scoped grind =]` co-tagging follows this same logic, adding grind registration
alongside simp for definition-unfolding equalities and iff characterizations. The `scoped` qualifier
is essential: it means the attribute only fires when the relevant namespace/scope is opened, which
prevents namespace pollution across unrelated modules.

**The three-tier model observed in CSLib** (evidence-grounded):

| LHS character | Attribute used | Example |
|---------------|----------------|---------|
| Definitional `def` that should unfold | `@[simp, scoped grind =]` | `Proposition.denotation`, `Satisfies.Bundled` |
| Iff/eq characterization theorem | `@[scoped grind =]` | `Satisfies.or_iff_or`, `derivation_def` |
| Inductive-def that grind must case-split | `@[scoped grind]` (no `=`) | `Satisfies`, `Parallel.fvar` |

The `@[simp]` attribute is withheld from characterization *theorems* (pattern B) because simp
would loop: the iff has the same structure on both sides through the definition. The `=` variant of
grind handles iffs directionally (it uses the iff as a rewrite rule rather than a case-split rule).

---

### 2. Simp Loop Risk Analysis

**Risk 1: `abbrev` transparency -- the phantom loop risk**

All derived connectives in CSLib (`neg`, `top`, `or`, `and`, `diamond`, `someFuture`, etc.) are
defined as `abbrev`, not `def`. In Lean 4, `abbrev` declarations are **reducible by default**:
they are automatically unfolded by `simp` and by definitional equality checks. This means:

- `@[simp]` tags on lemmas about `abbrev`-defined connectives are genuinely needed (to control
  which direction rewriting happens)
- But there is no *new* simp loop risk from adding `scoped grind =` to these lemmas, because
  grind will reuse the same orientation simp would use (LHS → RHS)

**Concrete check**: `Formula.neg φ = Formula.imp φ Formula.bot` is already transparent. Adding
`@[scoped grind =]` to a lemma that says `neg φ = imp φ bot` is safe because:
1. The grind `=` attribute adds this as a directed rewrite (LHS → RHS), not an iff
2. `abbrev` unfolding would reduce `neg φ` to `imp φ bot` anyway; the tag just makes grind
   aware of this explicitly

**Risk 2: Paired unfolding / refolding chains**

The only genuine simp loop risk arises when **two lemmas together form a cycle**:
```
lemma A_def: A x = f x
lemma A_def': f x = A x   -- if both were simp lemmas, this loops
```

Searching CSLib for such pairs near the target files:

- `listImp_nil` (`listImp [] φ = φ`) -- no inverse exists
- `listImp_cons` (`listImp (ψ :: Ψ) φ = HasImp.imp ψ (listImp Ψ φ)`) -- no inverse
- `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons` -- no inverses found
- `toTemporal_atom`, `toTemporal_bot`, `toTemporal_imp` -- no inverses
- `Satisfies.neg_iff`, `Satisfies.or_iff`, `Satisfies.and_iff` -- these are iff characterizations;
  no loop risk because they are rewrites FROM a derived connective TO primitive-level propositions

**Risk 3: `simpNF` violations on iff theorems**

The `simpNF` linter verifies that simp lemmas' LHS is not redundantly reducible by simp itself.
For iff characterizations (`X ↔ Y`), simp canonicalizes both sides, so if `X` or `Y` is already
a simp normal form, `simpNF` may complain. This is why:
- `@[simp, nolint simpNF, scoped grind =]` appears in `BuchiClosure.lean` line 96 for a case
  where the simp LHS was deemed "complex" by the author but does not satisfy simpNF's normal form
  check

**Implication for the task**: Iff characterization lemmas (`Satisfies.neg_iff`, etc.) should NOT
get `@[simp]` added -- only `@[scoped grind =]`. They currently have no simp tag and that is
architecturally correct. The `@[simp]`-only or `@[simp, scoped grind =]` pattern applies to
definition-unfolding equalities with a clean LHS (structural equations over constructors).

---

### 3. Alternative Tagging Strategies

#### Strategy A: Co-tag everything (task description's intended approach)
All definitional equalities (structural `X_nil`, `X_cons`, `X_def`) get `@[simp, scoped grind =]`.
All iff characterizations (`X_iff`, `X_def_iff`) get `@[scoped grind =]` without `simp`.

**Verdict**: Correct for the structural equalities. Confirmed safe by existing CSLib patterns.

#### Strategy B: `@[simp]` only (no grind) on some lemmas

Some lemmas in CSLib have `@[simp]` without `scoped grind =` and this is intentional:
- `swapTemporal_someFuture` and related lemmas (`Bimodal/Syntax/Formula.lean` lines 158-178) have
  `@[simp]` but not `scoped grind =`. These are structural equalities about `swapTemporal`, a
  function used via `simp only [...]` in specific proofs, not a general rewrite for grind.
- `subst_atom_eq`, `subst_bot`, `subst_imp`, etc. (`Bimodal/ProofSystem/Substitution.lean` lines
  55-83) are tagged `@[simp]` only. These substitution lemmas are used in targeted `simp only`
  calls, not in `grind`-based proofs.

**Verdict**: Lemmas used only in targeted `simp only [...]` proofs and not in `grind` automation
can stay `@[simp]` only. The task targets the *normalization layer* specifically, meaning lemmas
that should participate in automated proof search (where grind would encounter them).

#### Strategy C: `@[grind =]` only (no simp) 

Some CSLib lemmas have `@[scoped grind =]` without `@[simp]` at all:
- `InferenceSystem.rwConclusion` (`Foundations/Logic/InferenceSystem.lean` line 40-41)
- Several lemmas in `Modal/Basic.lean` (lines 199-232): `derivation_def`, `neg_satisfies`, etc.

This is used when the definition/theorem is important for grind automation but should NOT be
applied by simp (to avoid triggering in contexts where the user wants manual control).

**Verdict**: For the `listImp` and `bigconj` lemmas, `@[simp]` is already correct because they
appear in `simp only [...]` calls within existing proofs. Grind should be co-added.

#### Strategy D: Adding `@[scoped grind =]` to Modal `Satisfies.*_iff` lemmas

Currently `Modal/Basic.lean` has:
- `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, `Satisfies.or_iff` --
  NOT tagged (internal characterization lemmas)
- But lines 204-232 have `@[scoped grind =]` versions that wrap these via `⇓Modal[m,w ⊨ ...]`
  notation

There is mild redundancy risk: if both the unwrapped and wrapped forms are grind-registered, grind
may attempt both and produce slightly longer proof search. However the risk of incorrect behavior
is nil. The wrapped `⇓Modal[...]` forms are the "correct" ones for the grind `=` attribute since
they use the registered notation. Adding grind to the unwrapped `Satisfies.*_iff` theorems is
**optional but safe** -- grind may use them as fallback lemmas.

---

### 4. Ordering / Dependency Considerations

**Recommended order** (minimizes intermediate build failures):

1. **`Foundations/Logic/Metalogic/ListImplication.lean`** (leaf file, no dependencies on the
   others). Change `@[simp]` to `@[simp, scoped grind =]` on `listImp_nil` and `listImp_cons`.

2. **`Foundations/Logic/Theorems/BigConj.lean`** (leaf file). Change `@[simp]` to
   `@[simp, scoped grind =]` on `bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`,
   `negBigconj_def`.

3. **`Logics/Temporal/FromPropositional.lean`** (imports `Propositional.Defs` and
   `Temporal.Syntax.Formula`). Upgrade `@[simp]` to `@[simp, scoped grind =]` on
   `toTemporal_atom`, `toTemporal_bot`, `toTemporal_imp`, `toTemporal_and`, `toTemporal_or`.

4. **`Logics/Modal/Basic.lean`** (add `@[scoped grind =]` only -- not `simp` -- to
   `Satisfies.neg_iff`, `Satisfies.diamond_iff`, `Satisfies.and_iff`, `Satisfies.or_iff`).

**Build-failure risk**: Very low. None of these changes remove existing tags; they add new tags.
Existing `simp only [...]` calls will be unaffected (scoped grind tags are inert outside their
scope). The most likely failure mode would be `simpNF` lint violations if the iff forms have the
wrong orientation. To hedge against this: run `lake build` after each individual file change
before proceeding to the next.

---

### 5. Prior Art in CSLib (Evidence Inventory)

The following files demonstrate the co-tagging convention that this task extends:

**Canonical reference (most developed)**: `Cslib/Foundations/Data/OmegaSequence/Init.lean`
- 15+ lemmas with `@[simp, scoped grind =]` on structural equalities like `drop_zero`, `get_fun`,
  `eta`, etc.
- Pattern: purely structural equations about `ωSequence` operations

**Logic-domain examples**:
- `Cslib/Logics/Modal/Basic.lean` lines 189, 427, 432: `@[simp, scoped grind =]` on `valid` def
  and `Satisfies.Bundled`; `@[scoped grind =]` on lines 199-232 for iff characterizations
- `Cslib/Logics/Modal/Denotation.lean` line 25: `@[simp, scoped grind =]` on `denotation` def
- `Cslib/Logics/HML/Basic.lean` lines 61, 72, 77, 100, 128: `@[simp, scoped grind =]` on `neg`,
  `finiteAnd`, `finiteOr`, `denotation`, `neg_satisfies`

**Existing `@[simp]`-only patterns that should remain as-is**:
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` lines 55-83: structural substitution
  lemmas; these are used in `simp only [...]` for specific proofs but not for grind
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` lines 158-178: `swapTemporal_*` lemmas

**One precedent for `@[simp, nolint simpNF, scoped grind =]`**:
- `Cslib/Computability/Automata/DA/BuchiClosure.lean` line 96: when simpNF would be triggered
  by the LHS form, but the author still wants both attributes, `nolint simpNF` is added

---

### 6. Lemmas Where `@[simp]` Is Appropriate But `grind` Is Not (or vice versa)

**`@[simp]` only (not grind)** -- justified cases in CSLib:

Substitution structural lemmas (`subst_atom_eq`, `subst_bot`, `subst_imp`, etc.):
These are called in targeted `simp only [...]` in specific proofs. They don't appear in proof
contexts where grind would be active. Adding grind would have no benefit and slightly increase
grind's premise database size.

`swapTemporal_*` lemmas in `Bimodal/Syntax/Formula.lean`:
These are highly specific structural equalities used only in soundness proofs where the author
manually selects them via `simp only [Formula.swapTemporal, truthAt]`. Grind automation is
unlikely to need them.

**`@[scoped grind =]` only (not simp)** -- justified cases:

`derivation_def` in `Modal/Basic.lean`:
This says `⇓Modal[m,w ⊨ φ] = Satisfies m w φ`. It's not a simp lemma because `simp` using
this would constantly unfold the notation, which the user wants to avoid in most proof goals.
Grind needs it to equate the two representations during automation.

`InferenceSystem.rwConclusion` in `Foundations/Logic/InferenceSystem.lean`:
This function rewrites the conclusion of a proof. It's useful for grind equational reasoning
but should not fire automatically in simp normalization.

---

### 7. Risks to Existing Proofs

**Simp behavior**: Adding `scoped grind =` to existing `@[simp]` lemmas does NOT change how
`simp` behaves. Simp and grind are independent tactic engines. Existing `simp` proofs are
completely unaffected.

**Grind behavior**: Adding `@[scoped grind =]` to lemmas that are already in grind's reachable
search space (via unfolding) makes grind slightly faster and more reliable. This is strictly
positive.

**Potential regression**: The only regression risk is if adding `@[scoped grind =]` to a lemma
causes grind to rewrite in an unexpected direction, making a previously-terminating grind call
diverge or time out. In practice this is extremely unlikely for:
- Simple structural equalities (`listImp_nil : listImp [] φ = φ`)
- Iff characterizations that are already proven (`neg_satisfies`, `Satisfies.or_iff`)

The `scoped` qualifier provides an important safeguard: the grind attribute only activates
within the relevant scope (namespace/open), so proofs in unrelated modules are unaffected.

---

## Recommended Approach

### Primary Recommendation: Match the OmegaSequence/HML Pattern Exactly

The existing CSLib pattern (from `OmegaSequence/Init.lean` and `HML/Basic.lean`) is:
- **Definitional equality** (`X = Y` where X is a structural expression): `@[simp, scoped grind =]`
- **Iff characterization** (`X ↔ Y` where X is a derived predicate): `@[scoped grind =]` (no simp)

**Apply this to the target files**:

| File | Tag to add | Lemma type |
|------|-----------|------------|
| `ListImplication.lean` lines 51, 54 | `@[simp, scoped grind =]` | Structural equality |
| `BigConj.lean` lines 72, 76, 79, 87 | `@[simp, scoped grind =]` | Structural equality |
| `FromPropositional.lean` lines 69, 74, 79, 84, 90 | `@[simp, scoped grind =]` | Structural equality (`= rfl`) |
| `Modal/Basic.lean`: `Satisfies.neg_iff`, `.diamond_iff`, `.and_iff`, `.or_iff` | `@[scoped grind =]` | Iff characterization |

### Ordering

Process files in dependency order (leaves first):
1. `Foundations/Logic/Metalogic/ListImplication.lean`
2. `Foundations/Logic/Theorems/BigConj.lean`
3. `Logics/Temporal/FromPropositional.lean`
4. `Logics/Modal/Basic.lean`

Run `lake build` between each file to catch any unexpected simpNF violations.

### Exclusions (Not to Tag)

Do NOT tag:
- `Bimodal/ProofSystem/Substitution.lean` substitution lemmas (already `@[simp]` correctly;
  not used by grind in practice)
- `Bimodal/Syntax/Formula.lean` `swapTemporal_*` lemmas (same reason)
- Any `Derivable.*` constructor-mirroring lemmas (as specified in task description)
- Any `DerivationTree.*` constructor theorems (height lemmas, constructor wrappers)

---

## Evidence/Examples

### Example 1: Canonical co-tagged structural equality (OmegaSequence pattern)
```lean
-- From Foundations/Data/OmegaSequence/Init.lean line 35
@[simp, scoped grind =]
protected theorem eta (s : ωSequence α) : head s ::ω tail s = s := by ...

-- From same file, line 101
@[simp, scoped grind =] theorem drop_zero {s : ωSequence α} : s.drop 0 = s := rfl
```
Pattern: LHS is a structured expression over constructors. The `rfl` proof signals this is a
definitional equality that both simp and grind can use directly.

### Example 2: Co-tagged for grind automation in modal semantics (HML pattern)
```lean
-- From HML/Basic.lean line 61
@[simp, scoped grind =]
def Proposition.neg (a : Proposition Label) : Proposition Label :=
  match a with | .true => .false | .false => .true | ...

-- From HML/Basic.lean line 128
@[simp, scoped grind =]
theorem neg_satisfies {lts : LTS State Label} :
    ¬Satisfies lts s a.neg ↔ Satisfies lts s a := by
  induction a generalizing s <;> grind
```
Pattern: `neg_satisfies` is proved BY grind after `neg` and `Satisfies` are grind-tagged.
This is the goal: after tagging `listImp_nil/cons`, grind should be able to prove goals that
currently require manual `simp only [listImp_nil, listImp_cons]` calls.

### Example 3: `@[scoped grind =]` only on iff (Modal/Basic.lean pattern)
```lean
-- From Modal/Basic.lean line 208-210
@[scoped grind =]
theorem Satisfies.or_iff_or {m : Model World Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := Satisfies.or_iff
```
Pattern: No `@[simp]` because this would cause simp to unfold `∨` goals everywhere. Grind uses
it for the `=` rewrite direction in automated proof search.

### Example 4: `@[simp, nolint simpNF, scoped grind =]` for simpNF-failing lemmas
```lean
-- From Computability/Automata/DA/BuchiClosure.lean line 96
@[simp, nolint simpNF, scoped grind =]
theorem Buchi.mem_infOftenOne_language (xs : ωSequence (Fin 2)) :
    xs ∈ language Buchi.infOftenOne ↔ ∃ᶠ k in atTop, xs k = 1 := by ...
```
Pattern: When `simpNF` linter complains about an iff form but the author wants both attributes,
add `nolint simpNF`. The task's target lemmas are all simple structural equalities (`= rfl`) that
should pass simpNF without needing the nolint.

---

## Confidence Level

**HIGH** for the following:
- The three-tier tagging model (`@[simp, scoped grind =]` vs `@[scoped grind =]` vs `@[simp]`)
  is well-evidenced across CSLib with clear architectural justification
- Structural equalities (`listImp_nil/cons`, `bigconj_*`, `toTemporal_*`) are safe to co-tag
- No simp loop risk: CSLib's derived connectives are `abbrev` (already transparent) and there
  are no inverse lemma pairs for the target lemmas
- Iff characterizations in `Modal/Basic.lean` (`Satisfies.*_iff`) should NOT get `@[simp]`,
  only `@[scoped grind =]`
- `abbrev` declarations do NOT need `@[simp]` or `@[grind]` tags on the abbrevs themselves
  (they are already kernel-transparent); only *theorems about them* need tagging

**MEDIUM** for the following:
- Whether the four `Satisfies.*_iff` lemmas in `Modal/Basic.lean` should be tagged -- the
  `⇓Modal[...]`-wrapped versions are already grind-registered, so this may be redundant;
  adding them is harmless but may be unnecessary
- Whether `Bimodal/ProofSystem/Substitution.lean` substitution lemmas should also be upgraded
  (they are not in the task's stated target list, but the pattern would fit)

**LOW** for:
- Whether any proofs currently using `simp only [listImp_nil, listImp_cons]` would become
  redundant after grind tagging (they would still work fine; the tags do not remove simp hints)
