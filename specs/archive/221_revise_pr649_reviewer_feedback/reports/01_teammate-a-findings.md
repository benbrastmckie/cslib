# Teammate A Findings: Primary Implementation Approach for Revising PR #649

## Key Findings

### 1. Files in PR #649 Scope

PR #649 currently touches these files:
- `Cslib.lean` — adds three new public imports
- `Cslib/Foundations/Logic/Connectives.lean` — **new file** (typeclass hierarchy)
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` — **new file** (must be removed per thomaskwaring)
- `Cslib/Logics/LTL/Syntax/Formula.lean` — **new file** (keep)
- `Cslib/Logics/Propositional/Defs.lean` — modified (copyright, architecture docstring, removed `[Bot Atom]`)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — modified (copyright, renamed `implE`→`impE`, `orI₁`→`orI1`, etc.)
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — **new file** (keep)
- `references.bib` — new entries added

### 2. LTL Semantics Split (thomaskwaring's primary request)

thomaskwaring explicitly requests: "Please split the semantics development into a separate PR."

**Action required**: Remove `Cslib/Logics/LTL/Semantics/Satisfies.lean` from PR #649 and its import from `Cslib.lean`. The file exists at:
- `/home/benjamin/Projects/cslib/Cslib/Logics/LTL/Semantics/Satisfies.lean`

The `LTL/Syntax/Formula.lean` stays (thomaskwaring says "split the semantics development," not the syntax). The directory `Cslib/Logics/LTL/Semantics/` should be left empty or the directory removed from this PR's scope.

### 3. PR #536 Merge — Critical Consistency Issue

PR #536 (merged 2026-06-16T06:46:52Z) changed `IsIntuitionistic` and `IsClassical` from theory-based to **inference-system-based**:

**Upstream (post-PR #536)** in `Cslib/Logics/Propositional/Defs.lean`:
```lean
class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)

class IsClassical (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  dne (A : Proposition Atom) : S⇓(¬¬A → A)
```

**Local branch** in `Cslib/Logics/Propositional/Defs.lean`:
```lean
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T

class IsClassical (T : Theory Atom) where
  dne (A : Proposition Atom) : (¬¬A → A) ∈ T
```

The local branch still uses the **old** theory-parameterized form. The upstream also retains `[Bot Atom]` — while our PR aimed to remove this, PR #536 reintroduced it (upstream IPL uses `[Bot Atom]`). This is a significant rebase conflict.

**Additionally**: The upstream `NaturalDeduction/Basic.lean` uses `implE`, `implI`, `orI₁`, `orI₂` (subscript notation), while our PR renames these to `impE`, `impI`, `orI1`, `orI2`. This rename appears to be part of PR #649's changes to `NaturalDeduction/Basic.lean`, but conflicts with PR #536's changes to `Theory.lean` which also reference these names.

### 4. Naming Question: `imp` vs `impl`

**Finding**: thomaskwaring said "the actually existing example (`Modal`) uses `impl`." However, this refers to the **upstream** version of `Modal/Basic.lean`, which has:
```lean
-- Upstream Modal (leanprover/cslib main):
inductive Proposition (Atom : Type u) : Type u where
  | atom (p : Atom)
  | not (φ : Proposition Atom)      -- NOT bot+imp as primitives!
  | and (φ₁ φ₂ : Proposition Atom)
  | diamond (φ : Proposition Atom)

def Proposition.impl (φ₁ φ₂ : Proposition Atom) : Proposition Atom := ¬φ₁ ∨ φ₂
```

The upstream Modal uses `{atom, not, and, diamond}` as primitives and `impl` is a **derived** definition (not a constructor). Our local Modal branch refactored this to `{atom, bot, imp, box}` as primitives with `imp` as the constructor name.

**Conclusion**: There is no genuine conflict. The upstream `impl` is derived from `not`+`or`, not a primitive constructor. Our choice of `imp` as a primitive constructor name is consistent and independent. However, the PR description must be updated to:
1. Not cite "CSLib's existing formula types" as justification for `imp` (since those types are our own unmerged work)
2. Instead justify `imp` on independent grounds: the Gentzen/Prawitz natural deduction tradition uses `⊃` / `→` / `imp` as a primitive; "impl" abbreviates "implication" but `imp` is shorter and consistent with Mathlib's `Prop.imp` naming.

### 5. References — German-Language Papers Problem

The German-language papers in PR #649's scope (added to `references.bib` and cited in file headers):

| BibKey | Issue |
|--------|-------|
| `Johansson1937` | German: "Der Minimalkalkül..." |
| `Wajsberg1938` | German: "Untersuchungen über den Aussagenkalkül..." |
| `Heyting1930` | German: "Die formalen Regeln der intuitionistischen Logik" |
| `Gentzen1935` | German: "Untersuchungen über das logische Schließen" |

These appear in:
- `Cslib/Foundations/Logic/Connectives.lean` — references Johansson1937, Wajsberg1938, McKinsey1939, Prawitz1965, TroelstraVanDalen1988, Church1956, Heyting1930, Gentzen1935
- `Cslib/Logics/Propositional/Defs.lean` — references Gentzen1935, Johansson1937, Prawitz1965, TroelstraVanDalen1988
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — references Johansson1937, Prawitz1965, TroelstraVanDalen1988, Gentzen1935

**Avigad replacement**: ctchou recommends Jeremy Avigad's *Mathematical Logic and Computation* (Cambridge, 2022), chapters 2-3. This book is **not currently in `references.bib`**. A new entry `Avigad2022` must be added.

The key question is which German papers to keep and which to replace:
- `Gentzen1935`: Historical significance is high (natural deduction invented here), but German. thomaskwaring notes he read it in translation. **Recommendation**: Keep `Gentzen1935` (historical source attribution is still valuable) but add `Avigad2022` as the primary reading reference. Alternatively, remove the Gentzen cite and point to Prawitz1965 (English) which covers the same content.
- `Johansson1937`: German. Minimal logic originates here. **Recommendation**: Could retain as historical source but add English alternative.
- `Wajsberg1938`: German and Polish. Used only in Connectives.lean to justify primitive `and`/`or`. **Recommendation**: Replace with Avigad2022 or another English source.
- `Heyting1930`: German. Not directly cited in PR #649 files (only in Connectives.lean which mentions it). **Recommendation**: Consider replacing with Avigad2022.

thomaskwaring explicitly said "I agree with @ctchou about citing literature in English — the Gentzen paper is my bad, I read it in translation." This suggests removing `Gentzen1935` from citations and using `Prawitz1965` (English, covers same content) plus `Avigad2022`.

### 6. Design Trade-offs — Bot as Primitive

thomaskwaring raises four design concerns about primitive `⊥`:
1. In minimal logic, `⊥` behaves like an atom — why not represent it as `WithBot Atom`?
2. Minimal logic works fine without `⊥` (Curry-Howard approach)
3. Extra constructor makes proofs more verbose
4. Substitution should allow maps that don't preserve `⊥` (the `WithBot.some` pattern is natural for "intuitionistic conservative over minimal" results)
5. `⊤ = a → a` for arbitrary `a` is a *feature* — proofs about `⊤` should only depend on provability

The PR description must acknowledge these trade-offs rather than asserting the five-primitive design is unambiguously better. The positive case for primitive `⊥` in *temporal logic* specifically:
- The LTL formula type needs `bot` to define `neg φ := φ → ⊥` and `top := ⊥ → ⊥`, and the entire typeclass hierarchy (`HasBot`, `PropositionalConnectives`) is built around it
- In LTL specifically, `⊥` is not just an atom — the `toTemporal` embedding uses `.bot` as a distinguished element in the `next φ = φ U ⊥` encoding
- The temporal satisfiability semantics treats `bot` as `False` specifically (not as an arbitrary atom)

However, the PR description should concede that for propositional logic alone (PR #648's scope), the original `WithBot Atom` approach had merit.

### 7. Coordination with PR #607 and PR #587

PR #649 description says to coordinate with #607 and #587. The PR description should explicitly state the relationship:
- PR #607 (fmontesi's operator typeclasses) — Connectives.lean adopts the same per-operator typeclass pattern
- PR #587 — relationship should be stated

## Recommended Approach

### Phase 1: Remove LTL Semantics from PR #649 branch

1. Delete `Cslib/Logics/LTL/Semantics/Satisfies.lean` (or exclude from PR branch)
2. Remove `public import Cslib.Logics.LTL.Semantics.Satisfies` from `Cslib.lean`
3. Open a new PR with just `Satisfies.lean` after this PR merges

### Phase 2: Rebase and Reconcile with PR #536

The rebase on upstream/main (which includes PR #536) requires reconciling:
- `Cslib/Logics/Propositional/Defs.lean`: The upstream now uses `IsClassical (Atom) [Bot Atom] (S : Type*)` — our PR still uses `IsClassical (T : Theory Atom)`. Since PR #536 merged with a different design, our PR's changes to `Defs.lean` need to be rebased to not conflict.
- The `[Bot Atom]` removal in `Theory.lean` (our PR removes it from variable declaration) — check if this is still valid post-#536.
- `NaturalDeduction/Basic.lean` renaming: Our `implE`→`impE`, `orI₁`→`orI1` may conflict with what's already in upstream post-#536.

**Key check**: Run `lake build` to verify the current branch compiles after the rebase. If not, fix the conflicts.

### Phase 3: Update References

Add `Avigad2022` to `references.bib`:
```bibtex
@book{Avigad2022,
  author       = {Avigad, Jeremy},
  title        = {Mathematical Logic and Computation},
  publisher    = {Cambridge University Press},
  address      = {Cambridge},
  year         = {2022},
  isbn         = {978-1-108-84072-1}
}
```

Replace German-language citations with English alternatives:
- In all files citing `Gentzen1935`: Replace with `[Prawitz1965]` (covers same content, English) plus `[Avigad2022]` chapters 2-3
- In files citing `Johansson1937`: Consider keeping as historical source but add `[Avigad2022]` as primary
- In files citing `Wajsberg1938`, `Heyting1930`: Replace with `[Avigad2022]`
- `McKinsey1939` is English — keep

### Phase 4: Update PR Description

Revise PR #649 description to:
1. Remove mention of `LTL.Satisfies` from key contributions (split out)
2. State stacking on merged PR #536 explicitly
3. Acknowledge bot-as-primitive trade-offs per thomaskwaring's points
4. Justify `imp` on independent grounds (not by citing our own unmerged work)
5. Update references section to use Avigad2022 as primary reference
6. Add coordination note for #607/#587

### Phase 5: `imp` Naming Justification

The PR description should justify `imp` without citing our own unmerged types:
- The standard name in proof theory for implication as a constructor is `imp` (as opposed to `impl` which is typically a defined operation, e.g., `¬P ∨ Q`)
- Mathlib uses `Prop.imp` for the implication combinator
- The distinction matters: `imp` names a *constructor*, `impl` names a *derived definition* (as in upstream Modal's `Proposition.impl`)

## Evidence

### File locations
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` — exists, must be removed from this PR
- `Cslib/Logics/LTL/Syntax/Formula.lean` — exists, stays in PR
- `Cslib/Logics/Temporal/Syntax/Formula.lean` — exists, stays in PR
- `Cslib/Foundations/Logic/Connectives.lean` — exists, stays in PR
- `references.bib` — needs Avigad2022 added, German refs reviewed

### Upstream state (post-PR #536)
- `IsClassical` and `IsIntuitionistic` are now `(S : Type*) [InferenceSystem S (Proposition Atom)]`-parameterized
- `[Bot Atom]` is retained in upstream (used for `IPL`/`CPL` definitions)
- `Modal/Proposition` uses `{atom, not, and, diamond}` as primitives upstream; `impl` is derived

### PR #649 inline comments
- PR #649 has no inline code review comments yet (only issue-thread comments)
- PR #648 reviews from ctchou and thomaskwaring are the source of feedback

## Confidence Level

- **High**: LTL Semantics split required (thomaskwaring's explicit request, clear)
- **High**: Avigad2022 reference needed (both reviewers agree on English refs)
- **High**: `imp` vs `impl` — `imp` is fine and independently justified; no need to rename
- **Medium**: PR #536 reconciliation — the exact scope of conflict depends on rebase state; `lake build` verification needed
- **Medium**: Which German refs to keep vs replace — Prawitz1965 + Avigad2022 can replace Gentzen1935; Johansson1937 may be retained as historical source
- **High**: PR description must acknowledge bot-as-primitive trade-offs (both reviewers raised design concerns)
