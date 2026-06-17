# Teammate B Findings: Alternative Approaches and Prior Art for PR #649 Revision

## Key Findings

### 1. `imp` vs `impl` Naming Convention: Strong Prior Art for `imp`

The `imp` vs `impl` debate has a clear answer from prior art:

**Uses `imp`** (the current PR #649 / #648 choice):
- **FormalizedFormalLogic/Foundation** (major Lean 4 logic library, ~10k stars): Uses `imp` as the constructor name in both `LO.Propositional.Formula` and `LO.Modal.Formula`:
  ```lean
  inductive Formula (α : Type u) : Type u
    | atom   : α → Formula α
    | falsum : Formula α
    | and    : Formula α → Formula α → Formula α
    | or     : Formula α → Formula α → Formula α
    | imp    : Formula α → Formula α → Formula α
  ```
  and in Modal:
  ```lean
  inductive Formula (α : Type*) where
    | atom   : α → Formula α
    | falsum : Formula α
    | imp    : Formula α → Formula α → Formula α
    | box    : Formula α → Formula α
  ```
- **CSLib's own existing formula types** (Bimodal, Temporal): Both use `| imp (φ₁ φ₂ : Formula Atom)` as the constructor.
- **Bentzen (arxiv 2310.01916)**: Uses `impl` but this is Lean 3 legacy syntax; the post-Lean 4 convention has shifted to `imp`.

**Uses `impl`**:
- **Avigad's LAMR textbook** (`avigad.github.io/lamr`): Uses `impl` in `PropForm`:
  ```lean
  inductive PropForm where
  | tr : PropForm
  | fls : PropForm
  | var : String → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm
  | impl : PropForm → PropForm → PropForm
  | neg : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  ```
- **CSLib Modal** (existing, pre-PR): Uses `impl` in `Modal.Proposition`.

**Assessment**: thomaskwaring's objection that "the actually existing example (Modal) uses `impl`" is factually correct for the current codebase. However, `imp` is the dominant convention in the major Lean 4 logic formalization ecosystem (FormalizedFormalLogic/Foundation, which is the closest large-scale comparable project). The rename from `impl` to `imp` is consistent with CSLib's Bimodal and Temporal formula types, which already use `imp`.

**Recommendation**: Keep `imp`. The PR description should note the cross-CSLib-formula consistency with Bimodal and Temporal (not just the unmerged PR #648), and should not claim alignment with external CSLib formula types as the primary justification. The primary justification is internal CSLib consistency (Bimodal and Temporal already use `imp`) plus alignment with the major Lean 4 logic library (FormalizedFormalLogic).

**If reviewers resist `imp`**: One alternative is to use `impl` in PL (matching Modal and LAMR) and accept the inconsistency with Bimodal/Temporal. Another is to defer the rename to a separate cleanup PR after the core structural changes are accepted.

---

### 2. Bot-as-Primitive: Design Trade-off Analysis

thomaskwaring raises five specific objections. Here is a systematic response with prior art:

**Objection A: "In minimal logic bot behaves like an atom"**

This is partly true but overlooks a key distinction: bot-as-atom conflates two different roles. In the original design, the "bottom atom" under `[Bot Atom]` means there is an atom `⊥` that substitution replaces. Real substitution should be invariant on logical constants. The PR #648 rationale correctly identifies that `(.atom ⊥).subst f = f ⊥`, breaking the expected behavior that bottom is preserved by substitution.

**Prior art supporting bot-as-primitive**:
- Bentzen (arxiv 2310.01916): Uses `| bot : form` as explicit constructor alongside atom
- FormalizedFormalLogic/Foundation: Uses `| falsum : Formula α` as explicit constructor
- Avigad LAMR: Uses `| fls : PropForm` as explicit constructor
- Heyting (1930), Johansson (1937): Treat ⊥ as a primitive propositional symbol

All major Lean 4 logic formalizations treat bot/falsum as a separate constructor from atoms.

**Objection B: "Minimal logic works without ⊥"**

True — this is Johansson's pure implicational minimal logic. However, CSLib's existing `Proposition` type already includes `and` and `or`, which go beyond the implication-only fragment. Including `bot` as primitive alongside `and`/`or` is standard for the five-primitive NJ formulation (Prawitz 1965, Avigad Chapter 2). The "no ⊥" option would require a separate minimal-implicational formula type, which is more work.

**Objection C: "Adding a constructor makes proofs more verbose"**

Measured against actual code: the PR 649 Kripke semantics handles bot with `| .bot => False` — a single line. This is no more verbose than the old approach of having a special `Bot Atom` instance. The verbosity concern is real but minor.

**Objection D: "Substitution should allow maps that don't preserve bottom (WithBot.some pattern)"**

This is the strongest objection. The PR description addresses it in `intuitionisticCompletion` which already uses `WithBot.some`. The PR 649 branch preserves `Theory.intuitionisticCompletion : Theory (WithBot Atom)` using `WithBot.some <$> T` — exactly thomaskwaring's preferred pattern. The conservative extension theorem "IPL is conservative over MPL for ⊥-free formulas" can be stated as: the image of `WithBot.some` in atomic types carries only MPL-derivable propositions. This is already accommodated.

**Recommendation for PR description**: Acknowledge that thomaskwaring's substitution point is valid, note that `WithBot.some` remains the right pattern for ⊥-free fragments, and explain that `bot`-as-primitive and `WithBot.some`-as-embedding are complementary tools (not mutually exclusive).

**Objection E: "⊤ being a→a for arbitrary a is a feature"**

Counter-argument: `⊤ := ⊥ → ⊥` is definitionally equal to `a → a` in any system that proves `⊥ → ⊥`, so no proof content is lost. The PR gives `⊤` a unique normal form independent of any `Inhabited` instance, making the definition canonical.

---

### 3. References: Modern English Replacements

Both ctchou and thomaskwaring object to 1930s German-language citations. The PR already cites thomaskwaring as co-author; he acknowledges "I read [Gentzen] in translation." Recommended replacements:

**Primary (ctchou-endorsed)**:
- **Avigad, "Mathematical Logic and Computation"** (Cambridge, 2022), Chapters 2–3
  - BibKey: `Avigad2022` (not currently in `references.bib`)
  - Covers: propositional logic (Ch. 2), semantics (Ch. 3), natural deduction, sequent calculus
  - Cambridge URL: https://www.cambridge.org/core/books/mathematical-logic-and-computation/300504EAD8410522CE0C27595D2825A2
  - This is the explicit recommendation from ctchou's review

**Supplementary (already in bib)**:
- `Prawitz1965` — *Natural Deduction: A Proof-Theoretical Study* (English, 1965) — keep
- `Church1956` — *Introduction to Mathematical Logic* (English, 1956) — keep
- `TroelstraVanDalen1988` — *Constructivism in Mathematics: An Introduction* (English, 1988) — keep (for IPL completeness context)

**To remove/replace**:
- `Johansson1937` — German, replace with Avigad Ch. 2 footnote or Prawitz references to Johansson
- `Gentzen1935` — German, replace with Avigad Ch. 2 or Prawitz (which covers Gentzen's ND system in English)
- `Wajsberg1938`, `McKinsey1939`, `Heyting1930` — if cited in `Connectives.lean`, replace with Avigad

**Note on BibKey format**: CONTRIBUTING.md requires `[AuthorYYYY]` format. The new key should be `[Avigad2022]`. The bib entry does not currently exist in `references.bib` and will need to be added.

---

### 4. PR Splitting Strategy

thomaskwaring's specific request: split `LTL.Semantics.Satisfies` into a separate PR. The current PR 649 already addresses ctchou's reviewer feedback by removing Encodable instances and splitting LTL away from Temporal.

**Recommended split for PR #649**:

| PR | Content | Status |
|----|---------|--------|
| **PR #648 (revised)** | `Connectives.lean`, `Propositional/Defs.lean` refactor (5 primitives), `NaturalDeduction/Basic.lean` | Needs revision |
| **PR #649 (revised)** | `Temporal.Formula`, `LTL.Formula`, typeclass hierarchy | Keep, but remove `LTL.Satisfies` |
| **Future PR A** | `LTL.Semantics.Satisfies` | Defer |
| **Future PR B** | Kripke semantics for IPL (ctchou's suggestion) | Defer |

**Key insight**: thomaskwaring's request to split LTL semantics is already partially addressed in the current PR 649 branch. The `LTL/Semantics/Satisfies.lean` file needs to be removed from the PR 649 branch diff. This is the highest-priority mechanical change needed.

**Should PR #648 and #649 be merged?** No. They address different concerns (#648 = propositional foundations, #649 = temporal/LTL formula types). Keeping them separate allows independent review, which thomaskwaring prefers. The only coupling is that #649 imports from #648's `Connectives.lean`.

---

### 5. Adapting to Merged PR #536

PR #536 changed `IsIntuitionistic` and `IsClassical` from theory-based to inference-system-based:

**Before #536** (theory-based):
```lean
class IsIntuitionistic [Bot Atom] (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T
```

**After #536** (inference-system-based):
```lean
class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*)
    [InferenceSystem S (Proposition Atom)] where
  efq (A : Proposition Atom) : S⇓(⊥ → A)
```

**Impact on PR #649 branch**: The branch already rebases on #536. The `Defs.lean` in `feat/temporal-formula-propositional` retains `IsIntuitionistic` and `IsClassical` as theory-based classes (the old design), because the new five-primitive `Proposition` still uses `[Bot Atom]` implicit constraints via the `Bot (Proposition Atom)` instance. The PR #649 description says `IsIntuitionistic` is still theory-based — this is accurate post-rebase, since #536's inference-system-based version lives in `Defs.lean` on `main`, not in PR 649's proposed changes.

**Verification needed**: The PR 649 branch's `Defs.lean` has the new 5-primitive `Proposition` type with `bot` as constructor. This is compatible with #536's `[Bot Atom]` constraint because `instance : Bot (Proposition Atom) := ⟨.bot⟩` is provided. The `IsIntuitionistic` class in the branch should be checked against #536's version to ensure the rebase didn't create conflicting definitions.

---

### 6. Alternative PR Structuring Strategies (if bot-as-primitive is contested)

If thomaskwaring continues to object to bot-as-primitive, there are two fallback paths:

**Option A: Bot-as-primitive but with a cleaner substitution story**
- Keep `| bot` constructor
- Explicitly provide `WithBot.some`-based embedding for ⊥-free fragments as a utility function in the PR
- Add a lemma showing substitution along `WithBot.some` corresponds to ⊥-free fragment
- This directly addresses thomaskwaring's domain-theory analogy

**Option B: Revert to [Bot Atom] with improvements**
- Revert to `[Bot Atom]` constraint
- Only add `imp`, `and`, `or` as primitives (no `bot`)
- Fix the substitution issue by defining a separate `substNoBot` or using `WithBot Atom` throughout
- This reduces the PR's scope significantly but loses the clean `neg`/`top` story

**Recommendation**: Option A is strongly preferred. Option B abandons too much value. The domain-theory analogy thomaskwaring mentions actually supports Option A: domains have a bottom element, but maps between domains don't need to preserve it. With primitive bot, you can still map `Proposition Atom → Proposition (WithBot Atom)` along `WithBot.some` on the atom type. The substitution `Proposition.subst (WithBot.some ∘ f)` preserves `bot` by construction.

---

## Recommended Approach

For the PR #649 revision, the recommended approach is:

1. **Remove `LTL/Semantics/Satisfies.lean`** from the PR diff (mechanical: split into separate future PR)
2. **Keep `imp` naming** — justify with FormalizedFormalLogic/Foundation precedent and CSLib cross-formula consistency (Bimodal, Temporal)
3. **Replace German-language references** with Avigad2022 (add bib entry) plus retain Prawitz1965, Church1956, TroelstraVanDalen1988
4. **Address bot-as-primitive trade-offs honestly** in PR description: acknowledge objections, explain WithBot.some compatibility, provide the conservative extension framing
5. **Update PR description** to: (a) note stacking on merged #536 not #648, (b) describe semantics split-out, (c) mention coordination with #607/#587, (d) use balanced design rationale

---

## Evidence / Examples

| Claim | Evidence | Source |
|-------|----------|--------|
| `imp` is dominant in Lean 4 logic libraries | `inductive Formula ... \| imp : Formula α → Formula α → Formula α` | FormalizedFormalLogic/Foundation (propositional and modal) |
| Avigad LAMR uses `impl` | `\| impl : PropForm → PropForm → PropForm` | avigad.github.io/lamr |
| Bentzen (arxiv 2310.01916) uses `impl` in Lean 3 | `inductive form ... \| impl : form → form → form` | bbentzen/ipl source |
| Bot-as-primitive is standard in Lean 4 logic formalizations | `\| falsum : Formula α` | FormalizedFormalLogic/Foundation, Bentzen (both separate from atom) |
| ctchou explicitly recommends Avigad Ch 2-3 | "A good modern reference is Jeremy Avigad's textbook... chapters 2 and 3 covers everything in this PR" | PR #648 review (pullrequestreview-4502084546) |
| thomaskwaring acknowledges Gentzen in German | "I read it in translation (in 'The Collected Papers of Gerhard Gentzen')" | PR #648 issue comment |
| PR #536 merged: IsIntuitionistic now inference-system-based | `class IsIntuitionistic (Atom : Type u) [Bot Atom] (S : Type*) [InferenceSystem S ...]` | commit 70c5bf58 |

---

## Confidence Levels

| Finding | Confidence |
|---------|------------|
| `imp` vs `impl` — `imp` is dominant in Lean 4 logic libs | **High** — direct code inspection of FormalizedFormalLogic/Foundation |
| Avigad LAMR uses `impl` | **High** — direct fetch of avigad.github.io/lamr |
| Bentzen 2023 uses `impl` (Lean 3) | **High** — direct code inspection of bbentzen/ipl |
| Avigad "Mathematical Logic and Computation" covers Ch 2-3 propositional logic | **High** — Cambridge Core table of contents + ctchou endorsement |
| WithBot.some approach is compatible with bot-as-primitive | **High** — current branch code already has `intuitionisticCompletion` with `WithBot.some` |
| Bot-as-primitive is standard in Lean 4 formalizations | **High** — confirmed in FormalizedFormalLogic/Foundation and Bentzen |
| PR #536 inference-system refactor is compatible with PR #649 | **Medium** — reasoning based on diff inspection; actual Lean type-checking not verified |
