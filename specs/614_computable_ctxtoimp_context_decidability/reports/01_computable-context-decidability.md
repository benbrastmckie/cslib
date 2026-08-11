# Research Report: Computable Context-Based Decidability for LJ/LK

**Task**: 614 — Give `ctxToImp` a computable definition so the four context-based `Decidable`
instances for the propositional sequent calculi stop being `noncomputable`.

**Status**: RESEARCHED — a zero-cost route exists and has been **empirically verified** by
compiling and evaluating a complete prototype of all four instances against the live tree.

---

## 1. Executive Summary

| Question | Answer |
|----------|--------|
| Can the four instances become computable? | **Yes**, verified working prototype |
| Does it require a new typeclass hypothesis (`[LinearOrder Atom]`)? | **No** |
| Does it change any public statement (Finset contexts preserved)? | **No** |
| Can `ctxToImp : Ctx Atom → Proposition Atom → Proposition Atom` itself become computable? | **No** — genuinely impossible without extra structure (see §3) |
| Downstream breakage risk | **None** — zero references to the affected declarations outside the two files |
| Does a non-empty-context decision actually evaluate? | **Yes**, verified: `{p, p→q} ⊢ q` evaluates to `true`, `{q} ⊢ p` to `false` |

The task description's own framing must be split in two. Its **title ask** ("give `ctxToImp` a
computable definition") is not achievable. Its **stated goal** ("the four context-based
`Decidable` instances stop being `noncomputable`") is fully achievable, at no cost, by a route
neither of the description's two proposed routes covers.

---

## 2. Confirmation of the Defect Inventory

The task's inventory was verified against the live tree at the stated locations:

| Declaration | File:Line | Currently |
|-------------|-----------|-----------|
| `ctxToImp` | `Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean:82` | `noncomputable def` |
| `ljProofDeductionFwd` | LJ/Decidability.lean:112 | `noncomputable def` |
| `ljProofDeductionBwd` | LJ/Decidability.lean:170 | `noncomputable def` |
| `instDecidableLJDerivable` | LJ/Decidability.lean:197 | `noncomputable instance` |
| `instDecidableDerivableInIPL` | LJ/Decidability.lean:218 | `noncomputable instance` |
| `lkProofDeductionFwd` | LK/Decidability.lean:92 | `noncomputable def` |
| `lkProofDeductionBwd` | LK/Decidability.lean:153 | `noncomputable def` |
| `instDecidableLKDerivable` | LK/Decidability.lean:174 | `noncomputable instance` |
| `instDecidableDerivableInCPL` | LK/Decidability.lean:190 | `noncomputable instance` |

The already-computable list-level machinery the fix builds on:

| Declaration | File:Line | Status |
|-------------|-----------|--------|
| `listToImp` | LJ/Decidability.lean:72 | plain computable `def` |
| `ljListDeductionFwd` | LJ/Decidability.lean:91 | plain computable `def` |
| `ljListDeductionBwd` | LJ/Decidability.lean:130 | plain computable `def` |
| `lkListDeductionFwd` | LK/Decidability.lean:65 | plain computable `def` |
| `lkListDeductionBwd` | LK/Decidability.lean:110 | plain computable `def` |

**`Ctx Atom` is `Finset (Proposition Atom)`** (`Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:128`).
This single fact drives everything below.

**Reference grounding for the two bridge lemmas the instances route through** (both unchanged by
this task):
- `lj_iff_ivalid : IValid.{u,u} φ ↔ Nonempty (LJProof (∅ ⊢ φ))` — LJ/Completeness.lean:288
- `ivalid_universe_invariant (φ) : IValid.{_,v} φ ↔ IValid.{_,0} φ` — Tableau/Intuitionistic/DecisionProcedure.lean:165
- `instDecidableIValid (φ) : Decidable (IValid.{_,0} φ)` — Tableau/Intuitionistic/DecisionProcedure.lean:107
- `lk_iff_tautology` — LK/Completeness.lean:377
- `instDecidableTautologyTableau` (priority 100) — Tableau/Classical/DecisionProcedure.lean:81

---

## 3. Adversarial Finding: The Title Ask Is Impossible

`ctxToImp` cannot be made computable at its current type, with or without cleverness, and this
should be stated in the plan rather than silently worked around.

A computable function `Finset α → β` must factor through the underlying `Multiset`, i.e. it must
be **invariant under permutation of the underlying list**. `listToImp` is not: `A → B → C` and
`B → A → C` are distinct `Proposition Atom` values (interderivable, but not equal). Therefore no
computable `Ctx Atom → Proposition Atom → Proposition Atom` extending `listToImp` exists.

Three escape hatches were checked and all fail:
- **`Finset.fold`** requires `[Std.Commutative op] [Std.Associative op]`
  (Mathlib/Data/Finset/Fold.lean:32). `Proposition.imp` is neither. Confirmed by reading the
  source, matching the task description's claim.
- **`Hashable Atom`** yields a `UInt64` but no injection, hence no total order.
- **`Multiset.toList`** is itself `noncomputable def toList (s) := s.out` — choice-based. The
  task description is right that this, not `Finset.toList` per se, is the root.

So the correct framing for the plan is: **`ctxToImp` stays `noncomputable`, and that is
harmless**, because nothing that needs to *run* will depend on it any more. `noncomputable` is
only a defect when it blocks a decision procedure; on a statement-level encoding used inside
theorem statements it costs nothing.

---

## 4. Route Analysis

### Route 1 — `[LinearOrder Atom]` + `Finset.sort` (task description's option 1)

Works, but pays a real price: it adds a hypothesis to all four **public** instances, whereas
`instDecidableIValid`/`instDecidableTautologyTableau` need only `[DecidableEq Atom] [Hashable Atom]`.
Every downstream user of context decidability would then need a linear order on atoms that the
mathematics does not require. **Not recommended.**

### Route 2 — Restate over `List` contexts (task description's option 2, "cheapest real fix")

**This route does not actually solve the stated problem.** The four instances are stated for
`Γ : Ctx Atom = Finset (Proposition Atom)`, because `Sequent`/`LKSequent`/`DerivableIn` are all
defined over `Finset` contexts. Restating the *instances* over `List` contexts would either
(a) change the sequent type — far out of scope, or (b) only supply decidability for the special
case `Γ = l.toFinset` for a *given* list `l`, leaving arbitrary `Γ : Finset` undecided, which is
precisely the API users have. The list-level lemmas being computable is a necessary ingredient,
not a sufficient fix. **Rejected as stated**; its computable list-level lemmas are however
reused verbatim by Route 3.

### Route 3 (RECOMMENDED) — Subsingleton quotient elimination

`Decidable p` is a `Subsingleton`. Therefore one may eliminate from the `Multiset` quotient into
it **computably**, choosing an arbitrary list representative, without ever needing a canonical
one — precisely because the *result* of the choice (the decision) is provably independent of the
choice, even though the intermediate formula is not.

This is a well-established Mathlib idiom, with two direct precedents:

- `Multiset.decidableMem` — `Mathlib/Data/Multiset/Defs.lean:129`:
  `Quot.recOnSubsingleton s fun l ↦ inferInstanceAs (Decidable (a ∈ l))`
- **`Finset.Nontrivial.instDecidablePred`** — `Mathlib/Data/Finset/Insert.lean:216`, an exact
  structural match for our case (Finset, motive carrying the `Nodup` hypothesis, applied to
  `s.nodup`):
  ```
  Quotient.recOnSubsingleton (motive := fun (s : Multiset α) =>
      (h : s.Nodup) → Decidable (Finset.Nontrivial ⟨s, h⟩))
    s.val (fun l h => …) s.nodup
  ```

The reconstruction `⟨Γ.val, Γ.nodup⟩` is **definitionally** `Γ` by structure eta, so no cast and
no rewriting is needed at the instance level — the motive simply mentions `⟨s, h⟩` and the final
application to `Γ.nodup` lands on the right type on the nose.

**Cost: zero.** No new hypothesis, no statement change, no new axiom, no `sorry`.

---

## 5. Verified Prototype

Both files' instances were prototyped in scratch modules and compiled against the live tree with
`lake env lean` (Lean `v4.33.0-rc1`, Mathlib rev `169c26b5`). **All compiled clean with no
`noncomputable` marker**, and all evaluated to the semantically correct verdicts.

### 5.1 LJ (intuitionistic)

```lean
/-- List-level decidability of LJ derivability … -/
def ljListDerivableDecidable (l : List (Proposition Atom))
    (h : (↑l : Multiset (Proposition Atom)).Nodup) (A : Proposition Atom) :
    Decidable (Nonempty (LJProof ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ A))) :=
  letI : Decidable (IValid (listToImp l A)) :=
    decidable_of_iff (IValid.{_, 0} (listToImp l A)) (ivalid_universe_invariant _).symm
  decidable_of_iff (IValid (listToImp l A)) <| by
    have hset : (⟨(↑l : Multiset (Proposition Atom)), h⟩ : Finset (Proposition Atom))
        = l.toFinset := List.toFinset_eq h
    rw [hset]
    constructor
    · intro hv
      obtain ⟨d⟩ := lj_iff_ivalid.mp hv
      have hd := ljListDeductionBwd l ∅ A d
      rw [Finset.union_empty] at hd
      exact ⟨hd⟩
    · rintro ⟨d⟩
      refine lj_iff_ivalid.mpr ⟨ljListDeductionFwd l ∅ A ?_⟩
      rw [Finset.union_empty]
      exact d

instance instDecidableLJDerivable {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (Nonempty (LJProof (Γ ⊢ A))) :=
  Quotient.recOnSubsingleton (motive := fun (s : Multiset (Proposition Atom)) =>
      (h : s.Nodup) → Decidable (Nonempty (LJProof ((⟨s, h⟩ : Finset (Proposition Atom)) ⊢ A))))
    Γ.val (fun l h => ljListDerivableDecidable l h A) Γ.nodup

instance instDecidableDerivableInIPL {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (LJProof (Γ ⊢ A))) nd_iff_lj.symm
```

Note the universe bridge (`letI` + `ivalid_universe_invariant`) is preserved verbatim from the
existing instance — the task's instruction to keep it load-bearing is honoured.

### 5.2 LK (classical)

Structurally identical, but **simpler**: `instDecidableTautologyTableau` is not universe-pinned,
so no `letI` bridge is needed (matching the existing LK instance, which also has none).

```lean
def lkListDerivableDecidable (l : List (Proposition Atom))
    (h : (↑l : Multiset (Proposition Atom)).Nodup) (A : Proposition Atom) :
    Decidable (Nonempty (LKProof ((⟨↑l, h⟩ : Finset (Proposition Atom)) ⊢ₛ {A}))) :=
  decidable_of_iff (Tautology (listToImp l A)) <| by
    have hset : … = l.toFinset := List.toFinset_eq h
    rw [hset]
    constructor
    · intro hv
      obtain ⟨d⟩ := lk_iff_tautology.mp hv
      have hd := lkListDeductionBwd l ∅ A d
      rw [Finset.union_empty] at hd
      exact ⟨hd⟩
    · rintro ⟨d⟩
      refine lk_iff_tautology.mpr ⟨lkListDeductionFwd l ∅ A ?_⟩
      rw [Finset.union_empty]
      exact d

instance instDecidableLKDerivable {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (Nonempty (LKProof (Γ ⊢ₛ {A}))) :=
  Quotient.recOnSubsingleton (motive := fun (s : Multiset (Proposition Atom)) =>
      (h : s.Nodup) → Decidable (Nonempty (LKProof ((⟨s, h⟩ : Finset (Proposition Atom)) ⊢ₛ {A}))))
    Γ.val (fun l h => lkListDerivableDecidable l h A) Γ.nodup

instance instDecidableDerivableInCPL {Γ : Ctx Atom} {A : Proposition Atom} :
    Decidable (DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom) (Γ ⊢ A)) :=
  decidable_of_iff (Nonempty (LKProof (Γ ⊢ₛ {A}))) nd_iff_lk.symm
```

### 5.3 Measured evaluation results

All via `#eval decide (…)` on `Atom := Bool` (`false` = p, `true` = q):

| Expression | Result | Expected |
|------------|--------|----------|
| LJ `{p} ⊢ p` | `true` | ✓ |
| LJ `{q} ⊢ p` | `false` | ✓ |
| LJ `{p, p → q} ⊢ q` (**non-empty context, the task's target case**) | `true` | ✓ |
| LJ `∅ ⊢ p → p` | `true` | ✓ |
| LJ `∅ ⊢ p ∨ (p → ⊥)` | `false` | ✓ (correctly intuitionistic) |
| LK `{p} ⊢ p` | `true` | ✓ |
| LK `{q} ⊢ p` | `false` | ✓ |
| LK `∅ ⊢ p ∨ (p → ⊥)` | `true` | ✓ (correctly classical) |
| IPL `DerivableIn IntPropAxiom ({p} ⊢ p)` | `true` | ✓ |
| IPL `DerivableIn IntPropAxiom ({q} ⊢ p)` | `false` | ✓ |
| CPL `DerivableIn PropositionalAxiom ({p} ⊢ p)` | `true` | ✓ |

The LJ/LK contrast on `p ∨ ¬p` is the strongest single piece of evidence that the two instances
are wired to the right decision procedures and not accidentally to each other.

### 5.4 A failed variant, recorded so the implementer does not repeat it

Fully **inlining** the helper into the instance body (avoiding a named `def`) does **not**
elaborate: inside the `Quotient.recOnSubsingleton` lambda the representative appears as `⟦l⟧`
rather than `↑l`, and `rw [show (⟨↑l, h⟩ : Finset _) = l.toFinset from List.toFinset_eq h]`
fails with

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern { val := ↑l, nodup := h }
in the target expression … Nonempty (LJProof ({ val := ⟦l⟧, nodup := h }, A))
```

The named-helper form avoids this because the coercion is resolved by *unification* against the
helper's declared type rather than by syntactic rewriting. **Use the named helper.**

Also note: `List.toFinset_eq h : (⟨↑l, h⟩ : Finset _) = l.toFinset` — this orientation, not its
symm. (A first attempt with `.symm` failed with a type mismatch.)

---

## 6. Testing: `#eval`, Never `decide`

The task's VERIFY line asks for a `#guard_msgs`-protected computation. That is the right and the
**only** available idiom here.

**Verified**: `by decide` on these instances **fails**, exactly as
`CslibTests/TableauConformance.lean`'s header documents for the tableau drivers generally:

```
Tactic `decide` failed … After unfolding the instances decidable_of_decidable_of_iff,
decidable_of_iff, instDecidableEqBool, Bool.decEq, instDecidableIValid,
instDecidableLJDerivable, and ljListDerivableDecidable, reduction got stuck …
```

Read that list carefully: the kernel unfolded straight *through* the new `Quotient.recOnSubsingleton`
instance and the new helper without difficulty, and only got stuck at the pre-existing
`WellFounded.fix` inside the tableau driver. **The new construction introduces no new kernel
obstruction**; it inherits the existing one.

**Verified working test idiom** (both positive and negative cases pass `#guard_msgs`):

```lean
/-- info: true -/
#guard_msgs in
#eval decide (Nonempty (LJProof
  (({Proposition.atom false, Proposition.imp (Proposition.atom false) (Proposition.atom true)}
      : Ctx Bool) ⊢ Proposition.atom true)))

/-- info: false -/
#guard_msgs in
#eval decide (Nonempty (LJProof (({Proposition.atom true} : Ctx Bool) ⊢ Proposition.atom false)))
```

Header requirement (verified): the test module needs **both** `public import X` and
`public meta import X` for the Decidability modules, matching `CslibTests/TableauConformance.lean`
and `CslibTests/Propositional.lean`. A plain `import` alone gives
"may not access declaration … imported as 'meta'" on constructor references.

`CslibTests/*.lean` do **not** import `Cslib.Init` (confirmed against `CslibTests/Propositional.lean`),
so `checkInitImports` is not a concern for the new test file.

---

## 7. CI and Infrastructure Consequences (do not skip these)

### 7.1 The axiom-census ratchet will fail unless handled

`scripts/check-axiom-census.sh` + `scripts/axiom-census-baseline.txt` is an **exact-set** ratchet
wired into `.github/workflows/lean_action_ci.yml` (step "axiom-census ratchet", `if: always()`).
Two of the four instances are already in the baseline:

```
Cslib.Logic.PL.instDecidableDerivableInIPL   …/LJ/Decidability.lean   Cslib.Logic.PL.instDecidableLJDerivable
Cslib.Logic.PL.instDecidableLJDerivable      …/LJ/Decidability.lean   Cslib.Logic.PL.instDecidableIValid
```

(They are `sorryAx`-tainted transitively through `intuitionisticTableau_complete`. The two LK
instances are absent from the baseline — the classical tableau is sorry-free.)

Consequence: the **new public LJ helper `ljListDerivableDecidable` will enter the live tainted
set** and the ratchet fails with exit 1 until the baseline is regenerated. The LK helper will
*not* appear (sorry-free chain).

Required step in the plan: after the change builds green, run
```
bash scripts/check-axiom-census.sh --update
```
and commit the baseline diff, which should be **exactly one added line** for the LJ helper (plus
a possible column-3 "reason" churn on `instDecidableLJDerivable`, which the comparison ignores
but `--update` rewrites). Any larger diff means something unintended changed and should be
investigated, not committed.

Alternative if baseline churn is unwanted: mark the LJ helper `private` (the census filters on
the *exported* environment, `env.setExporting true`). Not recommended — it hides a genuinely
useful list-level result and fights the file's `@[expose] public section`.

### 7.2 New test file must be registered

`CslibTests.lean` is an explicit `public import` barrel and `lake exe mk_all --check` runs in CI.
A new `CslibTests/…` file must be added to that barrel (alphabetically) — or the `#eval`s can be
appended to the existing `CslibTests/Propositional.lean`, which needs no barrel change but does
need the two new imports. Either is acceptable; a dedicated file is more in keeping with the
repo's many focused test modules.

### 7.3 No barrel change under `Cslib/`

No new files under `Cslib/` are needed, so `Cslib.lean` is untouched.

---

## 8. Blast Radius

A repo-wide grep for `ctxToImp`, all four instance names, and `ljProofDeduction*`/`lkProofDeduction*`
found **zero references outside the two Decidability files**. There is no downstream consumer to
break, and no `Decidable` instance-resolution behaviour change (types are byte-identical; only
the `noncomputable` marker and the definitional body change).

---

## 9. Recommended Change Set

**`Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean`**
1. Add `ljListDerivableDecidable` (new, computable, docstring'd) in the "Decidability Instances"
   section, before the instances.
2. Replace `instDecidableLJDerivable`'s body (:197-212) with the `Quotient.recOnSubsingleton`
   form; drop `noncomputable`.
3. Drop `noncomputable` from `instDecidableDerivableInIPL` (:218); body unchanged.
4. Leave `ctxToImp` (:82), `ljProofDeductionFwd` (:112), `ljProofDeductionBwd` (:170) as
   `noncomputable` — **rewrite their docstrings** to say the noncomputability is inherent (order
   of a `Finset` is a genuine choice) and no longer affects any decision procedure.
5. Update the instance docstrings (:189, and the Strategy block at :17-35) — remove
   "The instance is `noncomputable` because `ctxToImp` uses `Finset.toList`" and describe the
   representative-independence argument instead. Keep the existing "Universe note" (:191-196)
   verbatim; it is still exactly right.

**`Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean`**
6. Add `lkListDerivableDecidable`; rewrite `instDecidableLKDerivable` (:174) and drop
   `noncomputable`; drop `noncomputable` from `instDecidableDerivableInCPL` (:190).
7. Same docstring corrections (:91, :152, :173, and the Strategy block at :18-31).

**Tests**
8. New `CslibTests/…` module (or an addition to `CslibTests/Propositional.lean`) with at minimum
   one `#guard_msgs in #eval` for a **non-empty-context** LJ decision and one for LK, plus
   negative cases. Register in `CslibTests.lean` if a new file.

**Ratchet**
9. `bash scripts/check-axiom-census.sh --update`; verify the diff is the single expected line.

**Verification order** (per `.claude/rules/cslib.md`)
10. `lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
    `lake test` → `lake exe mk_all --module`. Compare `lake lint` output against the two known
    pre-existing warnings in this subtree, which are explicitly **not** this task's to fix.

Suggested phase split (each ≈ one agent run): (P1) LJ file, (P2) LK file, (P3) tests + barrel,
(P4) ratchet + full CI sweep.

---

## 10. Explicitly Out of Scope / Do Not Touch

- `decidableDerivableIntPropAxiomFMP` (Metalogic/IntDecidability.lean:489) and
  `decidableDerivableMinPropAxiomFMP` (MinDecidability.lean:445) — noncomputable for an unrelated
  and irreducible reason (`Fintype.ofInjective`). The task description's analysis here is correct
  and was not re-litigated. Leave them alone.
- The closed-context restriction on the tableau TFAE folds (ProofSystemEquivalence.lean:176-186).
- The two pre-existing lint warnings in this subtree.
- Any `[LinearOrder Atom]`-based `ctxToImp` variant — deliberately not added.

## 11. Note for the LM-Decidability Follow-On

The coordination note in the task description is worth acting on: the Route 3 pattern
(`Quotient.recOnSubsingleton` on `Γ.val` + a list-level `Decidable` helper) transfers verbatim to
LM/minimal-logic context decidability, given `mvalid_universe_invariant` and `instDecidableMValid`
which mirror the intuitionistic pair exactly. Whoever takes that item should inherit this shape
rather than the `Finset.toList` taint.

---

## 12. Zero-Debt Compliance

No `sorry`, no new axiom, no vacuous definition, and no deferral is proposed anywhere in this
report. The recommended route was compiled and executed end to end before being recommended. The
only remaining `noncomputable` markers after the change (`ctxToImp` and the four Finset-level
deduction defs) are inherent, documented, and block nothing executable — they are not debt but a
correct statement of a mathematical fact.
