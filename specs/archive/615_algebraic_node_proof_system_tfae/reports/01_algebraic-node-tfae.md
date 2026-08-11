# Research: Algebraic Semantic Validity as a TFAE Node

Task: 615 — Add algebraic semantic validity as a further equivalent node in the propositional
proof-system TFAE families.

Status: RESEARCHED. Every claim below was compiled against the live repo (see "Verification").

---

## 1. Executive Summary

The algebraic node can be added to the **closed** TFAE families by pure composition, with **no
new lemmas at all**: `MPL.hilbert_alg_completeness`, `IPL.hilbert_alg_completeness`, and
`CPL.hilbert_alg_completeness` are already stated *exactly* as `node-1 ↔ algebraic-validity`
for the closed families. Each fold is a one-line `tfae_have 1 ↔ 4 := <completeness theorem>`.

The context-based families can also be folded, but only through the **theory-generic
GHA-relative** form, which is not tier-matched (the CPL node would say "true in every
generalized Heyting algebra modelling the classical axiom theory", not "valid in every Boolean
algebra") and needs one new bridge lemma. A tier-matched context node is **not available**: the
relativized Lindenbaum algebra carries only a `GeneralizedHeytingAlgebra` instance.

**Recommendation: closed families only.** Add three new 4-way theorems, scoped in their own
section, and record the closed-only decision in the module docstring. Rationale in §4.

---

## 2. Reuse Check (CSLib reuse-first protocol)

| Needed | Already exists? | Where |
|---|---|---|
| Algebraic validity predicates | Yes — `GHAValid`, `HAValid`, `BAValid` | `Cslib/Logics/Propositional/Semantics/Algebra.lean:132,139,146` |
| MPL Hilbert ↔ GHA validity | Yes | `Semantics/Algebra/HilbertCompleteness.lean:96` |
| IPL Hilbert ↔ HA validity | Yes | `Semantics/Algebra/HilbertCompleteness.lean:125` |
| CPL Hilbert ↔ BA validity | Yes | `Semantics/Algebra/HilbertCompleteness.lean:158` |
| Context/strong algebraic completeness | Yes, but GHA-generic only | `Semantics/Algebra/HilbertStrongCompleteness.lean:85` |
| `Finset`-context ↔ `Set`-context bridge | **No** | would be new (§4.2) |
| HA/BA instance on relativized Lindenbaum algebra | **No** — only GHA | `Semantics/Algebra/HilbertLindenbaumRel.lean:646` |

No new abstraction is warranted. Everything the closed fold needs is already in
`Foundations`/`Semantics`. Nothing in this task requires defining a new predicate, typeclass, or
notation.

---

## 3. The Three Completeness Theorems (exact signatures)

All three live in `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean` and
all three take `{Atom : Type u}` with the algebra universe pinned to `u`:

```lean
theorem MPL.hilbert_alg_completeness {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@MinPropAxiom Atom) φ ↔ GHAValid.{u, u} φ            -- :96

theorem IPL.hilbert_alg_completeness {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@IntPropAxiom Atom) φ ↔ HAValid.{u, u} φ             -- :125

theorem CPL.hilbert_alg_completeness {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@PropositionalAxiom Atom) φ ↔ BAValid.{u, u} φ       -- :158
```

The LHS of each is **verbatim node 1** of the corresponding `...TfaeClosed` theorem
(`Derivable PropositionalAxiom φ` etc.). That is why the fold is trivial.

None of the three requires `[DecidableEq Atom]`, `[Hashable Atom]`, or any other instance —
they are stated for a bare `Type u`.

---

## 4. The "decide and record" question: context-based, closed, or both?

### 4.1 Closed families — recommended

The tier-matched validity predicates `GHAValid` / `HAValid` / `BAValid` are *weak* (empty
context) notions by definition (`Semantics/Algebra.lean:132-148`). They line up 1:1 with the
`...TfaeClosed` node 1. The fold is:

```lean
tfae_have 1 ↔ 4 := CPL.hilbert_alg_completeness
```

No `Iff.trans` gymnastics are needed here — unlike the IPL/MPL tableau folds documented at
`ProofSystemEquivalence.lean:229-243`, the `rw`-vs-`Iff.trans` universe gotcha **does not
arise**, because there is no universe-invariance bridge in the chain: both sides are already
pinned at the same `u`. The term is supplied directly, so the question never comes up.

### 4.2 Context-based families — feasible, but not recommended

`hilbert_alg_strong_complete_theory` (`HilbertStrongCompleteness.lean:85`) states

```lean
SetDerivable Axioms Γ φ ↔
  ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
    v ⊨[bot_val] AxiomTheory Axioms →
    SatisfiesTheory (AlgEvaluate v bot_val) Γ →
    AlgEvaluate v bot_val φ = ⊤
```

Two mismatches with the context-based TFAE families:

1. **Container mismatch.** TFAE node 1 is `Deriv Axioms Γ.toList φ` for `Γ : Ctx Atom`
   (`Ctx Atom := Finset (Proposition Atom)`, `NaturalDeduction/Basic.lean:128`), whereas
   `SetDerivable` takes `Γ : Set _`. A new bridge lemma is required (verified to compile, §6
   Test C):

   ```lean
   theorem deriv_toList_iff_setDerivable {Γ : Ctx Atom} :
       Deriv Axioms Γ.toList φ ↔ SetDerivable Axioms (↑Γ : Set (PL.Proposition Atom)) φ := by
     constructor
     · intro h; exact ⟨Γ.toList, fun x hx => Finset.mem_toList.mp hx, h⟩
     · rintro ⟨L, hL, ⟨d⟩⟩
       exact ⟨DerivationTree.weakening L Γ.toList φ d
         (fun x hx => Finset.mem_toList.mpr (hL x hx))⟩
   ```

2. **Tier mismatch — the decisive objection.** The strong theorem quantifies over
   *generalized Heyting algebras* for **all three** logics; the logic is distinguished only by
   which `AxiomTheory Axioms` the valuation models. So the CPL context node would *not* say
   "valid in every Boolean algebra" — it would say "true in every GHA modelling the classical
   axiom theory". Placed beside the closed CPL node (`BAValid φ`), that reads as an
   inconsistency rather than as a parallel.

   Making the context node tier-matched would require `HeytingAlgebra` and `BooleanAlgebra`
   instances on `RelLindenbaumAlgebra`. Those **do not exist**: `HilbertLindenbaumRel.lean`
   declares only `relLindenbaumGHA` (:646), while the absolute algebra does carry the tier
   instances (`hilbertLindenbaumIntHA` :695, `hilbertLindenbaumClHA` :700,
   `hilbertLindenbaumClBA` :756 in `HilbertLindenbaum.lean`). Supplying them is new
   mathematical content, well outside a discoverability task.

3. Cosmetically, the node is a five-line quantified statement; three of them would roughly
   double the file and bury the point.

**Verdict: closed families only.** The docstring must say so, and must say *why* — the
tier-matched predicates are empty-context notions, and the relativized Lindenbaum algebra
carries only a GHA instance, so a context node could only be stated in a non-tier-matched form.

---

## 5. Recommended Implementation

### 5.1 Import

Add to `ProofSystemEquivalence.lean`'s import block:

```lean
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
```

No cycle risk: `ProofSystemEquivalence.lean` is imported only by the `Cslib.lean` barrel
(verified by grep over `--include=*.lean`), so nothing under `Semantics/Algebra/` can reach it.

### 5.2 New section, after `end WithTableau`

Mirror the tableau section's typeclass hygiene, but note the constraint here is a **universe
pin**, not an extra instance. The algebraic node needs *no* new typeclass — so, unlike
`section WithTableau`, this section introduces no `variable`. Instead each theorem carries its
own `{Atom : Type u}` binder, shadowing the file-level `variable {Atom : Type*}`, because
`GHAValid`/`HAValid`/`BAValid` must be written with explicit universes `.{u, u}` and an
auto-bound `Type*` universe cannot be named. This shadowing was verified to compile without
error or warning.

Requires `universe u` (add near `variable {Atom : Type*} [DecidableEq Atom]`, or inside the new
section).

```lean
/-! ## Algebraic Semantics Folds (closed formulas only)

The algebraic validity predicates `GHAValid`, `HAValid`, and `BAValid`
(`Semantics/Algebra.lean`) are weak — empty-context — notions of validity, so each fold below
extends the corresponding `...Closed` three-way equivalence rather than the context-based one.

A context-based algebraic node was considered and deliberately not added. Strong algebraic
completeness exists (`hilbert_alg_strong_complete_theory`), but it quantifies over
*generalized* Heyting algebras for all three logics, distinguishing them only by the axiom
theory the valuation models; the tier-matched form (Boolean algebras for CPL, Heyting algebras
for IPL) would need `HeytingAlgebra`/`BooleanAlgebra` instances on `RelLindenbaumAlgebra`,
which carries only a `GeneralizedHeytingAlgebra` instance. A non-tier-matched context node
would break the parallel with the closed nodes below, so the algebraic node lives on the closed
families alone.

Unlike `section WithTableau`, these theorems need no extra typeclass; the constraint is a
universe pin. `GHAValid`/`HAValid`/`BAValid` carry a second universe for the algebra carrier,
and the Hilbert Lindenbaum construction pins it to `Atom`'s universe, so each theorem binds
`{Atom : Type u}` explicitly instead of using the file-level `Type*` variable. There is no
universe-invariance lemma for algebraic validity (contrast `ivalid_universe_invariant`), so the
`.{u, u}` pin is part of the statement. -/

section WithAlgebra

/-- **CPL Four-Way Equivalence** (closed, with algebraic semantics): ...
4. Boolean-algebra validity: `BAValid.{u, u} φ` -/
theorem cplProofSystemsWithAlgebraTfae {Atom : Type u} [DecidableEq Atom]
    (φ : PL.Proposition Atom) :
    [Derivable PropositionalAxiom φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LKProof ((∅ : Ctx Atom) ⊢ₛ ({φ} : Finset _))),
     BAValid.{u, u} φ].TFAE := by
  have h := cplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := CPL.hilbert_alg_completeness
  tfae_finish

/-- **IPL Four-Way Equivalence** (closed, with algebraic semantics): ... `HAValid.{u, u} φ` -/
theorem iplProofSystemsWithAlgebraTfae {Atom : Type u} [DecidableEq Atom]
    (φ : PL.Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ)),
     HAValid.{u, u} φ].TFAE := by
  have h := iplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := IPL.hilbert_alg_completeness
  tfae_finish

/-- **MPL Four-Way Equivalence** (closed, with algebraic semantics): ... `GHAValid.{u, u} φ` -/
theorem mplProofSystemsWithAlgebraTfae {Atom : Type u} [DecidableEq Atom]
    (φ : PL.Proposition Atom) :
    [Derivable MinPropAxiom φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (SeqProofMinimal ((∅ : Ctx Atom) ⊢ φ)),
     GHAValid.{u, u} φ].TFAE := by
  have h := mplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := MPL.hilbert_alg_completeness
  tfae_finish

end WithAlgebra
```

This is the complete implementation. Every proof above was compiled verbatim (§6).

### 5.3 Module docstring updates

- Opening paragraph: extend "...and (at the empty context) the tableau decision procedure" to
  also mention algebraic semantics, and note that the closed families now carry two independent
  fourth nodes (tableau, algebra).
- `## Main Results`: add the three `...WithAlgebraTfae` entries.
- `## Dependencies`: add `MPL.hilbert_alg_completeness`, `IPL.hilbert_alg_completeness`,
  `CPL.hilbert_alg_completeness` (algebraic folds).

### 5.4 Deliberately NOT recommended: a five-way fold

A single 5-way theorem (Hilbert, ND, sequent, tableau, algebra) would be the most discoverable
shape, but it would force `[Hashable Atom]` — needed only by the IPL/MPL tableau algorithms —
onto the algebraic equivalence, violating the task's scope-discipline instruction and the
hygiene rationale already recorded at `ProofSystemEquivalence.lean:176-186`. Two separate
four-way folds off a shared three-way core is the hygienic shape. If the planner wants the
5-way anyway, it should be *additional*, inside `section WithTableau`, never a replacement.

---

## 6. Verification (what was actually compiled)

A scratch file importing `ProofSystemEquivalence`, `Algebra.HilbertCompleteness`, and
`Algebra.HilbertStrongCompleteness` was compiled with `lake env lean` against the live build.
It contained a file-level `variable {Atom : Type*} [DecidableEq Atom]` to reproduce the real
shadowing situation.

| Test | What it checked | Result |
|---|---|---|
| A | `cplProofSystemsWithAlgebraTfae` exactly as written in §5.2 | compiles, no errors/warnings |
| B | IPL and MPL analogues | compile |
| C | `deriv_toList_iff_setDerivable` bridge (§4.2) | compiles |
| D | Context-based CPL 4-way via `hilbert_alg_strong_complete_theory` | compiles (feasible but rejected on tier-mismatch grounds, §4.2) |

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]` — no new axioms.
Zero sorries (none written). The scratch file was deleted; the working tree is unchanged.

Note: `lake env lean` runs syntax linters only. The environment linters (`lake lint`) and text
linters (`lake exe lint-style`) still need to run in the implementation phase.

---

## 7. Zero-Debt and Lint Notes

- **Zero-debt**: this task needs no `sorry`, no new axiom, no placeholder. The entire
  mathematical content already exists; the work is three one-line folds plus docstrings.
- **docBlame**: all three new theorems need docstrings — draft them in the tableau folds' style
  (numbered node list + a "Nodes 1-3 are `...Closed`; node 1 ↔ 4 is `...`" sentence).
- **defLemma**: all three are `theorem`, correct for Prop-valued results.
- **defsWithUnderscore**: `cplProofSystemsWithAlgebraTfae` etc. are lowerCamelCase, no
  underscores — consistent with the nine existing names.
- **unusedSectionVars**: the new theorems shadow the file-level `Atom`/`[DecidableEq Atom]`,
  so the section variables are simply not included; no `omit` should be needed. Confirm with
  `lake lint` after implementation.
- **shake**: run `lake shake --add-public --keep-implied --keep-prefix` after adding the import;
  the new `public import` is genuinely used and should survive, but the tool may reshuffle.
- **Existing statements**: none of the nine existing TFAE theorems is touched.

---

## 8. Optional Follow-Up (out of scope, not required)

`Cslib/Foundations/Logic/ProofSystem.lean:55` is a documentation hub that already lists the
three `hilbert_alg_completeness` theorems. Once the folds exist, a one-line cross-reference
there would improve discoverability further. This is not part of task 615's stated work.
