# Research Report: `ConjImpBotMinAxiom` — MPL⟨∧,→,⊥,⊤⟩ Fragment Axiom System (Task 353)

## Summary

Task 353 introduces `ConjImpBotMinAxiom`, the fourth element of the MPL fragment tower. It is
**exactly** `ConjImpBotAxiom` minus the ex-falso constructor (`efq : ⊥ → φ`). This is the point
where the MPL chain diverges from IPL: ⊥ becomes a "free" atom-like constant rather than the least
element with explosion. Every required piece (definition, two subsumptions, substitution closure,
fragment-predicate compatibility, deduction-theorem instance) has a direct, verified template in
the existing code. **No new lemmas, no Mathlib search, no sorry risk.** This is a faithful
mechanical transcription.

All work lives in the existing file
`Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`, appended immediately after the
`ConjImpBotAxiom` block (after line 394, before `end Cslib.Logic.PL` at line 396). `ConjImpBotAxiom`
is left untouched.

## Reuse Check (CSLib reuse-first)

- `MinPropAxiom` already exists (`Axioms.lean:126`) and contains every target constructor
  (`implyK`, `implyS`, `andI`, `andE1`, `andE2`) under identical names — confirmed by direct read.
- `ConjImpBotAxiom` (`FragmentAxioms.lean:259`) is the structural template; the new type is it
  minus one constructor.
- `hasDeductionTheorem`, `propDerivationSystem`, `imp_isOrFree`, `and_isOrFree`,
  `Proposition.IsOrFree`, `Proposition.subst`, `Metalogic.HasDeductionTheorem` are all already
  imported and used in the same file — reuse directly.
- No new abstraction is warranted. The deliverable is a sibling inductive in an existing tower.

## Key Verified Facts

### 1. `ConjImpBotAxiom` definition (template), `FragmentAxioms.lean:259-277`

The exact 6-constructor inductive. The new type drops only the final constructor:

```lean
  /-- Ex falso quodlibet (explosion): `⊥ → φ` -/
  | efq (φ : PL.Proposition Atom) :
      ConjImpBotAxiom (Proposition.bot.imp φ)
```

### 2. `MinPropAxiom` constructor names (Axioms.lean:126-150)

Constructors of `MinPropAxiom`: `implyK`, `implyS`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`.
The first five are exactly the five non-exfalso `ConjImpBotAxiom` constructors with **identical
names and identical shapes**. Crucially, `MinPropAxiom` has **no `efq`** — this is precisely why
the new subsumption targets `MinPropAxiom` (not `IntPropAxiom`), and why it type-checks without an
ex-falso case.

### 3. Existing `ConjImpAxiom.toMinPropAxiom` template (FragmentAxioms.lean:102-109)

```lean
theorem ConjImpAxiom.toMinPropAxiom {φ : PL.Proposition Atom}
    (h : ConjImpAxiom φ) : MinPropAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b
```

`ConjImpBotMinAxiom.toMinPropAxiom` is **byte-for-byte the same proof body** (same five cases,
since `ConjImpBotMinAxiom` has exactly those five constructors). The `.implyK`/`.andI`/... dot
notation resolves against `MinPropAxiom` from the expected type.

### 4. Constructor → `MinPropAxiom` mapping (confirmed)

| `ConjImpBotMinAxiom` ctor | maps to `MinPropAxiom` ctor | shape |
|---|---|---|
| `implyK a b` | `.implyK a b` | `φ → (ψ → φ)` |
| `implyS a b c` | `.implyS a b c` | `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` |
| `andI a b` | `.andI a b` | `φ → (ψ → φ ∧ ψ)` |
| `andE1 a b` | `.andE1 a b` | `(φ ∧ ψ) → φ` |
| `andE2 a b` | `.andE2 a b` | `(φ ∧ ψ) → ψ` |

### 5. Deduction theorem invocation (FragmentAxioms.lean:392-394)

```lean
theorem conjImpBotAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpBotAxiom Atom)) :=
  hasDeductionTheorem ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
```

`hasDeductionTheorem` takes exactly the two witnesses `mem_implyK` and `mem_implyS` (defined in the
`ConjImpBotAxiom` namespace at lines 308-317). Both witnesses survive the drop of `efq` unchanged —
they only reference `implyK`/`implyS`.

### 6. Fragment-predicate compatibility (FragmentAxioms.lean:339-387)

Five `isOrFree` lemmas exist for the non-efq constructors plus one `conjImpBotAxiom_efq_isOrFree`.
The new type reuses the five non-efq lemma bodies verbatim (renamed to
`conjImpBotMinAxiom_*_isOrFree`) and **omits the efq lemma**. They depend only on `imp_isOrFree`
and `and_isOrFree`, both already in scope.

### 7. File / imports / barrel

- New code goes **in `FragmentAxioms.lean`** itself, appended after the `ConjImpBotAxiom`
  Deduction-Theorem block (after line 394, inside `namespace Cslib.Logic.PL`, before line 396).
- The file already imports everything needed (`Axioms`, `Derivation`, `DeductionTheorem`,
  `FragmentPredicates`) — verified at lines 9-12. **No new imports.**
- `FragmentAxioms.lean` is **already** in the barrel `Cslib.lean` (line 432). Because no new file is
  created, **`lake exe mk_all` is NOT required** (it is only needed when adding files).
- The file uses `@[expose] public section` (line 40) and the `module` system; the new declarations
  inherit this — no extra annotations needed.

## Implementation-Ready Code (drop-in, after FragmentAxioms.lean:394)

```lean
/-! ## ConjImpBotMin Axiom System -/

/-- Axiom schemata for the MPL conjunctive-implicational-bot fragment MPL⟨∧,→,⊥,⊤⟩.

Identical to `ConjImpBotAxiom` except that it omits ex falso quodlibet (`⊥ → φ`). This is the
point at which the minimal-logic (MPL) tower diverges from the intuitionistic tower: `⊥` is a
free constant rather than the least element with explosion.

The 5 axiom constructors are:
- **implyK** (weakening): `φ → (ψ → φ)`
- **implyS** (distribution): `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- **andI** (conjunction introduction): `φ → (ψ → φ ∧ ψ)`
- **andE1** (left conjunction elimination): `φ ∧ ψ → φ`
- **andE2** (right conjunction elimination): `φ ∧ ψ → ψ`

Together with modus ponens, these axioms characterize the conjunctive-implicational-bot fragment
of minimal propositional logic (no ex falso). -/
inductive ConjImpBotMinAxiom : PL.Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)` -/
  | implyK (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | implyS (φ ψ χ : PL.Proposition Atom) :
      ConjImpBotMinAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)` -/
  | andI (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom (φ.imp (ψ.imp (φ.and ψ)))
  /-- Left conjunction elimination: `φ ∧ ψ → φ` -/
  | andE1 (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom ((φ.and ψ).imp φ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ` -/
  | andE2 (φ ψ : PL.Proposition Atom) :
      ConjImpBotMinAxiom ((φ.and ψ).imp ψ)

/-! ## ConjImpBotMin Axiom Subsumption -/

/-- Every conjunctive-implicational axiom is a conjunctive-implicational-bot-min axiom. -/
theorem ConjImpAxiom.toConjImpBotMinAxiom {φ : PL.Proposition Atom}
    (h : ConjImpAxiom φ) : ConjImpBotMinAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b

/-- Every conjunctive-implicational-bot-min axiom is a minimal propositional axiom.

Note: the target is `MinPropAxiom` (which has no ex falso), **not** `IntPropAxiom`. Staying inside
minimal logic is the defining feature of this fragment. -/
theorem ConjImpBotMinAxiom.toMinPropAxiom {φ : PL.Proposition Atom}
    (h : ConjImpBotMinAxiom φ) : MinPropAxiom φ := by
  cases h with
  | implyK a b => exact .implyK a b
  | implyS a b c => exact .implyS a b c
  | andI a b => exact .andI a b
  | andE1 a b => exact .andE1 a b
  | andE2 a b => exact .andE2 a b

/-! ## ConjImpBotMin Implication Axiom Witnesses -/

namespace ConjImpBotMinAxiom

/-- `ConjImpBotMinAxiom` includes implyK: witness for deduction theorem arguments. -/
theorem mem_implyK :
    ∀ (φ ψ : PL.Proposition Atom),
    ConjImpBotMinAxiom (φ.imp (ψ.imp φ)) :=
  fun φ ψ => .implyK φ ψ

/-- `ConjImpBotMinAxiom` includes implyS: witness for deduction theorem arguments. -/
theorem mem_implyS :
    ∀ (φ ψ χ : PL.Proposition Atom),
    ConjImpBotMinAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  fun φ ψ χ => .implyS φ ψ χ

end ConjImpBotMinAxiom

/-! ## ConjImpBotMin Substitution Closure -/

/-- Conjunctive-implicational-bot-min axiom schemata are preserved under substitution. -/
theorem subst_preserves_conjImpBotMinAxiom
    {Atom : Type u} {Atom' : Type u}
    {φ : PL.Proposition Atom}
    (h : ConjImpBotMinAxiom φ) (f : Atom → PL.Proposition Atom') :
    ConjImpBotMinAxiom (φ.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | andI a b => exact .andI (a.subst f) (b.subst f)
  | andE1 a b => exact .andE1 (a.subst f) (b.subst f)
  | andE2 a b => exact .andE2 (a.subst f) (b.subst f)

/-! ## ConjImpBotMin Fragment Predicate Compatibility -/

/-- Applying the `implyK` constructor to or-free propositions yields an or-free formula.

This is `φ → (ψ → φ)`, which is or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_implyK_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    (φ.imp (ψ.imp φ)).IsOrFree = true :=
  imp_isOrFree hφ (imp_isOrFree hψ hφ)

/-- Applying the `implyS` constructor to or-free propositions yields an or-free formula.

This is `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`, or-free when `φ`, `ψ`, `χ` are. -/
lemma conjImpBotMinAxiom_implyS_isOrFree {φ ψ χ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) (hχ : χ.IsOrFree = true) :
    ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))).IsOrFree = true :=
  imp_isOrFree
    (imp_isOrFree hφ (imp_isOrFree hψ hχ))
    (imp_isOrFree (imp_isOrFree hφ hψ) (imp_isOrFree hφ hχ))

/-- Applying the `andI` constructor to or-free propositions yields an or-free formula.

This is `φ → (ψ → φ ∧ ψ)`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_andI_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    (φ.imp (ψ.imp (φ.and ψ))).IsOrFree = true :=
  imp_isOrFree hφ (imp_isOrFree hψ (and_isOrFree hφ hψ))

/-- Applying the `andE1` constructor to or-free propositions yields an or-free formula.

This is `φ ∧ ψ → φ`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_andE1_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    ((φ.and ψ).imp φ).IsOrFree = true :=
  imp_isOrFree (and_isOrFree hφ hψ) hφ

/-- Applying the `andE2` constructor to or-free propositions yields an or-free formula.

This is `φ ∧ ψ → ψ`, or-free when `φ` and `ψ` are. -/
lemma conjImpBotMinAxiom_andE2_isOrFree {φ ψ : PL.Proposition Atom}
    (hφ : φ.IsOrFree = true) (hψ : ψ.IsOrFree = true) :
    ((φ.and ψ).imp ψ).IsOrFree = true :=
  imp_isOrFree (and_isOrFree hφ hψ) hψ

/-! ## ConjImpBotMin Deduction Theorem Instance -/

/-- The deduction theorem holds for `ConjImpBotMinAxiom`. -/
theorem conjImpBotMinAxiom_hasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpBotMinAxiom Atom)) :=
  hasDeductionTheorem ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
```

## Notes / Watch-outs for the Implementer

1. **Module docstring (lines 14-31)**: optional but recommended — it currently lists only
   `ConjImpAxiom`/`ImpAxiom`. Consider adding a bullet for `ConjImpBotMinAxiom` to keep the
   header accurate. Not strictly required to build.
2. **`u` universe variable**: `subst_preserves_conjImpBotMinAxiom` reuses the `{Atom : Type u}`
   pattern from `subst_preserves_conjImpBotAxiom` (note it locally re-binds `Atom`, shadowing the
   section `variable {Atom : Type*}`). Copy the signature exactly as given.
3. **Lint compliance** (env linters are weekly-cron, but keep clean): every declaration above has a
   docstring (docBlame); Prop-valued items use `theorem`/`lemma` not `def` (defLemma); names are
   lowerCamelCase with no underscores in the identifier portion (the trailing `_isOrFree` etc.
   match the existing accepted convention in this file); instances are not introduced. The
   `ConjImpBotMinAxiom` namespace block wraps the two `mem_*` witnesses exactly like the existing
   `ConjImpBotAxiom` block (topNamespace).
4. **No `mk_all` needed** — file already barreled. Do **not** create a new file.
5. **`ConjImpBotAxiom` untouched** — all additions are strictly appended; do not edit lines 259-394.

## CI Verification Checklist (run in order)

```bash
cd /home/benjamin/Projects/cslib
lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms   # scoped, phase-end
lake build                                                         # full, final
lake exe checkInitImports        # file already imports Cslib.Init (no new file)
lake exe lint-style
lake shake --add-public --keep-implied --keep-prefix
lake test                        # CslibTests suite
```

`lake exe mk_all --module` is **not** required (no new file). `lake lint` (env linters) optional
locally; the code is written to satisfy docBlame/defLemma/topNamespace.

## Zero-Debt / Sorry Risk

Zero. Every proof body is a verified copy of a body that already compiles in this file, with the
sole change being the removal of the `efq`/`| efq ...` case. No `sorry`, no axioms, no vacuous
definitions.
