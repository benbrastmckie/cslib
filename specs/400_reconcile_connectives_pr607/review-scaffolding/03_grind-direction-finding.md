# PR #607 Engagement — `_def` Normal-Form Direction: Empirical Finding

> **FACTUAL SCAFFOLDING — Points for a human-authored review. Rewrite every sentence in your
> own words before posting (CSLib Zulip AI policy #605827029). No paragraph here is
> ready-to-post prose.**
>
> All claims below were verified by compiling scratch test files against CSLib's codebase
> (2026-06-29). Positive results mean `lake build` succeeded; negative results mean specific
> error messages were produced.

---

## 0. Context: chenson's CHANGES_REQUESTED

`chenson2018`'s open CHANGES_REQUESTED on PR #607 argues that the `_def` simp/grind lemmas
should be oriented **into** the notation (the notation = the normal form), matching
`List.append_eq` and `Nat.add_eq`. Current `_def` orientation in #607: `φ.op ψ = φ op ψ`
(method call → notation), which IS the "into notation" direction.

Waring agreed in principle but reported he couldn't make `grind` see through the notation
in the **modal satisfies** proof context without rewriting back — hence the modal proofs
became more verbose (`grind [=_ Proposition.or_def, Proposition.or]`).

**This finding resolves whether Waring's blocker is fixable and what advice to give.**

---

## 1. Empirical Setup

Two different formula-type architectures are in play and give DIFFERENT results:

### Architecture A — Derived connectives as `abbrev` (fork's `Modal.Proposition`)

The fork's `Modal.Proposition` has only 4 primitive constructors:
`atom`, `bot`, `imp`, `box`. Conjunction, disjunction, negation, and diamond are all
`abbrev`s built from these:

```lean
abbrev Proposition.and (φ₁ φ₂ : Proposition Atom) : Proposition Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot    -- ¬(φ₁ → ¬φ₂)

abbrev Proposition.or (φ₁ φ₂ : Proposition Atom) : Proposition Atom :=
  .imp (.imp φ₁ .bot) φ₂                -- ¬φ₁ → φ₂

abbrev Proposition.neg (φ : Proposition Atom) : Proposition Atom :=
  .imp φ .bot                            -- φ → ⊥

abbrev Proposition.diamond (φ : Proposition Atom) : Proposition Atom :=
  .neg (.box (.neg φ))                   -- ¬□¬φ
```

The `Satisfies` relation is defined on the 4 primitive constructors (not on `and`/`or`/etc.)
and is tagged `@[scoped grind]`.

### Architecture B — Primitive constructors + typeclass wrapper (simulating upstream / #607)

The upstream `Proposition` (and the minimal simulation) has `and`/`or` as **primitive
constructors** of the inductive type. `HasAnd.and` is a typeclass method whose implementation
is `Formula.and`. `φ ∧ ψ` uses the typeclass notation `HasAnd.and φ ψ`.

---

## 2. Empirical Results

### POSITIVE — Architecture A (fork's modal, abbrev-based)

**Finding**: `grind` SUCCEEDS without ANY `_def` bridge lemma.

All of the following compile without errors:

```lean
-- Test A: grind with explicit hint (expected to work)
example : Satisfies m w (φ₁ ∧ φ₂) ↔ Satisfies m w φ₁ ∧ Satisfies m w φ₂ := by
  grind [Satisfies.and_iff]   -- ✓ builds

-- Test C: grind ALONE, no hints at all
example : Satisfies m w (φ₁ ∧ φ₂) ↔ Satisfies m w φ₁ ∧ Satisfies m w φ₂ := by
  grind                       -- ✓ builds (no hints required!)

-- Dual: grind alone closes ◇φ ↔ ¬□¬φ in Satisfies form
example : Satisfies m w (Proposition.diamond φ ↔
    Proposition.neg (Proposition.box (Proposition.neg φ))) := by
  grind                       -- ✓ builds

-- simp + grind pipeline for the dual via derivation notation
example : ⇓Modal[m,w ⊨ ◇φ ↔ ¬□¬φ] := by
  simp only [derivation_def, Satisfies.and_iff_and, neg_satisfies,
             Satisfies.impl_iff_impl, Satisfies.box_iff_forall,
             Satisfies.diamond_iff_exists]
  grind                       -- ✓ builds
```

**Why it works**: `abbrev` in Lean 4 is definitionally transparent to the kernel and to
`grind`. When grind sees `Satisfies m w (φ₁ ∧ φ₂)` (where `∧` = `Proposition.and` = an
`abbrev` for `.imp (.imp φ₁ (.imp φ₂ .bot)) .bot`), it unfolds the `abbrev` and applies the
`@[scoped grind]` equations of `Satisfies` for the `imp` constructor. Classical propositional
reasoning then closes the goal. No `_def` bridge lemma needed.

**Implication for the chenson orientation question**: The `_def` orientation is **moot** for
the fork's modal development. The `_def` debate in #607 concerns the UPSTREAM propositional
(Architecture B), not the fork's modal.

### NEGATIVE — Architecture B (primitive constructor + typeclass wrapper)

**Finding**: `grind` FAILS and `simp` ALSO FAILS without an explicit bridge.

Simulation with a minimal inductive type:

```lean
-- Minimal inductive mimicking upstream's Propositional (primitive and constructor)
inductive Formula : Type where
  | bot : Formula
  | imp (a b : Formula) : Formula
  | and (a b : Formula) : Formula    -- ← PRIMITIVE constructor

@[simp] def FormSat : Formula → Prop
  | .bot => False
  | .imp a b => FormSat a → FormSat b
  | .and a b => FormSat a ∧ FormSat b

class HasAnd607 (α : Type*) where and : α → α → α

instance : HasAnd607 Formula where and := .and
```

```lean
-- FAILS: simp alone (simp doesn't unfold typeclass instance automatically)
example (A B : Formula) : FormSat (HasAnd607.and A B) ↔ FormSat A ∧ FormSat B := by
  simp    -- ✗ "simp made no progress"

-- FAILS: grind with explicit HasAnd607.and hint
-- (grind knows HasAnd607.and.eq_1 but can't connect to FormSat equations)
example (A B : Formula) : FormSat (HasAnd607.and A B) ↔ FormSat A ∧ FormSat B := by
  grind [HasAnd607.and]    -- ✗ "grind failed"

-- SUCCEEDS: simp [HasAnd607.and] (explicitly unfolds the instance)
example (A B : Formula) : FormSat (HasAnd607.and A B) ↔ FormSat A ∧ FormSat B := by
  simp [HasAnd607.and]    -- ✓ builds
```

**Grind diagnostic output** (from the failing `grind [HasAnd607.and]` run):
```
[grind] Goal diagnostics
  [ematch] E-matching patterns
    [thm] HasAnd607.and.eq_1: [@HasAnd607.and #1 #0]
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] HasAnd607.and.eq_1 ↦ 1
```

Grind found the instance equation `HasAnd607.and.eq_1` (connecting `HasAnd607.and` to
`Formula.and`) but couldn't connect that to `FormSat.and` to reduce the goal. The `@[simp]`
annotation on `FormSat` tells simp about it, but grind's E-matching failed to chain the
two rewrites together.

**Root cause**: grind cannot automatically chain
`FormSat (HasAnd607.and A B)` → (via `HasAnd607.and.eq_1`) → `FormSat (Formula.and A B)` →
(via `@[simp]` `FormSat.and` equation) → `FormSat A ∧ FormSat B`
because `FormSat` is `@[simp]` (not `@[grind]`), and the intermediate step requires
recognizing that the typeclass method `HasAnd607.and` equals the constructor `Formula.and`.

---

## 3. The `_def` Direction Diagnosis (Architecture B / upstream #607)

For #607's upstream propositional (Architecture B):

| `_def` orientation | Effect on grind in Satisfies proofs | Verdict |
|---|---|---|
| `φ.and ψ = φ ∧ ψ` (constructor → notation, chenson's direction) | Grind reaches `Satisfies m w (φ ∧ ψ)` (typeclass notation) and can't reduce it further — Satisfies knows constructors, not typeclass methods | **MAKES THINGS WORSE** for grind |
| `φ ∧ ψ = φ.and ψ` (notation → constructor) | Grind unfolds the typeclass notation to the constructor, then can apply Satisfies equations | **HELPS** grind |
| Both directions (or `@[simp]` on the instance + `@[grind]` on FormSat) | Grind has both paths; may work but is redundant | Acceptable workaround |
| `simp [HasAnd607.and]` (explicit instance in simp call) | Explicitly chains the rewrites; always works | **Waring's workaround** |

**Recommendation point for the review**:
- Waring's blocker is real and specifically applies to Architecture B (primitive constructors
  + typeclass wrappers).
- chenson's preferred orientation (constructor → notation, notation = normal form) **aggravates**
  the blocker rather than fixing it; it removes the path grind uses to reduce Satisfies goals.
- The orientation that HELPS grind is `notation → constructor` (`φ ∧ ψ = φ.and ψ`).
- BUT this conflicts with `List.append_eq`/`Nat.add_eq` precedent where the notation form IS
  the normal form.
- The only way to get BOTH (notation = normal form AND grind works for Satisfies) is to either:
  - Tag `Satisfies` equations with `@[grind]` in the typeclass-notation form as well, OR
  - Provide both directions as `@[grind =]` lemmas, OR
  - Tag the instance equations `HasAnd.and = Proposition.and` as `@[grind =]` so grind can chain

---

## 4. Leftover Debt: Commented-Out `grind only` Block in `Satisfies.dual`

The current fork's `Cslib/Logics/Modal/Basic.lean` has `Satisfies.dual` proved with:
```lean
theorem Satisfies.dual : ⇓Modal[m,w ⊨ ◇φ ↔ ¬□¬φ] := by
  change Satisfies m w (.iff (.diamond φ) (.neg (.box (.neg φ))))
  rw [and_iff]
  exact ⟨id, id⟩
```

The research report (02) notes "a commented-out `grind only` block remains — minor debt to
flag." The current code does NOT have such a block — it uses `change` + `rw`. Minor cleanup:
this is not a blocker for #607 but worth flagging to fmontesi as proof verbosity that could
be reduced if the `_def` direction is settled correctly.

**Empirical result**: For Architecture A (the fork's modal with `abbrev`s), `grind` alone CAN
prove the dual (verified above). The `change` + `rw` pattern is therefore conservative (safe
but more verbose than needed), not necessary.

---

## 5. Summary of Points for the Review (`_def` Direction Section)

These are *points to make*, not prose to paste:

- Waring's blocker is real but is specific to Architecture B (upstream propositional with
  primitive `and`/`or` constructors + typeclass wrappers).
- For the fork's modal (Architecture A, with `abbrev`-based `and`/`or`), `grind` works without
  any `_def` bridge lemma.
- chenson's preferred orientation (constructor → notation) makes the upstream case HARDER for
  grind, not easier.
- Recommendation: orient the bridge `notation → constructor` for the upstream propositional
  `_def` lemmas; then simp/grind can unfold notation to constructors before applying `Satisfies`.
- Alternatively: tag both the instance equations AND the Satisfies equations as `@[grind =]`
  so grind can chain the steps automatically.
- Offer to help test the settled orientation in #607's proof context before posting; the fork's
  modal gives a clean test bed (Architecture A).
- Minor cleanup: flag the remaining `change`-based `Satisfies.k`/`Satisfies.dual` proofs as
  candidates for simplification once the `_def` direction is agreed.
