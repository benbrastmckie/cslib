# Implementation Plan: Task #245

- **Task**: 245 - Encodable/Countable/Denumerable instances for the LTL Formula type
- **Status**: [NOT STARTED]
- **Effort**: 1.0 hours
- **Dependencies**: None
- **Research Inputs**: specs/245_formula_encodable_countable_instances/reports/01_encodable-countable-denumerable-instances.md
- **Artifacts**: plans/01_encodable-countable-denumerable-instances.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add `Encodable`, `Countable`, and `Denumerable` instances to the LTL `Formula` type at
`Cslib/Logics/LTL/Syntax/Formula.lean`. All three are zero-debt achievable using existing
Mathlib API: `Encodable` derives via Mathlib's `deriving Encodable` handler, `Countable`
follows from `Encodable.countable`, and `Denumerable` follows from
`Denumerable.ofEncodableOfInfinite` once an unconditional `Infinite (Formula Atom)` instance
is supplied (a `private iterNext` helper iterating `next` on `bot` injects `ℕ`). The only
nontrivial proof obligation is the injectivity of `iterNext`. The full instance block was
compiled end-to-end during research with `success: true`; no `noncomputable`, no sorries, no
new axioms. The net caller constraint is `[Encodable Atom]`.

### Research Integration

The research report (`reports/01_…`) verified every code sketch via `lean_run_code`:
- The `deriving Encodable` handler succeeds on the recursive (reflexive) `Formula` despite its
  docstring claiming non-reflexive only — this is the single de-risked unknown.
- `Encodable.countable` (from `Mathlib.Logic.Encodable.Basic`) closes `Countable` term-mode.
- `Denumerable.ofEncodableOfInfinite` (from `Mathlib.Logic.Denumerable`) closes `Denumerable`.
- `Infinite (Formula Atom)` holds for every `Atom` (including `Empty`) via `Infinite.of_injective iterNext`.
- Two `public import` lines are required: `Mathlib.Tactic.DeriveEncodable` and `Mathlib.Logic.Denumerable`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap_flag not set). The research notes a
downstream benefit: the Temporal/Bimodal completeness machinery
(`Temporal/Metalogic/Completeness.lean:101`, `Bimodal/Metalogic/BXCanonical/CanonicalModel.lean:183`)
currently takes `[Denumerable (Formula Atom)]` as a hypothesis; providing this instance lets
that hypothesis be discharged by `inferInstance` given `[Encodable Atom]`. The analogous
Temporal `Formula` (with the extra `snce` constructor) is an explicit out-of-scope follow-up.

## Goals & Non-Goals

**Goals**:
- Provide `Encodable (Formula Atom)` under `[Encodable Atom]` via the Mathlib deriving handler.
- Provide `Countable (Formula Atom)` under `[Encodable Atom]` via `Encodable.countable`.
- Provide unconditional `Infinite (Formula Atom)` via a `private iterNext` helper.
- Provide `Denumerable (Formula Atom)` under `[Encodable Atom]` via `Denumerable.ofEncodableOfInfinite`.
- Pass the full CSLib CI pipeline (build, lint, lint-style, shake, checkInitImports).

**Non-Goals**:
- Adding the same instances to `Cslib/Logics/Temporal/Syntax/Formula.lean` (separate follow-up).
- Rewriting the Temporal/Bimodal completeness theorems to drop their `[Denumerable …]` hypotheses.
- Any `noncomputable` or `Classical`-dependent fallback (not needed).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `deriving Encodable` handler regresses on reflexive `Formula` after a Mathlib bump | H | L | Verified working during research on the exact type shape; fallback is hand-written `Encodable.ofLeftInjection` into a tree-of-ℕ encoding (documented in report, not currently needed) |
| `iterNext` injectivity proof breaks under a Lean/Mathlib version skew | M | L | Research-verified proof reproduced verbatim below; if `simp [iterNext]` fails, substitute `Formula.next.injEq` explicitly |
| Lint flags `private iterNext` for missing docstring (docBlame) | L | M | Helper carries a docstring in the sketch; keep it `private` to limit exposure |
| `lake shake` flags an over-broad import | L | M | Run `lake shake --add-public --keep-implied --keep-prefix` and remove any flagged line (`Denumerable` transitively provides `Encodable.countable`) |
| Adding `Encodable` to the `deriving` clause breaks existing `DecidableEq, BEq` derivation order | L | L | Append `Encodable` last in the clause; build immediately after to confirm |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel. Phase 2 (CI verification) depends on the
edits from Phase 1.

### Phase 1: Add instances and imports to Formula.lean [COMPLETED]

**Goal**: Add the two `public import` lines, extend the `deriving` clause with `Encodable`,
and add the `Countable`, `private iterNext`, `Infinite`, and `Denumerable` instances inside
`namespace Cslib.Logic.LTL`.

**Tasks**:
- [ ] Add `public import Mathlib.Tactic.DeriveEncodable` and `public import Mathlib.Logic.Denumerable` to the import block (after the existing `public import` lines, lines 9-11).
- [ ] Extend the `deriving` clause on the `Formula` inductive (line 95) from `deriving DecidableEq, BEq` to `deriving DecidableEq, BEq, Encodable`.
- [ ] Add the `Countable` instance after the `Bot`/`Top` instances (before `end Cslib.Logic.LTL`, line 158).
- [ ] Add the `private iterNext` helper (with docstring) and the `Infinite` instance.
- [ ] Add the `Denumerable` instance.
- [ ] Build the module scoped: `lake build Cslib.Logics.LTL.Syntax.Formula`.

**Code sketch** (verified end-to-end during research):

```lean
-- Import block additions (after line 11):
public import Mathlib.Tactic.DeriveEncodable
public import Mathlib.Logic.Denumerable

-- Deriving clause (line 95) becomes:
deriving DecidableEq, BEq, Encodable

-- New instances inside `namespace Cslib.Logic.LTL`, after the `Bot`/`Top` instances:

/-- LTL formulas are countable whenever the atoms are encodable. -/
instance {Atom : Type u} [Encodable Atom] : Countable (Formula Atom) :=
  Encodable.countable

/-- Iterate `next` on `bot` `n` times, witnessing an injection `ℕ ↪ Formula Atom`. -/
private def iterNext {Atom : Type u} : Nat → Formula Atom
  | 0 => Formula.bot
  | n + 1 => Formula.next (iterNext n)

/-- `Formula Atom` is infinite for every `Atom` (no constraint on `Atom`). -/
instance {Atom : Type u} : Infinite (Formula Atom) :=
  Infinite.of_injective iterNext (by
    intro a b h
    induction a generalizing b with
    | zero => cases b with
      | zero => rfl
      | succ b => simp [iterNext] at h
    | succ a ih => cases b with
      | zero => simp [iterNext] at h
      | succ b => exact congrArg Nat.succ (ih (by simpa [iterNext] using h)))

/-- LTL formulas are denumerable whenever the atoms are encodable.
    `noncomputable` is NOT required. -/
instance {Atom : Type u} [Encodable Atom] : Denumerable (Formula Atom) :=
  Denumerable.ofEncodableOfInfinite (Formula Atom)
```

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - add two imports, extend deriving clause, add four instance/helper declarations.

**Proof obligations**:
- `iterNext` injectivity (the only nontrivial proof; complete and verified above).
- `Encodable (Formula Atom)` produced by the deriving handler and accepted by `inferInstance`.
- `Denumerable.ofEncodableOfInfinite (Formula Atom)` type-checks given the `Encodable` + `Infinite` instances.

**Verification**:
- `lake build Cslib.Logics.LTL.Syntax.Formula` succeeds with no errors/warnings.
- `#synth Encodable (Formula ℕ)`, `#synth Countable (Formula ℕ)`, `#synth Denumerable (Formula ℕ)` all resolve (optional inline check via `lean_multi_attempt`).
- No `sorry`, no new axioms (`lean_verify` on the instances if needed).

---

### Phase 2: Run the CSLib CI pipeline [COMPLETED]

**Goal**: Confirm the change passes the full CSLib CI verification order and minimize imports.

**Tasks**:
- [ ] `lake build` (full project) — confirm syntax linters pass.
- [ ] `lake exe checkInitImports` — confirm `Cslib.Init` import requirement still satisfied.
- [ ] `lake lint` — confirm environment linters (docBlame on `iterNext`, etc.) pass.
- [ ] `lake exe lint-style` — confirm text/style linters pass (`--fix` if needed).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — minimize imports; remove any flagged redundant line.
- [ ] `lake test` — run `CslibTests/` to confirm no regression.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - only if `lake shake` or `lint-style` flags adjustments.

**Verification**:
- All CI commands exit 0.
- `lake shake` reports no removable imports (or the flagged line is removed and build still passes).
- `lake lint` reports zero new warnings on the edited file.

---

## Testing & Validation

- [ ] `lake build` passes with zero errors and zero new warnings.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` passes (no docBlame/defLemma/topNamespace warnings on new declarations).
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports clean (or is applied).
- [ ] `lake test` passes.
- [ ] `Encodable`, `Countable`, and `Denumerable` for `Formula ℕ` all resolve by `inferInstance`.
- [ ] No `sorry`, no new axioms introduced.

## Artifacts & Outputs

- Modified `Cslib/Logics/LTL/Syntax/Formula.lean` with three new instances, one `private` helper, and two imports.
- Green CI pipeline output (build, lint, lint-style, shake, checkInitImports, test).

## Rollback/Contingency

- The change is localized to a single file; revert via `git checkout Cslib/Logics/LTL/Syntax/Formula.lean`.
- If the `deriving Encodable` handler fails (Mathlib regression), fall back to a standalone
  `instance ... : Encodable (Formula Atom) := by deriving_instance`, or, failing that, a
  hand-written `Encodable.ofLeftInjection` into a tree-of-ℕ encoding (documented in the
  research report). The `Countable`/`Infinite`/`Denumerable` instances are unaffected by which
  `Encodable` route is taken.
- If `iterNext` injectivity tactic fails under version skew, replace `simp [iterNext]` with
  explicit `Formula.next.injEq` rewriting; the structural induction shape stays the same.
