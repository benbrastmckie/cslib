# Cherry-Pick Recipe: PR #648 Foundation Refresh

**Task**: 399 — refresh_pr648_ipl_base_foundation
**Date**: 2026-06-29
**Branch target**: `feat/propositional-foundation` (new branch off `upstream/main`)

---

## Overview

This recipe produces a single focused commit on a fresh branch from `upstream/main` containing
ONLY the propositional foundation layer: the five-primitive `Proposition` type, gated `efq`
in `NaturalDeduction/Basic.lean`, and the six required `references.bib` entries. Per Waring
flag (a), connective typeclasses are excluded; per Waring flag (b), references and the
Zulip-thread link are present.

---

## Confirmed Context (Phase 1 Verification)

### Upstream/main HEAD

- Commit: `2772f421` (chore: fix header of DA/Prod.lean, #682)
- Propositional files in upstream barrel: **3 only**
  - `Cslib/Logics/Propositional/Defs.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
  - `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean`
- None of the 11 commits since merge base (`70c5bf58`) touch propositional files.

### Critical: Theory.lean Deletion (Option A)

`Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` in upstream/main:
- Uses the OLD `IsIntuitionistic Atom (S : InferenceSystem)` API with `[Bot Atom]` constraint
- Uses `implI`/`implE`/`implE` (old naming, to be renamed `impI`/`impE` in the new Defs.lean)
- Imported by `Cslib.lean` barrel at line 158: `public import Cslib.Logics.Propositional.NaturalDeduction.Theory`
- No other upstream file imports from `Cslib.Logics.Propositional.NaturalDeduction.Theory`
- The instances it provides (`instIsIntuitionisticIPL`, `instIsClassicalCPL`) are now in
  the new `Defs.lean`; derived rules (`efqCtx`, `efqRule`, `contra`, `byContra`, `lem`,
  `pierce`) go to a follow-up `DerivedRules` PR.

**Decision: DELETE Theory.lean (Option A).** This is a reviewer-visible decision and must be
flagged explicitly in the PR description.

### Impl → Imp Rename Impact

- Upstream `Basic.lean` uses `implI`/`implE` (old naming).
- No other upstream file outside Theory.lean uses `implI`/`implE` directly.
- Theory.lean uses `implI`/`implE` but is being deleted.
- The rename is backward-breaking only for downstream user code; upstream has zero other
  consumers.

### Connectives.lean Exclusion (Waring flag a)

- `Cslib/Foundations/Logic/Connectives.lean` exists in the local fork main but is NOT in
  upstream/main's propositional directory.
- Local fork main's `Defs.lean` imports it at line 10 and registers three typeclass instances
  (`PropositionalConnectives` at lines 113–114, `HasAnd` at lines 118–120, `HasOr` at 122–124).
- These are excluded from the cherry-pick per Waring flag (a).

### References

Upstream/main `references.bib` is MISSING these entries (present in local fork main):
1. `Johansson1937` — Der Minimalkalkül (cited in Defs.lean and Basic.lean)
2. `Gentzen1935` — Untersuchungen über das logische Schließen (cited in both)
3. `Prawitz1965` — Natural Deduction: A Proof-Theoretical Study (cited in both)
4. `TroelstraVanDalen1988` — Constructivism in Mathematics (cited in both)
5. `SorensenUrzyczyn2006` — Lectures on the Curry-Howard Isomorphism (cited in Basic.lean)
6. `Church1956` — Introduction to Mathematical Logic (cited in Defs.lean)
7. `ChagrovZakharyaschev1997` — Modal Logic (cited in Defs.lean)

Note: `Avigad2022` is present in local fork main's `references.bib` but is NOT cited in any
of the foundation cherry-pick files (`Defs.lean`, `Basic.lean`). It is omitted from the
cherry-pick.

---

## Exact File Changes

### File 1: `Cslib/Logics/Propositional/Defs.lean` (MODIFY)

Take the local fork main version **with two exclusions**:

**Exclusion 1 — Remove Connectives import (line 10):**
```
REMOVE:  public import Cslib.Foundations.Logic.Connectives
```
The remaining imports are:
```
import Cslib.Init
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.TypeTags
public import Aesop.BuiltinRules
```

**Exclusion 2 — Remove three typeclass instances (lines 113–124):**
```lean
REMOVE (entire block):
/-- Register `Proposition` as an instance of `PropositionalConnectives`. -/
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp

/-- Register `HasAnd` instance for `Proposition`. -/
instance : HasAnd (Proposition Atom) where
  and := .and

/-- Register `HasOr` instance for `Proposition`. -/
instance : HasOr (Proposition Atom) where
  or := .or
```

The resulting file retains:
- 5-primitive `Proposition` type (`atom`, `bot`, `imp`, `and`, `or`)
- `neg`, `top`, `iff` derived connectives
- `Bot` and `Top` instances
- All scoped notation (`⊥`, `⊤`, `∧`, `∨`, `→`, `↔`, `¬`)
- `Proposition.subst`, `Monad Proposition`
- `Theory`, `MPL`, `IPL`, `CPL` abbreviations
- `IsIntuitionistic`, `IsClassical` (new API on `Theory Atom`)
- `instIsIntuitionisticIPL`, `instIsClassicalCPL` (moved from Theory.lean)
- `instIsIntuitionisticExtention`, `instIsClassicalExtention`
- `intuitionisticCompletion`, `instIsIntuitionisticIntuitionisticCompletion`
- All six references entries (Johansson1937, Gentzen1935, Prawitz1965,
  TroelstraVanDalen1988, Church1956, ChagrovZakharyaschev1997)

### File 2: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (REPLACE)

Take the local fork main version **as-is**. This file:
- Does NOT import `Connectives.lean` (imports only `Defs` and `InferenceSystem`)
- Contains 11 constructors including gated `efq [IsIntuitionistic T]`
- Uses `imp`/`impI`/`impE` naming (new)
- Has `## Implementation notes` (IPL-as-base design note, MPL-as-fragment)
- Has Zulip-thread link at line 78 (Waring flag b)
- Has restored references section (Johansson1937, Prawitz1965, TroelstraVanDalen1988,
  Gentzen1935, SorensenUrzyczyn2006) — Waring flag (b)

### File 3: `Cslib.lean` (MODIFY)

Remove one line:
```
REMOVE:  public import Cslib.Logics.Propositional.NaturalDeduction.Theory
```
This line is at line 158 in upstream/main's barrel.

### File 4: `references.bib` (ADD ENTRIES)

Add the following 7 entries (from local fork main, not present in upstream):
- `Church1956`
- `ChagrovZakharyaschev1997`
- `Johansson1937`
- `Gentzen1935`
- `Prawitz1965`
- `TroelstraVanDalen1988`
- `SorensenUrzyczyn2006`

### File 5: `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` (DELETE)

Delete this file entirely. It uses the old `IsIntuitionistic Atom (S : InferenceSystem)`
API and `[Bot Atom]` constraint, which are incompatible with the new Defs.lean.

---

## Summary Diff

```
Files modified:  Defs.lean, Basic.lean (replace), Cslib.lean (1 line removed), references.bib (7 entries added)
Files deleted:   NaturalDeduction/Theory.lean
Files NOT touched: Connectives.lean (excluded; does not exist in upstream/main)
```

---

## Option A Rationale (Theory.lean Deletion)

Theory.lean in upstream uses `IsIntuitionistic Atom (S : InferenceSystem) [Bot Atom]` — the
old API that treats `⊥` as an atom constraint rather than a primitive constructor. The new
`Defs.lean` introduces a wholly different API: `IsIntuitionistic (T : Theory Atom)` (no
`[Bot Atom]` constraint, no `InferenceSystem` parameter). These two APIs are fundamentally
incompatible; Theory.lean cannot be updated without essentially rewriting it.

The instances previously in Theory.lean (`instIsIntuitionisticIPL`, `instIsClassicalCPL`,
`instIsIntuitionisticIntuitionisticCompletion`) are now in `Defs.lean`. The derived rules
(`efqCtx`, `efqRule`, `contra`, `byContra`, `lem`, `pierce`, `LEM`, `Pierce`,
`instIsClassicalLEM`, `instIsClassicalPierce`) are available in the local fork main at
`NaturalDeduction/DerivedRules.lean` and will be submitted in a follow-up PR.

This keeps the foundation PR tightly scoped: one file is a complete replacement
(`Defs.lean`), one is a full replacement of `Basic.lean`, one deletion + barrel update, and
seven `references.bib` entries.

---

## Local Verification Results

Phase 2 rehearsal completed 2026-06-29. All checks GREEN.

### Worktree details

- Created: `git worktree add -b verify/propositional-foundation ../cslib-foundation-verify upstream/main`
- Upstream/main HEAD: `2772f421` (chore: fix header of DA/Prod.lean, #682)
- Toolchain: `leanprover/lean4:v4.32.0-rc1` (upstream toolchain)
- Mathlib: `29af5245bafea7d69fdca69591450f60b916ed71`
- Cache: `lake exe cache get` downloaded 8573 Mathlib olean files
- Removed: worktree and `verify/propositional-foundation` branch deleted after verification

### Build status

- [x] `lake build Cslib.Logics.Propositional.Defs` — **GREEN** (497 jobs)
- [x] `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` — **GREEN** (592 jobs)
- [x] `lake build Cslib` (barrel) — **GREEN** (2741 jobs)
- [x] `lake exe checkInitImports` — **GREEN** (exit code 0)
- [x] `lake exe lint-style Defs.lean Basic.lean` — **GREEN** (exit code 0)

### Barrel consistency confirmed

- No reference to deleted `Theory.lean` remains in `Cslib.lean` or any propositional file
- No reference to excluded `PropositionalConnectives`, `HasAnd`, `HasOr` instances remains
- Fork main unchanged after worktree cleanup (`git status` clean except pre-existing diffs)

---

## Reviewer-Visible Decision Points

1. **Theory.lean deletion (Option A)**: The file uses an API incompatible with the new
   `Defs.lean`. It is deleted; its core instances are absorbed into `Defs.lean`; its derived
   rules (`byContra`, `contra`, `lem`, `pierce`) follow in a subsequent small PR.

2. **Connective typeclasses excluded (Waring flag a)**: `PropositionalConnectives`, `HasAnd`,
   `HasOr` instances are removed from `Defs.lean`; see PR #607 for the existing connective
   typeclass work and task 400 for the CSLib-side coordination.

3. **Namespace `PL` → `Propositional` (task 387, upstream-gated)**: The PR exposes
   `namespace Cslib.Logic.PL`. Rename to `Cslib.Logics.Propositional` requires upstream
   maintainer consensus and is tracked in task 387. No action in this PR.

4. **`impl` → `imp` rename**: The old `implI`/`implE` naming is replaced by `impI`/`impE`
   throughout `Basic.lean`. Theory.lean (the only upstream consumer of the old naming) is
   being deleted. No other upstream consumers.
