# Research: Prune redundant imports from Intuitionistic CanonicalModel.lean

## Task

Verify that `public import Cslib.Logics.Modal.Metalogic.MCS` and
`public import Cslib.Logics.Modal.Semantics.Birelational` in
`Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean` are unused (redundant after a
recent consolidation added `GenericMCSBridge` / `DerivationCombinators` imports), and determine a
regression-free removal procedure.

## Executive Summary

The task's premise is **partially correct but incomplete**. Both imports are unused *within
CanonicalModel.lean's own code* (all `MCS`/`Birelational` identifiers in that file appear only in
docstring prose). However, both are declared `public import` (re-exported), and a **downstream
file consumes `Birelational` through that re-export**. Naively deleting both lines from
CanonicalModel.lean alone **will break the build** of `TruthLemma.lean` and `Completeness.lean`.

The correct, regression-free change set is:

1. `CanonicalModel.lean`: remove the `MCS` and `Birelational` `public import` lines.
2. `TruthLemma.lean`: **add** `public import Cslib.Logics.Modal.Semantics.Birelational` to
   compensate for the lost transitive re-export.

`MCS` can be removed with no compensating change anywhere (genuinely unused across the whole
downstream subtree). Do **not** use `lake shake --fix` (see "Why not --fix").

## Evidence

### 1. In-file usage (CanonicalModel.lean) — docstring-only, confirmed

`grep` for `MCS | Birelational | BFrame | BModel | BForces | IValid | MValid | mcs_ | Maximal`
returns only:
- Lines 11-12: the import statements themselves.
- Comment/docstring prose (lines 29-43, 79, 102, 137, 231, 638, 748, 926, 992-997, 1143, 1207) —
  all inside `/- ... -/` or `/-- ... -/` blocks, none are used Lean identifiers.
- Line 71 `open Cslib.Logic.Metalogic.GenericMCS` resolves to the `GenericMCS` namespace supplied
  by `GenericMCSBridge`, **not** `MCS.lean`.

So the task's claim "referenced only in docstring prose, not as used Lean identifiers" is accurate
for CanonicalModel.lean itself.

### 2. `lake shake --add-public --keep-implied --keep-prefix` (authoritative)

Run over the module set `{TruthLemma, CanonicalModel}` (full-project replay), shake reports:

```
CanonicalModel.lean:
  remove #[import Cslib.Init, public import Cslib.Logics.Modal.Metalogic.MCS,
           public import Cslib.Logics.Modal.Semantics.Birelational]
TruthLemma.lean:
  remove #[import Cslib.Init]
  add    #[public import Cslib.Logics.Modal.Semantics.Birelational]
```

Two critical readings of this output:

- **Birelational removal from CanonicalModel is paired with a Birelational ADD to TruthLemma.**
  This is the crux the task description missed. It is not a free deletion — it is a *relocation*
  of the direct import down to the file that actually uses the names.
- **`import Cslib.Init` is flagged for removal in BOTH files. This is a shake false positive and
  MUST be ignored.** `Cslib.Init` is imported for side effects (linter setup + common tactics),
  not for declarations, so shake cannot see the dependency. Removing it violates the
  `lake exe checkInitImports` invariant (every CSLib file must `import Cslib.Init`).

`MCS` gets no compensating "add" anywhere → genuinely dead.

### 3. Transitive dependency graph (manual confirmation of shake)

Import edges (all `public import` unless noted):

```
Completeness  ->  TruthLemma  ->  CanonicalModel  ->  { PrimeTheory, MCS, Birelational,
                                                        GenericMCSBridge, DerivationCombinators }
```

- Sole importer of `CanonicalModel`: `TruthLemma.lean`.
- Sole importer of `TruthLemma`: `Completeness.lean`.
- Sole importer of `Completeness` in this subtree: (none within `Cslib/`).

Reachability of `Birelational` from CanonicalModel is **only** via CanonicalModel's own direct
import — none of `PrimeTheory`, `MCS`, or `GenericMCSBridge` import `Birelational`
(verified by reading their import headers). Therefore removing it from CanonicalModel removes it
from the transitive closure, which is why TruthLemma must re-add it.

Downstream name usage (real code, not docstrings):
- `TruthLemma.lean`: uses `BForces` (Birelational) throughout (e.g. lines 128, 146, 165, 218, 267).
  Uses no MCS names.
- `Completeness.lean`: uses `BModel` (line 102 — real `instance`/`def`), `IValid`, `MValid`
  (lines 173+) — all Birelational. Uses no MCS names.

Because TruthLemma will `public import Birelational` directly after the fix, the chain
`Completeness -> TruthLemma -> Birelational` keeps `BModel`/`IValid`/`MValid` reachable for
Completeness. No change needed in Completeness.

## Recommended Change Set (regression-free)

### Edit 1 — `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`

Remove these two lines (current lines 11-12), keeping `import Cslib.Init` (line 9) and the other
imports intact:

```
public import Cslib.Logics.Modal.Metalogic.MCS
public import Cslib.Logics.Modal.Semantics.Birelational
```

Resulting import block:
```
import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.PrimeTheory
public import Cslib.Logics.Modal.Metalogic.GenericMCSBridge
public import Cslib.Foundations.Logic.Theorems.DerivationCombinators
```

Note: the removed modules are still mentioned by name in CanonicalModel's docstrings (e.g. the
`## Confirmed Birelational.lean API` section, and `MCS.lean`'s `mcs_and_mem_iff` prose reference).
Those are illustrative prose, not imports, and may remain as-is; they do not require the imports.

### Edit 2 — `Cslib/Logics/Modal/Metalogic/Intuitionistic/TruthLemma.lean`

Add the Birelational import (e.g. immediately after the current line 10
`public import ...Intuitionistic.CanonicalModel`), keeping `import Cslib.Init`:

```
public import Cslib.Logics.Modal.Semantics.Birelational
```

This is required, not optional — TruthLemma directly references `BForces`.

## Verification Procedure

Preferred scoped build (covers the entire affected subtree in one command, since Completeness is
the terminal downstream consumer):

```bash
lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.Completeness
```

This transitively builds `CanonicalModel` and `TruthLemma` too. If it is green, there is no
regression. Optionally re-run
`lake shake --add-public --keep-implied --keep-prefix TruthLemma CanonicalModel` afterward and
confirm it reports no further `remove`/`add` for these two files except the (ignored)
`import Cslib.Init` false positive.

## Why NOT `lake shake --fix`

`--fix` applies **all** shake recommendations mechanically, which here would:

1. **Strip `import Cslib.Init` from both files** — breaking `lake exe checkInitImports` and every
   linter/tactic default those files rely on. This is the decisive reason to avoid `--fix`.
2. Touch **out-of-scope files** the same full-project run flagged (e.g.
   `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` import swaps,
   `Cslib/Logics/Modal/Metalogic/Intuitionistic/PrimeTheory.lean` `Cslib.Init` removal) — not part
   of this task and each with its own `Cslib.Init` false-positive risk.

Use targeted manual edits (Edits 1 and 2 above) instead.

## Zero-Debt / Standards Notes

- No `sorry`, no axioms, no vacuous definitions involved — this is a pure import-hygiene change.
- The `Cslib.Init` requirement (`checkInitImports`) is the one lint/CI invariant that interacts
  with this task; both edited files must retain `import Cslib.Init`.
- Change is small (2 line removals + 1 line addition across 2 files); a single-phase plan suffices.

## Open Considerations for Planner

- The task described a single-file edit; the plan must include the **TruthLemma compensating add**
  or the build will regress. Treat Edits 1 and 2 as an atomic unit.
- Verification should build `...Intuitionistic.Completeness` (not just CanonicalModel), because the
  `public import` re-export means a CanonicalModel-only build would not exercise the consumers that
  could break.
