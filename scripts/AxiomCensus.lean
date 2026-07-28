/-
Copyright (c) 2026 CSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Mathlib.Lean.CoreM

open Lean Core

/-!
# Axiom Census

Single-process, whole-`Cslib`-root-import census of `sorryAx`-tainted public declarations.

This is the driver invoked (via `lake env lean --run scripts/AxiomCensus.lean`, not a
registered `lean_exe`) by `scripts/check-axiom-census.sh`. It performs exactly one
`import Cslib` (via `CoreM.withImportModules`), then walks the resulting environment once, so
the whole census stays a single process rather than paying Lean's process-startup and
transitive-import cost once per module (a per-module design was measured at ~370x slower and
is rejected -- see the research report this script implements).

## Implementation-mechanism note (read before changing the axiom walk)

The plan this script implements specifies calling the **builtin** `Lean.collectAxioms` (from
`Lean.Util.CollectAxioms`) directly, on the premise that it is cheap because its results are
cached across declarations via the `exportedAxiomsExt` persistent environment extension (the
same mechanism backing `#print axioms`).

**That premise was tested against this repo's actual built `.olean`s and does not hold here.**
Calling `Lean.collectAxioms` directly, per declaration, in a loop over the ~18279 public
`Cslib.*` candidates was measured to take on the order of several minutes total (individual
calls repeatedly cost tens to hundreds of milliseconds, including on *repeat* calls for the
*same* declaration within the same process -- i.e. `exportedAxiomsExt`'s cross-declaration
cache is not actually being hit for a large fraction of this environment's declarations, for
reasons not further diagnosed here). That is roughly the same order of cost the per-module
design was rejected for, and unacceptable for a gate meant to run in CI and
`pre-pr-check.sh`.

The fix implemented below keeps every other part of the specified design (single process,
whole-root-import, walking the kernel dependency graph exactly as `Lean.collectAxioms` does:
same `ConstantInfo` case dispatch, same `sorryAx`-membership taint definition) but adds an
explicit **shared cache** (`IO.Ref (Std.HashMap Name (Array Name))`, threaded through the
entire census run, not just within one declaration's own recursion) so that a dependency
reached from many different top-level declarations -- which is the overwhelmingly common case
in a project sitting on top of Mathlib -- is only ever walked once. This is the direct
analogue of what `exportedAxiomsExt` is *supposed* to provide but was measured not to provide
here. With the shared cache, the full census (all ~18279 candidates) completes in single-digit
seconds, matching the plan's "a few seconds, not minutes" requirement, and reproduces the
exact same `tainted=43` figure the plan's baseline is built from.

## Method

For every constant `n` such that:
- `n`'s root namespace is `Cslib`,
- `n` is not `Name.isInternal` (auto-generated, not user-facing),
- `n`'s `ConstantInfo` is `.thmInfo`, `.defnInfo`, or `.opaqueInfo` (the three kinds that can
  carry axiom dependencies worth reporting -- constructors/recursors/inductives inherit their
  taint from their own defining declarations), and
- `n` is visible in the *exported* environment (`env.setExporting true`, matching the
  technically correct definition of "public" that this codebase's `module`/`public
  section`/`public import` surface uses; free to compute, and a no-op vs. the simpler
  `Name.isInternal` filter alone on the current tree, but stays correct if that ever changes),

we compute `n`'s transitive axiom set (see `collectAxiomsCached` below) and treat `n` as
tainted iff that set contains `sorryAx`.

## Output

One TSV line per tainted declaration, sorted by name for a stable diff:

    <fully-qualified name>\t<repo-relative file path>\t<reason>

`<reason>` is a durable-anchor debt-ledger entry, in this precedence order:
1. `direct` -- the declaration's own type/value directly contains a `sorry` marker
   (`Expr.hasSorry`), i.e. this is the primary sorry site.
2. `<name>` -- the lexicographically-first constant directly referenced by this declaration's
   type or value (`Expr.getUsedConstants`) that is itself `sorryAx`-tainted (single-hop
   attribution).
3. `transitive` -- no single-hop tainted dependency was found among direct references (the
   taint reaches this declaration through a longer chain).

A final summary line `# total=<N> tainted=<M>` is always printed last. This line, not just the
process exit code, is what lets the shell driver distinguish "clean census" from "broken
environment": an empty/unparseable census must never be read as "zero taint".
-/

/-- Collect the transitive axiom set used by declaration `c`, matching
`Lean.collectAxioms`'s own semantics (walk the kernel-level `ConstantInfo` for `c`; an
`axiomInfo` contributes itself; every other kind contributes the union of its immediate
dependencies' axiom sets, found via `Expr.getUsedConstants` on its type and, if present,
value). `cache` is shared across the *entire* census run (not reset per top-level candidate),
so a dependency reached from many declarations -- the common case for anything built on
Mathlib -- is only ever walked once. See the module header for why this explicit cache is
necessary here (measured: the builtin `exportedAxiomsExt` cache `Lean.collectAxioms` normally
relies on is not being hit for a large fraction of this environment's declarations). -/
partial def collectAxiomsCached (cache : IO.Ref (Std.HashMap Name (Array Name)))
    (env : Environment) (c : Name) : IO (Array Name) := do
  if let some axs := (← cache.get)[c]? then
    return axs
  -- Cycle guard (mutually-recursive inductives/constructors): register an empty placeholder
  -- before recursing so a cycle back to `c` terminates instead of looping.
  cache.modify (·.insert c #[])
  let collectFromExprs (es : List Expr) : IO (Array Name) := do
    let mut acc : Array Name := #[]
    for e in es do
      for n in e.getUsedConstants do
        acc := acc ++ (← collectAxiomsCached cache env n)
    return acc
  let axioms ← match env.find? c with
    | some (.axiomInfo _) => pure #[c]
    | some (.defnInfo v) => collectFromExprs [v.type, v.value]
    | some (.thmInfo v) => collectFromExprs [v.type, v.value]
    | some (.opaqueInfo v) => collectFromExprs [v.type, v.value]
    | some (.ctorInfo v) => collectFromExprs [v.type]
    | some (.recInfo v) => collectFromExprs [v.type]
    | some (.inductInfo v) => do
        let mut acc ← collectFromExprs [v.type]
        for ctor in v.ctors do
          acc := acc ++ (← collectAxiomsCached cache env ctor)
        pure acc
    | some (.quotInfo _) => pure #[]
    | none => pure #[]
  let sorted := (axioms.toList.eraseDups).toArray.qsort (Name.lt · ·)
  cache.modify (·.insert c sorted)
  return sorted

/-- Repo-relative `.lean` file path for the module that owns declaration `name`, or `"?"` if
the owning module cannot be resolved (should not happen for any constant actually reached by
this walk, but is not treated as fatal -- it is ledger metadata, not part of the taint
comparison). -/
def moduleFilePath (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx =>
    match env.header.moduleNames[idx]? with
    | some modName => modName.toString.replace "." "/" ++ ".lean"
    | none => "?"
  | none => "?"

/-- All constants directly referenced by `info`'s type and, if present, its value. Used only
for single-hop taint attribution (reason precedence tier 2), not for the taint check itself. -/
def directRefs (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  let fromValue := (info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
  fromType ++ fromValue

/-- `true` iff `info`'s own type or value directly contains a `sorry` marker, i.e. `name` is
itself a primary sorry site rather than merely a downstream consumer of one. -/
def isDirectSorry (info : ConstantInfo) : Bool :=
  info.type.hasSorry || ((info.value? (allowOpaque := true)).map Expr.hasSorry |>.getD false)

/-- Durable-anchor reason string for `name`'s `sorryAx` taint, per the precedence order
documented in the module header: `direct`, else the lexicographically-first single-hop
tainted dependency, else `transitive`. -/
def taintReason (cache : IO.Ref (Std.HashMap Name (Array Name))) (env : Environment)
    (name : Name) (info : ConstantInfo) : IO String := do
  if isDirectSorry info then
    return "direct"
  let refs := ((directRefs info).qsort (Name.lt · ·)).toList.eraseDups
  for r in refs do
    if r != name then
      let axs ← collectAxiomsCached cache env r
      if axs.contains `sorryAx then
        return r.toString
  return "transitive"

def main : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  CoreM.withImportModules #[`Cslib] (searchPath := searchPath) (trustLevel := 1024) do
    let env ← getEnv
    let exportedEnv := env.setExporting true
    let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
    let mut total : Nat := 0
    let mut rows : Array (Name × String × String) := #[]
    for (name, info) in env.constants.toList do
      if name.getRoot != `Cslib then continue
      if name.isInternal then continue
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        if (exportedEnv.find? name).isSome then
          total := total + 1
          let axs ← collectAxiomsCached cache env name
          if axs.contains `sorryAx then
            let file := moduleFilePath env name
            let reason ← taintReason cache env name info
            rows := rows.push (name, file, reason)
      | _ => pure ()
    let sorted := rows.qsort (fun a b => Name.lt a.1 b.1)
    for (name, file, reason) in sorted do
      IO.println s!"{name}\t{file}\t{reason}"
    IO.println s!"# total={total} tainted={sorted.size}"
    return 0
