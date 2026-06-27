# Research Report: Fix Linter Suppressions in Task-350 Files (Task 357)

## Summary

Five global `set_option linter.* false` directives across four task-350 files were
investigated by empirically removing each suppression and rebuilding the affected
module to observe the actual warnings. Key results:

- **Most suppressions are UNNECESSARY** and can simply be deleted (no warning surfaces).
- **`maxHeartbeats` overrides are UNNECESSARY**: all three files build cleanly at the
  default 200000 heartbeats. Removing them also removes the need for
  `linter.style.setOption false` (which only fired on `maxHeartbeats`).
- **Only two suppressions guard real warnings**: `linter.style.emptyLine` in
  `DeductionTheorem.lean` (blank lines inside `match` commands) and `linter.flexible` +
  `linter.dupNamespace` in `DenseMCS.lean`.
- **`@[nolint dupNamespace]` and `set_option linter.dupNamespace false` are DIFFERENT
  linters**: the attribute silences the `lake lint` environment linter; the `set_option`
  silences the build-time frontend linter. DenseMCS needs both because its declaration
  names intentionally duplicate the `Temporal.` namespace (an established convention also
  used in sibling base files `MCS.lean` and `DerivationTree.lean`).

Method: each file was edited to remove suppressions, the module was rebuilt with
`lake build <Module>`, warnings captured, then all files were restored via `git checkout`.
No edits remain in the working tree.

## Per-File Findings and Fix Strategy

### 1. `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` (lines 43-46)

Suppressions present:
```
set_option linter.style.show false       -- line 43
set_option linter.style.emptyLine false  -- line 44
set_option linter.style.setOption false  -- line 45
set_option linter.flexible false         -- line 46
```

Empirical result (all four removed, module rebuilt): **only `linter.style.emptyLine`
fires** — 11 warnings. No `style.show`, no `flexible`, no `style.setOption` warnings.

| Suppression | Status | Fix |
|-------------|--------|-----|
| `linter.style.show` | UNNECESSARY | delete the line |
| `linter.style.setOption` | UNNECESSARY (file sets no style option / no `maxHeartbeats`) | delete the line |
| `linter.flexible` | UNNECESSARY | delete the line |
| `linter.style.emptyLine` | **REAL** | remove blank lines inside the two `match` commands, then delete the line |

**emptyLine fix detail**: The warnings are blank lines *within* a single command — the
bodies of `deductionWithMem` (around lines 92-136) and `deductionTheorem` (around lines
168-...), where each `match` arm is separated by a blank line, plus the blank line before
`termination_by`. The emptyLine linter forbids empty lines inside a command. Fix = delete
each flagged blank line (the blank line between an arm's last tactic and the next `|`, and
before `termination_by`). These blanks are purely cosmetic; removal is behavior-preserving.

**Recommended end state**: delete all four `set_option` lines (43-46); remove the ~11
intra-command blank lines flagged by `linter.style.emptyLine`.

### 2. `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` (lines 64-66)

```
set_option linter.dupNamespace false      -- line 64
set_option linter.style.setOption false   -- line 65
set_option maxHeartbeats 400000           -- line 66
```

Empirical result (dupNamespace + setOption suppressions removed): **only the
`linter.style.setOption` warning on `maxHeartbeats` fires**. No `dupNamespace` warning
(declarations are `deriv_tree_to_list`, `unfold_listImp_in_tree`, `list_deriv_to_tree`,
`bimodal_deriv_iff_algebraic`, ... — none duplicate the namespace). Dropping the
`maxHeartbeats` line entirely, the module **builds cleanly at default 200000 heartbeats**.

| Line | Status | Fix |
|------|--------|-----|
| `linter.dupNamespace` (64) | UNNECESSARY | delete |
| `linter.style.setOption` (65) | UNNECESSARY once `maxHeartbeats` is gone | delete |
| `maxHeartbeats 400000` (66) | UNNECESSARY (builds at default) | delete |

**Recommended end state**: delete all three lines (64-66).
**Fallback** (only if CI machine variance produces a `maxHeartbeats` timeout): re-add a
*scoped* override `set_option maxHeartbeats 400000 in` immediately before
`deriv_tree_to_list` (the structural-induction proof, the most likely hotspot) rather than
file-global — this is the form the `style.setOption` linter requires and needs no
suppression.

### 3. `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (lines 54-56)

```
set_option linter.dupNamespace false      -- line 54
set_option linter.style.setOption false   -- line 55
set_option maxHeartbeats 400000           -- line 56
```

Identical situation to file 2. dupNamespace never fires; module builds at default
heartbeats. **Recommended end state**: delete all three lines (54-56). Same fallback as
file 2 (scope to `deriv_tree_to_list` if needed).

### 4. `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` (lines 41-44) — SHARED WITH TASK 356

```
set_option linter.style.setOption false   -- line 41
set_option linter.dupNamespace false      -- line 42
set_option linter.flexible false          -- line 43
set_option maxHeartbeats 3200000          -- line 44
```

Empirical result (all four removed): `style.setOption` fires on `maxHeartbeats`;
`dupNamespace` fires on 4 declarations; `flexible` fires on several `simp [...]` calls.
Dropping `maxHeartbeats` entirely, the module **builds cleanly at default 200000**
(the 3200000 override — 16x default — is stale over-allocation).

| Line | Status | Fix |
|------|--------|-----|
| `linter.style.setOption` (41) | UNNECESSARY once `maxHeartbeats` is gone | delete |
| `linter.dupNamespace` (42) | **REAL** (build-time linter) | replace with per-declaration scoped suppression — see below |
| `linter.flexible` (43) | **REAL** | convert flagged `simp [...]` to `simp only [...]`, then delete |
| `maxHeartbeats 3200000` (44) | UNNECESSARY (builds at default) | delete |

**dupNamespace fix (important distinction)**: The 4 declarations
`Temporal.DerivFc`, `Temporal.ThDerivableFc`, `Temporal.SetConsistentFc`,
`Temporal.SetMaximalConsistentFc` are defined inside `namespace Cslib.Logic.Temporal`,
producing full names `Cslib.Logic.Temporal.Temporal.<X>`. They already carry
`@[nolint dupNamespace]`, but **that attribute only silences the `lake lint` environment
linter; the build-time frontend linter `linter.dupNamespace` still fires** (confirmed: the
warnings appeared even with the attributes present). These are two distinct linters.

Renaming to drop the `Temporal.` prefix is **rejected** because:
- The sibling base files `MCS.lean` (`Temporal.SetConsistent`, `Temporal.SetMaximalConsistent`)
  and `DerivationTree.lean` (`Temporal.Deriv`, `Temporal.ThDerivable`) use the identical
  `Temporal.`-prefixed convention inside `namespace Cslib.Logic.Temporal`. The prefix is an
  intentional, library-wide naming convention, not a defect.
- Renaming would break naming consistency with those base files and require updating ~10
  external call sites in `DenseSoundness.lean` and `DenseCompleteness.lean`, plus the file's
  own self-references — out of scope and risk-prone.

**Recommended dupNamespace fix**: replace the file-global `set_option linter.dupNamespace
false` (line 42) with a per-declaration `set_option linter.dupNamespace false in`
immediately before each of the 4 declarations, keeping the existing `@[nolint dupNamespace]`.
Pattern:
```lean
set_option linter.dupNamespace false in
/-- docstring -/
@[nolint dupNamespace]
def Temporal.DerivFc ...
```
This localizes the suppression to exactly the 4 intentionally-duplicated names (satisfying
the task's "per-declaration rather than blanket-suppressing" directive) and mirrors the
existing dual-suppression pattern, without suppressing the linter for the rest of the file.

**flexible fix detail**: The `linter.flexible` warnings are on `simp [...]` calls whose
output a subsequent rigid tactic depends on. Confirmed flagged sites (restored-file line
numbers):
- line 245: `simp [List.mem_cons] at this` → followed by `rcases this`. Fix:
  `simp only [List.mem_cons] at this`.
- line 328 and line 356: `simp [temporalDerivationSystemFc, Temporal.DerivFc]` (modifying
  `⊢`, followed by an `exact` depending on the simplified goal). Fix:
  `simp only [temporalDerivationSystemFc, Temporal.DerivFc]`.
- Also check lines 259 (`simp [h1, DerivationTree.height]`) and 327
  (`simp [List.mem_cons] at hx; exact hx ▸ h_bot`) — convert to `simp only [...]` if the
  linter flags them too.

Implementer procedure: temporarily re-enable the linter, build, and for each flagged
`simp [...]` use `simp?` to obtain the explicit lemma set and replace with the suggested
`simp only [...]`. Verify the proof still closes after each change. Then delete line 43.

**Recommended end state for DenseMCS**: delete lines 41 (`style.setOption`), 43
(`flexible`), 44 (`maxHeartbeats`); replace line 42 with per-declaration
`set_option linter.dupNamespace false in` on each of the 4 decls; convert flagged
`simp [...]` → `simp only [...]`.

## Task 356 Overlap (Coordination Required)

`Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` is **also edited by task 356** (adds
docstrings). Both tasks touch overlapping regions:
- Task 356 adds/edits docstrings on declarations, including the 4 dup-namespaced decls.
- Task 357 (this task) rewrites the header `set_option` block (lines 41-44), inserts
  per-declaration `set_option linter.dupNamespace false in` before the same 4 decls, and
  edits proof bodies (`simp` → `simp only`).

These are not semantically conflicting but edit the same lines/declaration sites.
**Recommendation**: do NOT run 356 and 357 in parallel on DenseMCS. Sequence them (either
order), and have whichever runs second rebase onto the first's changes. The per-declaration
`set_option ... in` from 357 must sit immediately above the `@[nolint dupNamespace]` /
docstring block that 356 maintains; coordinate so the attribute/option/docstring ordering
stays valid (`set_option ... in` then docstring then `@[nolint]` then `def`).

## Verification Performed

- Baseline build of all four modules with suppressions intact: success (645 jobs).
- Build with all suppressions removed: surfaced exactly the warnings tabulated above.
- Build with `maxHeartbeats` overrides removed (default 200000): all three modules build
  successfully — confirming the overrides are unnecessary.
- Confirmed `@[nolint dupNamespace]` does not silence the build-time `linter.dupNamespace`
  (warning fires with the attribute present).
- Confirmed sibling convention via `MCS.lean` / `DerivationTree.lean`.
- All four target files restored to original via `git checkout` (working tree clean for
  these files).

## Zero-Debt / Standards Notes

- No `sorry`, no new axioms, no vacuous definitions involved — all fixes are
  style/structural and behavior-preserving.
- Final CI to run after implementation: `lake build` (the syntax linters run during build),
  then `lake lint`, `lake exe lint-style`, `lake exe checkInitImports`, `lake test`.
- No new abstractions are introduced, so the reuse-first protocol primarily applied to
  confirming the existing `Temporal.`-prefix naming convention (reused, not changed).
