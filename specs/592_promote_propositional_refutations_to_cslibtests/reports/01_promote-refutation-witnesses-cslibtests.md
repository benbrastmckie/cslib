# Research Report: Promote the Three Cited-but-Absent Propositional Refutation Witnesses into CslibTests/

- **Task**: 592
- **Type**: cslib
- **Date**: 2026-08-08
- **Session**: sess_1786219370_0903ea_592
- **Status**: Researched
- **File scope**: `CslibTests/`, `Cslib/Logics/Propositional/Tableau/`

## Executive Summary

The 2026-08-08 correction is confirmed on every point, and the work is smaller and lower-risk
than the original (false) premise implied.

1. **All three witness files exist at HEAD** under
   `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/`. Nothing was
   lost. The `[UNVERIFIED] / evidence lost` branch stays deleted.
2. **Both load-bearing witnesses compile clean at HEAD**, verified by direct
   `lake env lean` runs (exit 0, zero errors, zero sorries) against current Mathlib/Cslib. The
   `#eval` outputs reproduce the documented refutation numbers exactly, including
   `branchesAgree = true`, `decisiveFacts = (true, false)`, and the minimal-closure re-run.
3. **Promotion to `CslibTests/` was prototyped end-to-end and builds green.** I wrote
   module-mode probes of both witnesses into `CslibTests/`, built them with
   `lake build --wfail --iofail`, got `✔ Built` on both, then removed the probes. The
   working tree is back to its prior state.
4. **Three non-obvious blockers were found and solved during prototyping** (Findings 4, 5, 6):
   Mathlib tactic meta-imports, `#guard_msgs` wrapping to survive `--iofail`, and the fact that
   the `--wfail --iofail` gate is *already red at HEAD*.
5. **All 14 citations located with exact text.** Three of them will exceed the 100-column limit
   after substitution and need rewrapping. Scheme.lean:3474 — described in the task as "already
   correct and the reference form to copy" — is in fact **also broken** (Finding 8).

## Findings

### Finding 1: The three witness files exist and are intact

```
specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/
  BetaSplitRefutation.lean     (396 lines)
  HvalidShapeRefutation.lean   ( 84 lines)
  PersistPrototype.lean
  + BetaSplitProbe.lean, ForestComparableProbe.lean, ForestComparableProbe2.lean,
    Gap1FixpointProbe.lean, VariantProbe.lean
```

Landmarks named in the task description all check out: `phiRef1` at BetaSplitRefutation.lean:235,
`report` at :213, `phiK_valid : IValid phiK` at HvalidShapeRefutation.lean:65,
`valuation_not_upward_closed` at :57.

There is **no** `specs/430_*` directory at the repository root — the task directory was archived,
which is the second reason the citations do not resolve (see Finding 8).

### Finding 2: Both witnesses compile clean at HEAD

Direct verification, current toolchain (`lean4 v4.33.0-rc1`, mathlib rev `169c26b5`):

| File | Command | Result |
|------|---------|--------|
| `HvalidShapeRefutation.lean` | `lake env lean <path>` | **exit 0**, no output, no errors |
| `BetaSplitRefutation.lean` | `lake env lean <path>` | **exit 0**, only `#eval` info output |

Every symbol they depend on still exists in `Cslib/`:

| Symbol | Location |
|--------|----------|
| `intFImpReuseWitnessAnc?` | `Intuitionistic/Expansion.lean:316` |
| `applyPersistenceFixpoint` | `Intuitionistic/Expansion.lean:188` |
| `intStepBranch` | `Intuitionistic/Expansion.lean:205` |
| `isIntuitionisticallyClosed` | `Intuitionistic/Expansion.lean:96` |
| `isMinimallyClosed` | `Intuitionistic/Expansion.lean:110` |
| `intFuelExt` | `Intuitionistic/Scheme.lean:2143` |
| `intuitionisticTableau` | `Intuitionistic/Scheme.lean:5107` |
| `minimalTableau` | `Intuitionistic/Scheme.lean:5119` |
| `intStepBranch_branchingResult_length` | `Intuitionistic/Scheme.lean:4704` (not `private`) |
| `intAccessPreorder`, `..._le_of_isAccessible` | `Intuitionistic/Scheme.lean:268`, `:280` |
| `intExtractValuation`, `intBotForces` | `Intuitionistic/Soundness.lean:1129`, `:1139` |
| `isAccessible` | `Intuitionistic/Rules.lean:92` |
| `IValid` | `Cslib/Logics/Modal/Semantics/Birelational.lean:195` |

### Finding 3: The refutation still reproduces — measured values for the regression assertions

Captured from the live run. These are the exact strings the promoted file's `#guard_msgs`
annotations must carry:

| Expression | Output |
|------------|--------|
| `report phiRef1 40` | `("OPEN", 17, 2, [(1, 0), (2, 1)], [(1, 2), (2, 2)], some (2, 1, 2))` |
| `atomTable phiRef1 40` | `[(2, [2, 3]), (1, [3]), (0, [])]` |
| `atRealFuel` | `("OPEN", 17, 2, [(1, 0), (2, 1)], [(1, 2), (2, 2)], some (2, 1, 2))` |
| `branchesAgree` | `true` |
| `fimpWitnesses` | `[1]` |
| `decisiveFacts` | `(true, false)` |
| `reportMin phiRef1 realFuel` | `("OPEN", 17, 2, [(1, 0), (2, 1)], [(1, 2), (2, 2)], some (2, 1, 2))` |
| `minBranchesAgree` | `true` |
| `minAtomTable` | `[(2, [2, 3]), (1, [3]), (0, [])]` |

The decisive triple is `some (2, 1, 2)`: world `2` and world `1` are augmented-preorder-
equivalent, and `pr` (atom `2`) is forced at `2` but not at `1`. `branchesAgree = true` and
`minBranchesAgree = true` confirm the local recreation still tracks the real
`intuitionisticTableau` / `minimalTableau`.

**Do not promote these as assertions**: `report phiRef2 40` yields `... none` (no violation);
`phiRef2` is a variant that does *not* exhibit the defect. Only `phiRef1` is load-bearing.
`phiRef3` / `phiRef4` do reproduce it but are robustness variants, not cited by any annotation.

### Finding 4: CslibTests requires module mode — and Mathlib tactics need explicit `meta` imports

Every one of the 21 existing `CslibTests/*.lean` files begins with `module`. Both witnesses are
legacy-mode files. Conversion is mandatory, and the doubled-import idiom
(`import X` + `public meta import X`) from `AncestorRedirectRefutation.lean` /
`S4LoopGuardRegression.lean` is required so `#eval` can reach compiled code.

**The non-obvious part**: `public meta import ...Scheme` is *not sufficient*. Scheme.lean imports
`Mathlib.Tactic.Ring` non-publicly, so it does not propagate. My first probe failed with:

```
CslibTests/ZzProbeBeta.lean:29:5:  error: unknown tactic      -- `ring`
CslibTests/ZzProbeBeta.lean:123:60: error: unknown tactic      -- `norm_num`
```

Both live in `BetaSplitRefutation.lean`'s `termination_by`/`decreasing_by` machinery
(`sum_map_pow_const₄`, and the four `Nat.one_le_pow _ _ (by norm_num)` sites). Adding

```lean
import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.NormNum
```

resolved both. `simp`, `omega`, `decide`, `rintro`, `refine` were already available.
`HvalidShapeRefutation.lean` needs no extra tactic imports.

The verified working header for the BetaSplit promotion:

```lean
module

import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
public meta import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
import Cslib.Logics.Propositional.Defs
public meta import Cslib.Logics.Propositional.Defs
import Cslib.Foundations.Logic.Tableau.Branch
public meta import Cslib.Foundations.Logic.Tableau.Branch
import Mathlib.Tactic.Ring
public meta import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.NormNum
```

`private lemma` declarations survive the move (`weak.linter.privateModule = false` is set for the
`CslibTests` lib in `lakefile.toml`).

### Finding 5: Bare `#eval` breaks the `--iofail` gate; `#guard_msgs` is mandatory

`BetaSplitRefutation.lean` has 14 bare `#eval`s. Under the pipeline's step-5 gate
(`lake build --wfail --iofail`, `scripts/pre-pr-check.sh:78`) each emits an `info:` message and
the target is recorded as failed. Measured directly:

```
info: CslibTests/ZzProbeBeta.lean:362:0: ("OPEN", 17, 2, ...)
...
Some required targets logged failures:
- CslibTests.ZzProbeBeta
```

After wrapping the nine compact evals in `/-- info: ... -/ #guard_msgs in #eval` (values from
Finding 3) and deleting the five verbose/non-load-bearing ones, the same build gives:

```
✔ [972/972] Built CslibTests.ZzProbeBeta (1.8s)
```

Zero warnings, zero info output. This also converts the file from a printout into a genuine
regression test, matching `TableauConformance.lean`'s stated rationale and
`S4LoopGuardRegression.lean`'s practice.

**Evals to drop** (output is multi-page or not load-bearing): `report phiRef2 40`,
`report phiRef3 40`, `report phiRef4 40`, `tableAtRealFuel`, `branchDump`,
`reportMin phiRef3 realFuel`, `reportMin phiRef4 realFuel`. Keep the underlying `def`s — they
stay inspectable interactively and cost nothing.

### Finding 6: The `--wfail --iofail` gate is ALREADY RED at HEAD

Important so the implementer does not chase a phantom regression. At HEAD, with no changes:

```
$ lake build --wfail --iofail Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
warning: .../Scheme.lean:689:6: declaration uses `sorry`
warning: .../Scheme.lean:7862:6: declaration uses `sorry`
Some required targets logged failures:
- Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
error: build failed        # EXIT 1
```

The correct acceptance criterion is therefore **"the two new `CslibTests.*` targets report
`✔ Built` with no warnings and no `info:` lines, and the set of failing targets is unchanged
from the HEAD baseline"** — not "the pipeline is green".

### Finding 7: CI scope — what does and does not touch CslibTests

| Gate | Scope | Effect on this task |
|------|-------|---------------------|
| `lake exe checkInitImports` | filters `name.getRoot = \`Cslib\`` (`scripts/CheckInitImports.lean:33`) | **Exempt.** No existing CslibTests file imports `Cslib.Init`; the new ones must not either. |
| `check-sorry-suppressions.sh` | `SCAN_ROOT="Cslib"` (:111) | **Exempt.** |
| `check-axiom-census.sh` | `CoreM.withImportModules #[\`Cslib]`, skips `name.getRoot != \`Cslib\`` | **Exempt.** |
| `lake shake` | `--keep-prefix Cslib` | Low risk; the doubled Mathlib tactic imports are genuinely used. Re-run `check-shake-residue.sh` after the build to confirm no new baseline entries. |
| `lake build --wfail --iofail` | **full repo, includes CslibTests** | The real gate. See Findings 5 and 6. |
| `lake test` | `testDriver = "CslibTests"` | Builds the `CslibTests` lib root, i.e. `CslibTests.lean`. **This is the CI-protection mechanism** — a file not listed in the barrel is never built. |
| `lake exe lint-style` | text linter, 100-column limit | See Finding 9. Both witnesses are already ≤100 (max 98 and 100). |

### Finding 8: Scheme.lean:3474 is NOT a correct reference form

The task description states :3474 "is already correct and is the reference form to copy". It is
not. Current text:

```
`specs/430_.../scratch/PersistPrototype.lean` assumed as a hypothesis, before it was known to be
```

Two independent defects: (a) the literal ellipsis `430_...` is not a path; (b) there is no
`specs/430_*` at the repository root — the directory is `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/`.
So :3474 fails to resolve for the same root-relative reason as the other 13, plus an ellipsis.

This does not disturb the task's core correction — the `scratch/` prefix genuinely *was*
task-directory-relative, and :3474 is genuinely the only citation that already reaches for the
repo-root form. It just needs finishing rather than copying. **Treat :3474 as a 14th site to
repair, not as the template.** The repaired form is the full archive path.

Path-rule check: `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/...`
does **not** violate `.claude/rules/no-task-references-in-deliverables.md`. That rule's
`TASK_PATTERN` (`\b[Tt]asks?([[:space:]]+#?|[-_#])[0-9]+(-[0-9]+)?\b`,
`.claude/scripts/lib/task-reference-patterns.sh:31`) requires the literal word `task`/`tasks`
before the digits; a bare directory path does not match. Verified against the pattern source, so
the write-time hook will not block the edit.

### Finding 9: The 14 citations — exact text, and which lines need rewrapping

All 14 confirmed at the stated line numbers. Column limit is 100 (observed maxima: 97-100 across
the four files).

| # | File:line | Current fragment | Len | After +3 | Rewrap? |
|---|-----------|------------------|-----|----------|---------|
| 1 | `Minimal/Completeness.lean:52` | ``(`scratch/BetaSplitRefutation.lean`, `phiRef1 := ...` )`` | 93 | 96 | no |
| 2 | `Minimal/Completeness.lean:149` | ``` -- `isMinimallyClosed` (`scratch/BetaSplitRefutation.lean`'s `reportMin phiRef1 realFuel`, ``` | 92 | 95 | no |
| 3 | `Intuitionistic/Completeness.lean:50` | ``` `phiRef1 := ...` (`scratch/BetaSplitRefutation.lean`, ``` | 92 | 95 | no |
| 4 | `Intuitionistic/Completeness.lean:134` | ``` `scratch/HvalidShapeRefutation.lean`: `IValid (p → (q → p))` holds while the old premise's body ``` | 95 | 98 | no |
| 5 | `Intuitionistic/Completeness.lean:144` | ``` (`scratch/BetaSplitRefutation.lean`, `phiRef1`). Discharging ``` | 60 | 63 | no |
| 6 | `Intuitionistic/Completeness.lean:158` | ``` -- whose underlying content is refuted at `phiRef1` (`scratch/BetaSplitRefutation.lean`, ``` | 90 | 93 | no |
| 7 | `Intuitionistic/Expansion.lean:297` | ``` `scratch/BetaSplitRefutation.lean` exhibits `phiRef1 := ...` ``` | 95 | 98 | no |
| 8 | `Intuitionistic/Scheme.lean:585` | ``` REFUTED (see the `sorry`'s own annotation, and `scratch/BetaSplitRefutation.lean`). Retained here, ``` | 98 | **101** | **YES** |
| 9 | `Intuitionistic/Scheme.lean:747` | ``` -- `scratch/BetaSplitRefutation.lean` (`lake env lean`, zero errors, zero sorries) exhibits ``` | 97 | 100 | borderline (exactly 100) |
| 10 | `Intuitionistic/Scheme.lean:3474` | ``` `specs/430_.../scratch/PersistPrototype.lean` assumed as a hypothesis, before it was known to be ``` | 96 | **151** | **YES** (see Finding 8) |
| 11 | `Intuitionistic/Scheme.lean:7834` | ``` defective premise `tableau_complete` used to demand (`scratch/HvalidShapeRefutation.lean`, ``` | 90 | 93 | no |
| 12 | `Intuitionistic/Scheme.lean:7845` | ``` ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr` (`scratch/BetaSplitRefutation.lean`, zero errors, zero ``` | 98 | **101** | **YES** |
| 13 | `Intuitionistic/Scheme.lean:7929` | ``` -- (`scratch/BetaSplitRefutation.lean`, zero errors, zero sorries). The further step from that ``` | 96 | 99 | no |
| 14 | `Intuitionistic/Scheme.lean:7953` | ``` (`scratch/HvalidShapeRefutation.lean`: `IValid (p → (q → p))` holds while the old `hvalid`'s body ``` | 97 | 100 | borderline (exactly 100) |

Substitutions (delta +3 for both refutation witnesses):

- `scratch/BetaSplitRefutation.lean` -> `CslibTests/BetaSplitRefutation.lean` (11 sites: #1,2,3,5,6,7,8,9,12,13 and the second half of the docstring at #12)
- `scratch/HvalidShapeRefutation.lean` -> `CslibTests/HvalidShapeRefutation.lean` (3 sites: #4,11,14)
- `specs/430_.../scratch/PersistPrototype.lean` -> `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/PersistPrototype.lean` (1 site: #10)

### Finding 10: Barrel registration

`CslibTests.lean` is a hand-maintained barrel whose first line carries a shake directive
(`module  -- shake: keep-all --deprecated_module: ignore`). Two lines must be added in the
existing ASCII sort order:

```lean
public import CslibTests.AncestorRedirectRefutation
public import CslibTests.BetaSplitRefutation      -- NEW (after AncestorRedirect)
...
public import CslibTests.HilbertSearch
public import CslibTests.HvalidShapeRefutation    -- NEW (after HilbertSearch, before ImportWithMathlib)
public import CslibTests.ImportWithMathlib
```

(ASCII sort, so `HML` < `HasFresh` < `HilbertSearch` < `HvalidShapeRefutation` < `ImportWithMathlib`.)
Without these two lines the files are never built and the promotion buys no CI protection.
Prefer editing by hand and verifying with `lake test`; `lake exe mk_all --module` targets the
`Cslib.lean` barrel and should not be relied on to regenerate this one.

### Finding 11: Naming and namespace

Precedent is file-named-after-the-refutation (`CslibTests/AncestorRedirectRefutation.lean`), so:
`CslibTests/BetaSplitRefutation.lean` and `CslibTests/HvalidShapeRefutation.lean`.

For namespaces, `CslibTests/` has two idioms: the older bare `RefuteAncestorRedirect` and the
newer `CslibTests.<FileName>` (`CslibTests.S4LoopGuardRegression`,
`CslibTests.TableauConformance`, `CslibTests.ModalFrameSeparation`). **Use the newer form.**
Both probes verified with `CslibTests.BetaSplitRefutation` / `CslibTests.HvalidShapeRefutation`.

Note the namespace change moves the declarations out of `Cslib.Logic.PL` (where
`HvalidShapeRefutation.lean` currently puts them) — correct, since test declarations must not
land in a library namespace. Keep `open Cslib.Logic.PL` for the notation.

Add `set_option autoImplicit false` (both probes verified with it) and give every declaration a
docstring. `BetaSplitRefutation.lean` currently lacks docstrings on `AugRes`, `expandRaw`,
`branchLabels`, `branchAtoms`, `forcesAtom`, `pa`-`pc`, `realBranch`, `recreatedBranch`,
`expandRawMin`, `reportMin`, `realBranchMin`, `minBranchesAgree`, `minAtomTable`. Whether
`lake lint`'s docBlame reaches `CslibTests` is not worth determining — every existing
`CslibTests/` file documents every declaration, and the cost of matching that is trivial.

## Reuse Check

Ran per the reuse-first protocol before recommending any new construct. **No new abstractions are
needed and none are recommended.** The task is a file move plus comment edits:

- Promotion target and idiom already exist (`CslibTests/AncestorRedirectRefutation.lean`,
  `CslibTests/S4LoopGuardRegression.lean`, `CslibTests/TableauConformance.lean`).
- The `String`-valued-verdict adapter pattern used by the other two regression corpora is **not**
  needed here: `report`/`reportMin` already return `Repr`-able tuples that `#eval` prints, so
  `#guard_msgs` applies directly.
- Every Cslib symbol the witnesses touch already exists (Finding 2). No new definitions, no new
  notation, no new typeclass.
- `goRaw` duplicates `intExpandBranches.go`, which is `private` to `Scheme.lean`. This is
  deliberate and documented in the witness's own module comment (the augmented edge list is a
  proof-side ghost with no runtime counterpart), and `branchesAgree`/`minBranchesAgree` are the
  guard that the recreation stays faithful. **Do not "fix" this by de-privatising
  `intExpandBranches.go`** — that would widen `Cslib/`'s public surface to serve a test.

## Zero-Debt Assessment

No sorry is required anywhere in this task, and none is recommended.

- Both witnesses are already sorry-free and axiom-clean; the promotion is mechanical.
- The sorry census in `Cslib/Logics/Propositional/Tableau/` is **4** and must stay 4:
  `Intuitionistic/Completeness.lean:161`, `Minimal/Completeness.lean:155`,
  `Intuitionistic/Scheme.lean:760`, `Intuitionistic/Scheme.lean:7937`.
  (The two `--wfail` warnings at Scheme.lean:689 and :7862 are the enclosing declarations of
  :760 and :7937 — same two sorries, reported at declaration position.)
- Edits to `Cslib/` are confined to comment/docstring text. No verdict, no annotation, and no
  `sorry` moves. In particular the `DISPOSITION UNDECIDED` framing at Scheme.lean:7840-7860 and
  :7926-7938, and the `[UNVERIFIED]` marker on the inference at :7846, are left exactly as they
  are — this task restores auditability, it does not re-adjudicate.

## Recommendations

Suggested phase decomposition (each phase independently verifiable and committable):

1. **Promote `HvalidShapeRefutation`** — the easy one. Convert to module mode, namespace
   `CslibTests.HvalidShapeRefutation`, add docstrings, add barrel line.
   Verify: `lake build --wfail --iofail CslibTests.HvalidShapeRefutation` reports `✔ Built`.
2. **Promote `BetaSplitRefutation`** — module mode with the six doubled imports from Finding 4,
   namespace `CslibTests.BetaSplitRefutation`, `#guard_msgs` wrapping per Findings 3 and 5, drop
   the seven verbose evals, add docstrings, add barrel line.
   Verify: `✔ Built`, and `lake test`.
3. **Repoint the 13 `scratch/*Refutation.lean` citations**, rewrapping Scheme.lean:585 and :7845.
   Verify: `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/` returns only site #10.
4. **Repair Scheme.lean:3474** to the full archive path, rewrapping the sentence (Finding 8).
   Verify: the same grep returns nothing; every path in the four files resolves from the repo
   root.
5. **Final gate** — `lake test`; `lake build --wfail --iofail` compared against the HEAD baseline
   from Finding 6 (failing-target set unchanged, the two new targets green); sorry census still
   4; `bash scripts/check-shake-residue.sh`.

Two judgment calls worth flagging to the user, both deliberately left as recommendations rather
than decided here:

- The archive path in Scheme.lean:3474 is durable only as long as `specs/archive/430_.../` is not
  re-vaulted. A future vault operation (renumbering at >1000, per `state-management.md`) would
  break it again. Promoting `PersistPrototype.lean` too would make all 14 citations point in-tree
  and immune to that. The task scopes this out deliberately — the prototype is not a refutation
  witness — and I would keep it out of scope, but the fragility is real and should be a known
  consequence rather than a surprise.
- The `scratch/` directory holds five further probe files (`BetaSplitProbe`,
  `ForestComparableProbe`, `ForestComparableProbe2`, `Gap1FixpointProbe`, `VariantProbe`) that no
  in-source comment cites. Out of scope; noted only so the next reader knows they were seen and
  not overlooked.

## Verification Performed

Everything below was executed, not inferred:

| Check | Result |
|-------|--------|
| `lake env lean .../HvalidShapeRefutation.lean` | exit 0 |
| `lake env lean .../BetaSplitRefutation.lean` | exit 0, refutation values as Finding 3 |
| Module-mode probe, HvalidShape, in `CslibTests/` | `lake env lean` exit 0; `lake build --wfail --iofail` -> `✔ Built` |
| Module-mode probe, BetaSplit, in `CslibTests/` | first attempt failed (`ring`/`norm_num` unknown); fixed per Finding 4; `✔ Built` |
| Bare `#eval` under `--iofail` | reproduces target failure |
| `#guard_msgs`-wrapped evals under `--iofail` | clean, `✔ Built (1.8s)` |
| HEAD baseline of `--wfail --iofail` on Scheme | already fails (2 sorry warnings) |
| 14 citations located, with byte lengths | confirmed |
| `TASK_PATTERN` vs. the archive path | no match; hook will not block |
| Probe cleanup | both probe files and their build products removed; `git status` shows no residue in `CslibTests/` |

## References

- Witnesses: `/home/benjamin/Projects/cslib/specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/BetaSplitRefutation.lean`, `.../HvalidShapeRefutation.lean`, `.../PersistPrototype.lean`
- Promotion precedent: `/home/benjamin/Projects/cslib/CslibTests/AncestorRedirectRefutation.lean`, `/home/benjamin/Projects/cslib/CslibTests/S4LoopGuardRegression.lean`, `/home/benjamin/Projects/cslib/CslibTests/TableauConformance.lean`
- Barrel: `/home/benjamin/Projects/cslib/CslibTests.lean`
- Build config: `/home/benjamin/Projects/cslib/lakefile.toml`
- CI pipeline: `/home/benjamin/Projects/cslib/scripts/pre-pr-check.sh`
- Scope gates: `/home/benjamin/Projects/cslib/scripts/CheckInitImports.lean`, `/home/benjamin/Projects/cslib/scripts/check-sorry-suppressions.sh`, `/home/benjamin/Projects/cslib/scripts/AxiomCensus.lean`, `/home/benjamin/Projects/cslib/scripts/check-shake-residue.sh`
- Citation sites: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`, `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`, `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`, `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
