# Research Report: Namespace Lint Errors (Task 209)

## Summary

The 298 namespace lint errors come from two Batteries env_linters run by `lake lint`:
- **topNamespace** (239 errors): Auto-generated instance names not under any namespace
- **dupNamespace** (59 errors): Consecutive duplicate namespace components in declaration names

Both linters are defined in Batteries (`Batteries.Tactic.Lint.Misc`) and CSLib (`Cslib.Foundations.Lint.Basic` for topNamespace). The errors are structurally simple and fall into well-defined patterns. Fixes are mechanical but carry moderate downstream risk for the dupNamespace category.

## Error Category A: topNamespace (239 errors)

### Root Cause

Instance declarations in ProofSystem/Instances files use anonymous `instance` syntax inside a `section` but outside any `namespace`. Lean auto-generates names like `instModusPonensFormulaHilbertK` at the root (top-level) namespace. The `topNamespace` linter requires every declaration to live under a registered namespace.

### Affected Files (17 files)

| File | Errors | Logic |
|------|--------|-------|
| `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` | 39 | Bimodal |
| `Cslib/Logics/Temporal/ProofSystem/Instances.lean` | 30 | Temporal |
| `Cslib/Logics/Modal/ProofSystem/Instances/K.lean` | 8 | Modal K |
| `Cslib/Logics/Modal/ProofSystem/Instances/B.lean` | 10 | Modal B |
| `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` | 10 | Modal D |
| `Cslib/Logics/Modal/ProofSystem/Instances/T.lean` | 10 | Modal T |
| `Cslib/Logics/Modal/ProofSystem/Instances/K4.lean` | 10 | Modal K4 |
| `Cslib/Logics/Modal/ProofSystem/Instances/K5.lean` | 10 | Modal K5 |
| `Cslib/Logics/Modal/ProofSystem/Instances/D4.lean` | 12 | Modal D4 |
| `Cslib/Logics/Modal/ProofSystem/Instances/D5.lean` | 12 | Modal D5 |
| `Cslib/Logics/Modal/ProofSystem/Instances/DB.lean` | 12 | Modal DB |
| `Cslib/Logics/Modal/ProofSystem/Instances/TB.lean` | 12 | Modal TB |
| `Cslib/Logics/Modal/ProofSystem/Instances/S4.lean` | 12 | Modal S4 |
| `Cslib/Logics/Modal/ProofSystem/Instances/K45.lean` | 12 | Modal K45 |
| `Cslib/Logics/Modal/ProofSystem/Instances/KB5.lean` | 12 | Modal KB5 |
| `Cslib/Logics/Modal/ProofSystem/Instances/D45.lean` | 14 | Modal D45 |
| `Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` | 14 | Modal S5 |

### Fix Strategy

Wrap each `section ...Instances` block in an appropriate namespace:

```lean
-- BEFORE (in Cslib/Logics/Modal/ProofSystem/Instances/K.lean):
section ModalInstances
instance : InferenceSystem Modal.HilbertK ...
instance : ModusPonens Modal.HilbertK ...
end ModalInstances

-- AFTER:
namespace Cslib.Logic.Modal
section ModalInstances
instance : InferenceSystem Modal.HilbertK ...
instance : ModusPonens Modal.HilbertK ...
end ModalInstances
end Cslib.Logic.Modal
```

Most Modal files already have a `namespace Cslib.Logic.Modal` block above for their axiom definitions -- the fix is to extend that namespace to wrap the instances section, or add a second namespace block around the instances.

**Namespace choices:**
- Modal files: `namespace Cslib.Logic.Modal`
- Bimodal Instances.lean: `namespace Cslib.Logic.Bimodal`
- Temporal Instances.lean: `namespace Cslib.Logic.Temporal`

### Risk Assessment: LOW

- Instance names are auto-generated and never referenced explicitly in user code
- Instance resolution works by typeclass, not by name
- Adding a namespace changes the auto-generated name (e.g., `instModusPonensFormulaHilbertK` becomes `Cslib.Logic.Modal.instModusPonensFormulaHilbertK`) but this does not affect semantics
- No downstream files need updating
- Grep for all auto-generated instance name patterns (`instModusPonens`, `instNecessitation`, `instHasAxiom`, `instClassicalHilbert`, `instModalHilbert`, `instBimodal`, `instTemporalNec`, `instInferenceSystem`) found zero explicit references

## Error Category B: dupNamespace (59 errors)

### Root Cause

Declarations defined with a qualified prefix that duplicates the enclosing namespace. Three patterns:

1. **Chronicle.Chronicle** (30 errors): `structure Chronicle` defined inside `namespace ...Chronicle`, producing `...Chronicle.Chronicle`
2. **Temporal.Temporal.X** (17 errors): `def Temporal.Deriv`, `abbrev Temporal.SetConsistent`, etc. inside `namespace Cslib.Logic.Temporal`
3. **Bimodal.Bimodal.X** (12 errors): `def Bimodal.Deriv`, `def Bimodal.Derivable`, etc. inside `namespace Cslib.Logic.Bimodal`

### Affected Files (8 files)

| File | Errors | Dup Component | Pattern |
|------|--------|---------------|---------|
| `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` | 15 | Chronicle | struct name = namespace |
| `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` | 15 | Chronicle | struct name = namespace |
| `Cslib/Logics/Bimodal/ProofSystem/Derivable.lean` | 10 | Bimodal | qualified def in matching ns |
| `Cslib/Logics/Temporal/ProofSystem/Derivable.lean` | 9 | Temporal | qualified def in matching ns |
| `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` | 4 | Temporal | qualified abbrev in matching ns |
| `Cslib/Logics/Temporal/Metalogic/MCS.lean` | 2 | Temporal | qualified abbrev in matching ns |
| `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` | 2 | Temporal | qualified def in matching ns |
| `Cslib/Logics/Bimodal/Metalogic/Core/DerivationTree.lean` | 2 | Bimodal | qualified def in matching ns |

### Fix Strategy

#### Sub-pattern B1: Chronicle struct (30 errors)

**Option 1 (Recommended): Close namespace before struct, reopen after.**

```lean
-- BEFORE (in namespace Cslib.Logic.Temporal.Metalogic.Chronicle):
structure Chronicle (Atom : Type*) where ...
def Chronicle.c0 ...

-- AFTER:
end Cslib.Logic.Temporal.Metalogic.Chronicle
-- Define at parent namespace level:
namespace Cslib.Logic.Temporal.Metalogic
structure Chronicle (Atom : Type*) where ...
def Chronicle.c0 ...
end Cslib.Logic.Temporal.Metalogic
namespace Cslib.Logic.Temporal.Metalogic.Chronicle
```

This changes the FQN from `...Chronicle.Chronicle` to `...Metalogic.Chronicle`, keeping `Chronicle.c0` etc. as `Cslib.Logic.Temporal.Metalogic.Chronicle.c0`.

**Option 2: Rename struct to avoid collision.**

Rename `Chronicle` to something like `ChronicleData` -- but this would require updating 97+ references across many files.

**Option 3: Use `@[nolint dupNamespace]` annotation.**

```lean
@[nolint dupNamespace]
structure Chronicle (Atom : Type*) where ...
```

This suppresses the error without code changes. The `nolint` attribute on the structure also suppresses for auto-generated `.mk`, `.rec`, field projectors, etc.

**Recommendation**: Option 3 (`@[nolint dupNamespace]`) is safest and most pragmatic for the Chronicle pattern. The struct-in-matching-namespace pattern is an intentional design choice (the namespace `Chronicle` groups all chronicle-related definitions), and the duplication is harmless. Option 1 would work but changes the import structure of everything in the Chronicle namespace.

#### Sub-pattern B2: Temporal.X / Bimodal.X qualified defs (29 errors)

**Fix: Remove redundant qualifier.**

```lean
-- BEFORE (inside namespace Cslib.Logic.Temporal):
def Temporal.Deriv (...) := ...
def Temporal.ThDerivable (...) := ...
abbrev Temporal.SetConsistent (...) := ...

-- AFTER (inside namespace Cslib.Logic.Temporal):
def Deriv (...) := ...
def ThDerivable (...) := ...
abbrev SetConsistent (...) := ...
```

This produces the same logical FQN minus the duplication: `Cslib.Logic.Temporal.Deriv` instead of `Cslib.Logic.Temporal.Temporal.Deriv`.

### Downstream Impact Analysis for B2

Removing the redundant qualifier changes the short name used at reference sites. All uses of `Temporal.Deriv` within `namespace Cslib.Logic.Temporal` resolve fine with just `Deriv`. But uses in other namespaces that currently write `Temporal.Deriv` (which resolves to `Cslib.Logic.Temporal.Temporal.Deriv`) will need to change to just `Deriv` (with appropriate `open` or full path).

**Reference counts for affected names:**

| Name | References | Files Affected |
|------|-----------|----------------|
| `Temporal.SetMaximalConsistent` | 270 | Many (Temporal Metalogic) |
| `Temporal.SetConsistent` | 39 | Many (Temporal Metalogic) |
| `Temporal.Deriv` | 39 | ~10 files |
| `Temporal.Derivable` | 23 | ~8 files |
| `Temporal.SetMaximalConsistentFc` | 15 | ~5 files |
| `Temporal.DerivFc` | 14 | ~5 files |
| `Temporal.ThDerivable` | 7 | ~3 files |
| `Temporal.ThDerivableFc` | 5 | ~3 files |
| `Temporal.SetConsistentFc` | 5 | ~3 files |
| `Bimodal.Derivable` | 28 | ~8 files |
| `Bimodal.Deriv` | 13 | ~5 files |
| `Bimodal.ThDerivable` | 5 | ~3 files |

**Total**: ~463 reference site updates for the B2 sub-pattern.

Most references are within the same namespace or use `open Cslib.Logic.Temporal`, so they will resolve correctly after removing the qualifier. The key risk is in files that use `Temporal.SetMaximalConsistent` from a different namespace context -- those will need to use `Cslib.Logic.Temporal.SetMaximalConsistent` or add an `open` statement.

**Critical note**: One file explicitly uses the fully-qualified doubled name:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:117` uses `Cslib.Logic.Bimodal.Bimodal.ThDerivable` -- must be updated to `Cslib.Logic.Bimodal.ThDerivable`

### Risk Assessment: MODERATE for B2, LOW for B1

**B1 (Chronicle)**: Using `@[nolint dupNamespace]` has zero risk. Even Option 1 (namespace restructuring) is low risk since Chronicle is mostly self-contained.

**B2 (Temporal/Bimodal qualified defs)**: Moderate risk due to 463+ reference updates. However:
- All references use the short form `Temporal.X` rather than the doubled `Temporal.Temporal.X`
- Within namespace `Cslib.Logic.Temporal`, `Temporal.X` resolves to `Cslib.Logic.Temporal.Temporal.X` -- after the fix, plain `X` resolves to `Cslib.Logic.Temporal.X`
- The resolution chain changes but the target declaration is the same
- Files using `open Cslib.Logic.Temporal` and then referencing `Temporal.Deriv` will break -- they'll need `Deriv` instead

## Implementation Recommendations

### Phase 1: topNamespace fixes (239 errors) -- LOW RISK

1. Add `namespace Cslib.Logic.Modal` around instance sections in all 15 Modal files
2. Add `namespace Cslib.Logic.Bimodal` around instance section in Bimodal/ProofSystem/Instances.lean
3. Add `namespace Cslib.Logic.Temporal` around instance section in Temporal/ProofSystem/Instances.lean
4. Build and verify: `lake build Cslib`

### Phase 2: dupNamespace Chronicle fixes (30 errors) -- LOW RISK

1. Add `@[nolint dupNamespace]` to `structure Chronicle` in both ChronicleTypes.lean files
2. Remove `set_option linter.dupNamespace false` if no other definitions need it
3. Build and verify

### Phase 3: dupNamespace Temporal/Bimodal qualified def fixes (29 errors) -- MODERATE RISK

1. In definition files, remove the redundant `Temporal.`/`Bimodal.` prefix
2. Update all reference sites (grep-and-replace, ~463 sites)
3. Remove `set_option linter.dupNamespace false` from affected files
4. Build and verify iteratively per-file
5. Fix the one explicit `Cslib.Logic.Bimodal.Bimodal.ThDerivable` reference

### Phasing Rationale

Phase 1 is entirely mechanical, zero-risk, and fixes 81% of the errors (239/298).
Phase 2 is a trivial annotation, zero-risk, and fixes 10% of the errors (30/298).
Phase 3 requires careful grep-and-replace across many files but fixes the remaining 10% (29/298).

## Verification

After all fixes, run:
```bash
lake lint 2>&1 | grep -c "is not namespaced"     # should be 0
lake lint 2>&1 | grep -c "is duplicated in the name"  # should be 0
lake build  # should compile clean
```
