# Universe Mismatch Analysis: countermodel_dense

## Task 231 Research Report

### Problem Summary

The theorem `countermodel_dense` in `ChronicleToCountermodelBasic.lean` (line 814) is
blocked by a universe mismatch. The file declares `variable {Atom : Type*}` (universe
polymorphic), but the proof needs to invoke `ParametricCanonicalTaskFrame` which is
defined under `variable {Atom : Type}` (universe 0). Lean cannot unify `Type u_1` with
`Type 0`, so the proof body cannot be completed.

The downstream `completeness_dense` (Dense.lean:122) is also blocked because it depends
on `countermodel_dense`.

### Root Cause

Five files in the `Cslib.Logics.Bimodal.Metalogic.Algebraic` directory use
`variable {Atom : Type}` (universe 0) instead of `variable {Atom : Type*}` (universe
polymorphic):

| File | Line | Declaration |
|------|------|-------------|
| `ParametricCanonical.lean` | 36 | `variable {Atom : Type}` |
| `ParametricHistory.lean` | 37 | `variable {Atom : Type} {fc : FrameClass} ...` |
| `ParametricTruthLemma.lean` | 39 | `variable {Atom : Type} {fc : FrameClass} ...` |
| `ParametricCompleteness.lean` | 37 | `variable {Atom : Type} {D : Type*} ...` |
| `RestrictedParametricTruthLemma.lean` | 41 | `variable {Atom : Type} [DecidableEq Atom] ...` |

All other files in the same directory (BooleanStructure, InteriorOperators,
LindenbaumQuotient, UltrafilterMCS) already use `variable {Atom : Type*}`.

All files in the `BXCanonical/` and `Bundle/` directories also use `variable {Atom : Type*}`.

### Why the Restriction is Artificial

The `Atom : Type` restriction is a porting artifact. Analysis confirms:

1. **All upstream dependencies are universe-polymorphic**:
   - `Formula : Type u -> Type u` (universe polymorphic)
   - `SetMaximalConsistent : {Atom : Type u_1} -> ...` (universe polymorphic)
   - `ExistsTask : {Atom : Type u_1} -> ...` (universe polymorphic)
   - `canonicalRTransitive : {Atom : Type u_1} -> ...` (universe polymorphic)
   - `BFMCS : (Atom : Type u_2) -> (D : Type u_3) -> ...` (universe polymorphic)
   - `FMCS : (Atom : Type*) -> (D : Type*) -> ...` (universe polymorphic)
   - `TaskFrame : (D : Type*) -> ...` (universe polymorphic)

2. **No `Denumerable`, `Countable`, or `Encodable` constraints** appear in any of the
   5 Parametric files that would force `Type 0`.

3. **All 5 files are sorry-free** -- the proofs are complete and well-typed. Changing
   `Type` to `Type*` is a pure generalization.

4. **The proofs use only universe-agnostic tactics and lemmas** -- no explicit universe
   annotations or universe-sensitive constructions.

### Exported Definitions Affected

Generalizing to `Type*` changes the universe signatures of these definitions:

| Definition | Current Signature | After Fix |
|------------|-------------------|-----------|
| `ParametricCanonicalWorldState` | `(Atom : Type) -> Type` | `(Atom : Type u) -> Type u` |
| `parametricCanonicalTaskRel` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| `ParametricCanonicalTaskFrame` | `{Atom : Type} -> TaskFrame D` | `{Atom : Type u} -> TaskFrame D` |
| `ParametricCanonicalTaskModel` | `{Atom : Type} -> TaskModel Atom ...` | `{Atom : Type u} -> TaskModel Atom ...` |
| `parametricToHistory` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| `ParametricCanonicalOmega` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| `ShiftClosedParametricCanonicalOmega` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| `parametric_shifted_truth_lemma` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| `restricted_parametric_shifted_truth_lemma` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| `fully_restricted_parametric_shifted_truth_lemma` | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |
| All completion/countermodel theorems | `{Atom : Type} -> ...` | `{Atom : Type u} -> ...` |

These are all **generalizations** (wider applicability), not restrictions. Every existing
call site that worked with `Atom : Type` will still work, and new call sites with
`Atom : Type u` will also work.

### Proposed Fix

**Phase 1: Generalize Parametric files** (5 files, 5 one-line edits)

Change the `variable` declaration in each file from `{Atom : Type}` to `{Atom : Type*}`:

1. `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCanonical.lean:36`
   ```lean
   -- Before:
   variable {Atom : Type}
   -- After:
   variable {Atom : Type*}
   ```

2. `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricHistory.lean:37`
   ```lean
   -- Before:
   variable {Atom : Type} {fc : FrameClass} ...
   -- After:
   variable {Atom : Type*} {fc : FrameClass} ...
   ```

3. `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricTruthLemma.lean:39`
   ```lean
   -- Before:
   variable {Atom : Type} {fc : FrameClass} ...
   -- After:
   variable {Atom : Type*} {fc : FrameClass} ...
   ```

4. `Cslib/Logics/Bimodal/Metalogic/Algebraic/ParametricCompleteness.lean:37`
   ```lean
   -- Before:
   variable {Atom : Type} {D : Type*} ...
   -- After:
   variable {Atom : Type*} {D : Type*} ...
   ```

5. `Cslib/Logics/Bimodal/Metalogic/Algebraic/RestrictedParametricTruthLemma.lean:41`
   ```lean
   -- Before:
   variable {Atom : Type} [DecidableEq Atom] ...
   -- After:
   variable {Atom : Type*} [DecidableEq Atom] ...
   ```

**Phase 2: Implement countermodel_dense proof body** (ChronicleToCountermodelBasic.lean:825)

After Phase 1, the proof can use `ParametricCanonicalTaskFrame` with `Atom : Type u_1`.
The proof should:
- Construct `cantorBfmcsDense` (which gives `BFMCS Atom Rat fc`)
- Verify restricted coherence (already proved: `cantor_bfmcs_dense_restricted_tc`,
  `cantor_bfmcs_dense_restricted_buc`, `cantor_bfmcs_dense_restricted_fuc`)
- Apply `fully_restricted_parametric_completeness_from_neg_membership` to get
  `\neg truthAt ... \phi`
- Package the result as the existential

**Phase 3: Implement completeness_dense** (Dense.lean:122)

After `countermodel_dense` works, `completeness_dense` can:
- Obtain the countermodel from `countermodel_dense`
- Instantiate `h_valid_dense` with the countermodel's domain type and model
- Derive a contradiction (the model both satisfies and falsifies `\phi`)

### Risk Assessment

**Low risk**. The change is:
- A pure universe generalization (widens applicability, never narrows)
- Applied to sorry-free files (proofs are complete)
- Upstream dependencies are already universe-polymorphic
- No downstream callers exist outside the sorry-blocked `countermodel_dense`

The main risk is that Lean's elaborator might struggle with additional universe
variables in complex proofs, but this is unlikely given that:
- All underlying lemmas already carry universe parameters
- The proofs use standard tactics (simp, rfl, intro, cases, etc.)
- D is already `Type*` in these files, so the universe machinery is already active

### Impact on completeness_dense

After `countermodel_dense` is fixed:
- `completeness_dense` needs a proof that connects `countermodel_dense`'s output to
  `validDense`'s quantification
- `validDense` quantifies over `D : Type` (universe 0)
- `countermodel_dense` produces `D = Rat : Type 0` which matches
- The remaining proof work is purely logical (instantiation and contradiction)

Note: `validDense` quantifies `D : Type` (not `Type*`). The countermodel uses `D = Rat`
which is `Type 0`, so there is no universe issue on the `D` parameter. The only issue
was `Atom`, which this fix addresses.

### Additional Notes

- `ParametricCanonicalWorldState` is defined with explicit `(Atom : Type)` on line 39
  of ParametricCanonical.lean. This definition also needs to change to `(Atom : Type*)`.
- The `DecidableEq Atom` constraint in `RestrictedParametricTruthLemma.lean` is needed
  for subformula closure operations. `DecidableEq` works at any universe.
- The existing sorry comments reference "task 36" which is the WeakCanonical port. The
  universe mismatch is independent of that dependency.
