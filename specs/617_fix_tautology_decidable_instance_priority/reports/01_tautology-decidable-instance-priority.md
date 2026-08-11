# Research Report: `Decidable (Tautology φ)` Instance Priority Collision

**Task**: 617 — fix_tautology_decidable_instance_priority
**Session**: sess_1786405794_f0204e_617
**Date**: 2026-08-10
**Status**: RESEARCHED — defect reproduced red, fix verified green, no blockers

---

## 1. Executive Summary

Every claim in the task description was independently re-verified by direct experiment against
the live tree at HEAD `212318f2`. Nothing in the description is wrong, and no additional defect
was found in the same family. Three results beyond re-confirmation:

1. **The declaration-site form of the fix compiles and every downstream module stays green.**
   The task described the fix in consumer-side `attribute [instance 100]` form. The
   declaration-site form `instance (priority := 100) instDecidableTautologyTableau` was applied
   to `DecisionProcedure.lean:81` and built: `Cslib.Logics.Propositional.Tableau.Classical.
   DecisionProcedure`, `Cslib.Logics.Propositional.ProofSystemEquivalence`, and
   `Cslib.Logics.Propositional.SequentCalculus.LK.Decidability` all built successfully (988 jobs,
   exit 0). The experimental edit was reverted; the working tree is clean.
2. **The red baseline is exactly 7 failures, and the fix takes it to 0.** A copy of
   `CslibTests/Propositional.lean` with one added tableau import produces exactly 7
   ``Tactic `decide` failed`` errors without the fix, and compiles clean (exit 0) with it. The
   blast radius in the description is exact, not approximate.
3. **`#guard_msgs in #synth` works and pins instance selection precisely.** This gives a
   regression guard that names the defect directly, rather than only detecting it as a
   downstream `decide` failure. Verified working.

The single scope question the plan must settle is whether the regression guard goes into the
existing `CslibTests/Propositional.lean` or a new test file. Recommendation and rationale in §6.

---

## 2. The Defect (re-verified)

Two registered instances target `Decidable (Tautology φ)`:

| Instance | File:line | Hypotheses | Kernel-reducible |
|----------|-----------|------------|------------------|
| `instDecidableTautology` | `Cslib/Logics/Propositional/Semantics/Bool.lean:185` | `[Fintype Atom] [DecidableEq Atom]` | **Yes** |
| `instDecidableTautologyTableau` | `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean:81` | `[DecidableEq Atom] [Hashable Atom]` | **No** (stalls on `WellFounded.fix`) |

Both carry default priority (1000). Lean's instance resolution prefers the later-declared
instance among equals, so the tableau instance wins wherever both apply. `Cslib.lean` imports
`Semantics.Bool` at `:597` and `Tableau.Classical.DecisionProcedure` at `:627`, so every consumer
of the barrel receives the inert decider.

### Reproduction (run, not quoted)

Probe importing both modules:

```
#synth Decidable (Tautology (Atom := Bool) (.imp (.atom false) (.atom false)))
⇒ instDecidableTautologyTableau (Proposition.atom false → Proposition.atom false)

example : decide (Tautology (Atom := Bool) (.imp (.atom false) (.atom false))) = true := by decide
⇒ error: Tactic `decide` failed for proposition
    decide (Tautology (Proposition.atom false → Proposition.atom false)) = true
  because its `Decidable` instance ... did not reduce to `isTrue` or `isFalse`.
  After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, and
  `instDecidableTautologyTableau`, reduction got stuck at the `Decidable` instance
```

Verbatim match to the description's quoted error.

### Blast radius, measured

`CslibTests/Propositional.lean:64-90` holds 7 `by decide` tautology `example`s. A copy of that
file with a single line added —

```lean
public meta import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure
```

— produces **exactly 7** ``error: Tactic `decide` failed`` messages and no others. The count is
exact. The rest of the file (the 6 `BoolEvaluate` `decide` theorems and `tautology_soundness`) is
unaffected, because those do not go through a `Decidable (Tautology _)` instance.

---

## 3. The Fix (verified green)

```lean
instance (priority := 100) instDecidableTautologyTableau (φ : Proposition Atom) :
    Decidable (Tautology φ) :=
```

at `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean:81`. One token inserted.

### Evidence

| Check | Result |
|-------|--------|
| `#synth` after fix | `instDecidableTautology (Proposition.atom false → Proposition.atom false)` — flipped back |
| 3 representative `decide` examples under the fix | compile clean |
| Full test file + tableau import, under the fix | exit 0, zero errors (all 7 pass) |
| Same file, fix reverted | exactly 7 `decide` failures |
| Declaration-site build: `DecisionProcedure`, `ProofSystemEquivalence`, `LK.Decidability` | Build completed successfully (988 jobs), exit 0 |
| `Fintype`-free fallback still resolves | `example (φ : Proposition A) : Decidable (Tautology φ) := inferInstance` under `{A : Type} [DecidableEq A] [Hashable A]` — exit 0 |

The last row matters: lowering the priority does not remove the tableau instance from the
`Fintype`-free case, where it is the only candidate. Priority only breaks ties among applicable
instances.

### Why `100` and not `low`

`(priority := 100)` is numerically identical to `(priority := low)`, and `100` is the established
in-repo idiom — all four existing priority annotations in `Cslib/` use the numeric form:
`Foundations/Logic/Connectives.lean:206`, `Foundations/Order/HilbertAlgebra.lean:224`,
`Foundations/Order/BrouwerianSemilattice.lean:260` (all `priority := 100`), plus a documentation
mention at `Logics/Modal/Tableau/SoundnessStep.lean:78`. Use `100`.

---

## 4. Consumers Checked — No Collateral Damage

Every site that could see a changed instance selection was inspected.

**`Cslib/Logics/Propositional/SequentCalculus/LK/Decidability.lean:175`** —
`instDecidableLKDerivable` elaborates `decidable_of_iff (Tautology (ctxToImp Γ A)) ...` under
`variable {Atom : Type u} [DecidableEq Atom] [Hashable Atom]`. **No `Fintype Atom` is in scope**,
so `instDecidableTautology` never applied there and the tableau instance remains the only
candidate. Selection is unchanged. (The instance is `noncomputable` regardless, because
`ctxToImp` uses `Finset.toList`.) Verified by build.

**`Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean:566`** —
`instDecidableDerivablePropositionalAxiom` reduces through `Tautology phi` under
`[Fintype Atom] [DecidableEq Atom]`. That file's imports are `Semantics.Bool`,
`Semantics.SemanticConsequence`, `Metalogic.MCS`, `Metalogic.Soundness` — **no tableau import**,
so the collision never existed there and this instance already resolves (and stays resolved) to
the Boolean decider.

**`Cslib/Logics/Propositional/ProofSystemEquivalence.lean`** and
**`Cslib/Logics/Propositional/Tableau/Classical.lean`** — the other two importers of
`DecisionProcedure`. Built green under the fix.

### Negative finding: this is the only double-registration of its kind

The Intuitionistic and Minimal tableau modules have a superficially identical shape — a tableau
`Decidable (Derivable IntPropAxiom φ)` / `Decidable (Derivable MinPropAxiom φ)` instance in
`Tableau/{Intuitionistic,Minimal}/DecisionProcedure.lean`, alongside a finite-model-property
route in `Metalogic/{Int,Min}Decidability.lean`. **They do not collide**: the FMP routes are
`noncomputable def decidableDerivableIntPropAxiomFMP` / `...MinPropAxiomFMP`, deliberately *not*
registered as instances, and each says so in its own docstring ("This is a **named `noncomputable
def`**, not a registered `instance`"). `Decidable (IValid _)` and `Decidable (MValid _)` likewise
have one registered instance each. So the fix is genuinely one line in one file; there is no
sibling defect to bundle.

---

## 5. Reuse Check (CSLib reuse-first)

No new definition, abstraction, notation, or typeclass is required or recommended. The fix is a
priority annotation on an existing instance. Both deciders already exist, are already sorry-free,
and are already extensionally equivalent by their respective correctness theorems
(`tautology_iff_boolEvaluate_true` and `classicalTableau_decides`). Nothing to search Mathlib for.

---

## 6. The Regression Guard — recommendation

The task's verification step 4 offers a choice: add the tableau import to
`CslibTests/Propositional.lean`, or create a new test file importing both.

**Recommendation: add the import to the existing `CslibTests/Propositional.lean`, plus one
`#guard_msgs in #synth` pin.** Rationale:

- The 7 `decide` tests are already written and already in the barrel (`CslibTests.lean:24`). A new
  file would duplicate them or leave the originals still not exercising the both-in-scope
  configuration — which is the whole point of the step.
- One added import line converts 7 accidentally-passing tests into 7 deliberately-passing ones,
  at zero maintenance cost. Verified: the modified file compiles clean under the fix.
- Adding a new file additionally requires touching `CslibTests.lean` (and `lake exe mk_all
  --module` for `Cslib.lean` if it were a library file — not applicable to tests, but it is one
  more moving part).

### Import form

Mirror the file's existing style:

```lean
public meta import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure
```

The `meta`-only form is sufficient here and was verified (exit 0). Note that
`CslibTests/TableauConformance.lean:36-40` documents needing *both* `import X` and `public meta
import X` — that applies when the test body references constructors or definitions from the
module directly. This task's tests only need the instance visible to typeclass resolution, so
the `meta` form alone suffices. (Empirically confirmed: a probe using only `public meta import`
compiled all 7 tests; a separate probe that wrote `inferInstance` explicitly in a non-`meta`
definition did hit `may not access declaration ... imported as 'meta'` — but no such term appears
in the test file.)

### Explicit instance pin (recommended addition)

```lean
/-- info: instDecidableTautology (Proposition.atom false → Proposition.atom false) -/
#guard_msgs in
#synth Decidable (Tautology (Atom := Bool) (.imp (.atom false) (.atom false)))
```

**Verified working** (exit 0 under the fix). This is worth adding on top of the 7 `decide` tests
because it fails with a message that names the defect (`instDecidableTautologyTableau` instead of
`instDecidableTautology`), whereas the 7 `decide` failures only report that reduction got stuck.
`#guard_msgs` is already an established idiom in `CslibTests/` (20 conformance rows in
`TableauConformance.lean`).

---

## 7. Documentation Changes (recommended, small)

The priority annotation is invisible in intent unless the docstrings say why. Without this, a
future contributor reasonably "cleans up" the annotation and silently reinstates the defect.

1. **`DecisionProcedure.lean:76-80`** — the `instDecidableTautologyTableau` docstring currently
   says only "This is an alternative to the Boolean enumeration `instDecidableTautology` in
   `Bool.lean`. The two instances are extensionally equivalent but use different algorithms."
   Extend it to state that the priority is deliberately lowered because this instance does not
   reduce in the kernel, so `decide` must fall through to the Boolean enumeration whenever
   `Fintype Atom` is available; and that it remains the sole candidate in the `Fintype`-free case.
2. **`DecisionProcedure.lean:16`** — the module header says "This module delivers the `Decidable
   (Tautology φ)` instance", which after the fix overstates it. Soften to "a `Decidable
   (Tautology φ)` instance ... at lowered priority".
3. **`Semantics/Bool.lean:181-187`** (optional) — note that `instDecidableTautology` is the
   preferred instance when `Fintype Atom` is available, and that it is the one `decide` uses.

These are prose-only and cannot affect the build beyond the docstring linters.

---

## 8. Verification Plan for Implementation

Ordered, with the red-baseline step first as the task requires.

1. **Red baseline.** Add the tableau import to `CslibTests/Propositional.lean` *before* touching
   `DecisionProcedure.lean`, and run `lake build CslibTests.Propositional` (or `lake env lean` on
   the file). Expect exactly 7 ``Tactic `decide` failed`` errors. Do not skip — this is what makes
   the guard meaningful.
2. **Apply the fix.** `instance (priority := 100) instDecidableTautologyTableau` at
   `DecisionProcedure.lean:81`.
3. **Confirm the flip.** The `#guard_msgs in #synth` pin from §6 passes, i.e. resolution names
   `instDecidableTautology`.
4. **Confirm green.** `CslibTests/Propositional.lean` compiles with 0 errors.
5. **Docstrings.** Apply §7.
6. **Full CI.** `lake build`; `lake exe checkInitImports`; `lake lint`; `lake exe lint-style`;
   `lake test`.

### Notes on the CI steps

- **`lake shake` is not a risk here.** It is disabled in CI (`.github/workflows/lean_action_ci.yml`
  has the step commented out with a recorded rationale), and the local invocation is scoped to
  the `Cslib` target (`lake shake --add-public --keep-implied --keep-prefix Cslib`), which does not
  cover `CslibTests/`. So the instance-only test import will not be flagged as unused. The
  priority annotation changes no imports, so `scripts/check-shake-residue.sh`'s baseline is
  unaffected.
- **`lake exe checkInitImports`** targets library files; `CslibTests/Propositional.lean` already
  passes today without importing `Cslib.Init`, and adding an import does not change that.
- **Pre-existing unrelated warnings.** The build already emits `linter.unusedDecidableInType`
  warnings for `ivalid_universe_invariant` (`Tableau/Intuitionistic/DecisionProcedure.lean:159`)
  and `mvalid_universe_invariant` (`Tableau/Minimal/DecisionProcedure.lean:173`). These are
  present at HEAD, are unrelated to this task, and should not be "fixed" here.

---

## 9. Zero-Debt Compliance

No `sorry`, no new axiom, no vacuous definition, and no deferral is involved. The change is a
priority annotation plus an import plus docstring prose. Both instances involved are already
sorry-free (`DecisionProcedure.lean:38-43` records this). Nothing about this task can introduce
proof debt.

---

## 10. Files in Scope

| File | Change |
|------|--------|
| `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean` | `(priority := 100)` at `:81`; docstring at `:76-80`; header wording at `:16` |
| `CslibTests/Propositional.lean` | one `public meta import`; one `#guard_msgs in #synth` pin |
| `Cslib/Logics/Propositional/Semantics/Bool.lean` | optional docstring note at `:181-187` |

`Bool.lean` is outside the task's declared `file_scope` and its change is optional prose only;
the plan should either add it to scope explicitly or drop it.

---

## 11. Provenance

Surfaced as finding **C1** of `specs/reviews/review-2026-08-10.md:76-121` — the single finding in
that review classified as a defect in code rather than in prose. All experiments in this report
were re-run independently against HEAD `212318f2`; the working tree was left clean (the
experimental edit to `DecisionProcedure.lean` was reverted with `git checkout --` and the module
rebuilt to restore the baseline `.olean`).
