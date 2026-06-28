# Research Report: DenseMCS docBlame Violations (Task 356)

**Task type:** cslib | **Session:** sess_1782522754_5f0817_356
**Target file:** `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean`
**Source:** /vet of task 350

## Summary

All six flagged public declarations exist in the current file at the exact line
numbers given in the task description (the file has **not** shifted). Each is a
`theorem` lacking a `/-- ... -/` docstring, triggering the `docBlame` environment
linter. The fix is purely mechanical: insert one brief `/-- ... -/` docstring
immediately before each declaration. No proof changes, no signature changes, no
new imports. Zero-debt compliant (no sorry, no axioms).

## Verification of Declarations

Confirmed by reading the live file. Line numbers are current and accurate.

| # | Declaration | Line | Kind | docstring? |
|---|-------------|------|------|------------|
| 1 | `mp_deriv_fc` | 72 | `theorem` | missing |
| 2 | `weakening_deriv_fc` | 80 | `theorem` | missing |
| 3 | `assumption_deriv_fc` | 87 | `theorem` | missing |
| 4 | `mcs_bot_not_mem_fc` | 324 | `theorem` | missing |
| 5 | `mcs_neg_of_not_mem_fc` | 334 | `theorem` | missing |
| 6 | `mcs_not_mem_of_neg_fc` | 342 | `theorem` | missing |

All six sit under `namespace Cslib.Logic.Temporal` and reference
`Temporal.DerivFc` / `Temporal.SetMaximalConsistentFc` (the FC-parameterized
infrastructure this module introduces).

### Exact signatures and behavior

**1. `mp_deriv_fc` (line 72-78)** — Modus ponens for FC-parameterized derivability.
```
theorem mp_deriv_fc {fc : FrameClass} {Γ : List (Formula Atom)} {φ ψ : Formula Atom}
    (h₁ : Temporal.DerivFc fc Γ (φ → ψ)) (h₂ : Temporal.DerivFc fc Γ φ) :
    Temporal.DerivFc fc Γ ψ
```
From a derivation of `φ → ψ` and a derivation of `φ` at frame class `fc`, produces
a derivation of `ψ`. Unpacks both `Nonempty` derivation trees and applies the
`modus_ponens` constructor.

**2. `weakening_deriv_fc` (line 80-85)** — Weakening / monotonicity in the context.
```
theorem weakening_deriv_fc {fc : FrameClass} {Γ Δ : List (Formula Atom)} {φ : Formula Atom}
    (h : Temporal.DerivFc fc Γ φ) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Temporal.DerivFc fc Δ φ
```
If `φ` is derivable from context `Γ` and every member of `Γ` lies in `Δ`, then `φ`
is derivable from `Δ`. Applies the `weakening` constructor.

**3. `assumption_deriv_fc` (line 87-90)** — Assumption rule.
```
theorem assumption_deriv_fc {fc : FrameClass} {Γ : List (Formula Atom)} {φ : Formula Atom}
    (h : φ ∈ Γ) : Temporal.DerivFc fc Γ φ
```
Any hypothesis present in the context is derivable from it. Applies the
`assumption` constructor.

(Note: these three combinators are exactly the three fields used to build
`temporalDerivationSystemFc` at lines 98-100 — `weakening`, `assumption`, `mp`.)

**4. `mcs_bot_not_mem_fc` (line 324-332)** — Bottom not in an MCS.
```
theorem mcs_bot_not_mem_fc {fc : FrameClass} {Ω : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc fc Ω) : Formula.bot ∉ Ω
```
The falsum `⊥` is never a member of an fc-maximal-consistent set; otherwise the
singleton `[⊥]` would derive `⊥`, contradicting consistency.

**5. `mcs_neg_of_not_mem_fc` (line 334-340)** — Non-membership implies negation membership.
```
theorem mcs_neg_of_not_mem_fc {fc : FrameClass} {Ω : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc fc Ω) {φ : Formula Atom}
    (h_not : φ ∉ Ω) : Formula.neg φ ∈ Ω
```
If `φ` is not in an fc-MCS, its negation `¬φ` is. Direct consequence of negation
completeness (`temporal_negation_complete_fc`).

**6. `mcs_not_mem_of_neg_fc` (line 342-348)** — Negation membership implies non-membership.
```
theorem mcs_not_mem_of_neg_fc {fc : FrameClass} {Ω : Set (Formula Atom)}
    (h_mcs : Temporal.SetMaximalConsistentFc fc Ω) {φ : Formula Atom}
    (h_neg : Formula.neg φ ∈ Ω) : φ ∉ Ω
```
If `¬φ` is in an fc-MCS, then `φ` is not. If both were present, the implication
property would put `⊥` in `Ω`, contradicting `mcs_bot_not_mem_fc`.

## CSLib Docstring Conventions

Confirmed from the existing docstrings in this very file (reuse the established
local style):

- Use `/-- ... -/` (member doc comment) immediately before the declaration, with
  no blank line between docstring and declaration. (`/-! ... -/` is for section
  headers only and does **not** satisfy `docBlame`.)
- Brief: a single sentence/phrase, ending with a period. Examples already present:
  - `/-- Prop-valued derivability at frame class \`fc\`. -/` (line 59)
  - `/-- Theorem derivability at frame class \`fc\` (from empty context). -/` (line 65)
  - `/-- Theorems at fc belong to every fc-MCS. -/` (line 313)
  - `/-- Consistency: phi and neg phi cannot both be in an fc-consistent set. -/` (line 350)
- Backtick-quote Lean identifiers/symbols (e.g. `\`fc\``, `\`⊥\``, `\`φ\``) where it
  aids readability; the existing file mixes plain `fc` and backtick `` `fc` `` —
  either is acceptable, prefer backticks for consistency with the strongest examples.
- For an important result, the file optionally bolds a lead-in (e.g. line 217:
  `/-- **Deduction Theorem at arbitrary fc**: ... -/`). Not required for these six
  routine combinators/lemmas; a plain phrase suffices.

## Proposed Docstring Text

Insert each line immediately above the corresponding `theorem` keyword.

**1. `mp_deriv_fc`**
```lean
/-- Modus ponens for fc-parameterized derivability: from `φ → ψ` and `φ` derive `ψ`. -/
```

**2. `weakening_deriv_fc`**
```lean
/-- Weakening for fc-parameterized derivability: enlarging the context preserves derivability. -/
```

**3. `assumption_deriv_fc`**
```lean
/-- Assumption rule for fc-parameterized derivability: any hypothesis in the context is derivable. -/
```

**4. `mcs_bot_not_mem_fc`**
```lean
/-- Falsum `⊥` is never a member of an fc-maximal-consistent set. -/
```

**5. `mcs_neg_of_not_mem_fc`**
```lean
/-- In an fc-MCS, if `φ` is not a member then its negation `¬φ` is (negation completeness). -/
```

**6. `mcs_not_mem_of_neg_fc`**
```lean
/-- In an fc-MCS, if the negation `¬φ` is a member then `φ` is not. -/
```

## Reuse Check

No new abstractions are introduced or recommended — this is documentation only.
The six theorems already wrap existing infrastructure (`DerivationTree`
constructors and `Metalogic.SetMaximalConsistent` projections). Reuse-first
philosophy is satisfied trivially.

## Implementation Guidance

- Single file, six `Edit` insertions. Each edit anchors on the unique
  `theorem <name>` line and prepends the proposed `/-- ... -/` line.
- Verification: `lake build Cslib.Logics.Temporal.Metalogic.DenseMCS` then
  `lake lint` (confirm the six `docBlame` warnings for this file are gone).
- No risk to proofs; docstrings do not affect elaboration of theorem bodies.
- Lint note: docstrings here only clear `docBlame`. The file already sets
  `linter.dupNamespace false` and uses `@[nolint dupNamespace]` on the `Temporal.*`
  defs, so naming is not a concern for this change.

## Risks / Blockers

None. Mechanical documentation fix, zero-debt compliant.
