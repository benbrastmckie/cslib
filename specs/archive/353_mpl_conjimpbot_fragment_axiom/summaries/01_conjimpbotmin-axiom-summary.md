# Implementation Summary: Task #353 — `ConjImpBotMinAxiom`

- **Task**: 353 - Add MPL ⟨∧,→,⊥,⊤⟩ fragment axiom system `ConjImpBotMinAxiom`
- **Status**: [COMPLETED]
- **Date**: 2026-06-25
- **File Modified**: `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`

## What Was Done

Appended `ConjImpBotMinAxiom` — the fourth element of the MPL fragment tower — to
`Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` immediately after the
`ConjImpBotAxiom` block (after line 394, before `end Cslib.Logic.PL`). The change is 143
lines added, 0 deleted. `ConjImpBotAxiom` and all prior declarations are completely untouched.

### Declarations Added (in order)

1. **`inductive ConjImpBotMinAxiom`** (5 constructors: `implyK`, `implyS`, `andI`, `andE1`, `andE2`)
   — the MPL ⟨∧,→,⊥,⊤⟩ fragment, identical to `ConjImpBotAxiom` minus the `efq` constructor.

2. **`ConjImpAxiom.toConjImpBotMinAxiom`** — subsumption from `ConjImpAxiom` into
   `ConjImpBotMinAxiom` (5-case proof).

3. **`ConjImpBotMinAxiom.toMinPropAxiom`** — subsumption into `MinPropAxiom` (not
   `IntPropAxiom`); `MinPropAxiom` has no `efq`, so the 5-case proof type-checks exactly.

4. **`ConjImpBotMinAxiom.mem_implyK`** and **`ConjImpBotMinAxiom.mem_implyS`** — deduction-
   theorem witnesses in the `ConjImpBotMinAxiom` namespace.

5. **`subst_preserves_conjImpBotMinAxiom`** — substitution closure with the `{Atom : Type u}`
   local rebind (matching the pattern in `subst_preserves_conjImpBotAxiom`).

6. **Five `conjImpBotMinAxiom_*_isOrFree` lemmas** — fragment-predicate compatibility for
   `implyK`, `implyS`, `andI`, `andE1`, `andE2` (no `efq_isOrFree` — the MPL tower drops it).

7. **`conjImpBotMinAxiom_hasDeductionTheorem`** — `Metalogic.HasDeductionTheorem` instance.

### Why `MinPropAxiom` (Not `IntPropAxiom`)

`MinPropAxiom` (Axioms.lean:126) contains the five target constructors with no `efq`. This is
the defining feature of minimal logic: `⊥` is a free constant-like atom rather than the least
element with explosion. Using `IntPropAxiom` would fail to type-check (it has `efq`).

## CI Verification Results

| Step | Command | Result |
|------|---------|--------|
| 0 | `lake exe cache get` | PASS (cache warm) |
| 1 | `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` | PASS (660ms) |
| 2 | `lake exe checkInitImports` | PRE-EXISTING FAILURE (Bimodal module broken) — `FragmentAxioms.lean` imports `Cslib.Init` transitively via `Axioms -> Defs -> Init` |
| 3 | `lake exe lint-style` | PASS (no output = clean) |
| 4 | `lake shake --add-public --keep-implied --keep-prefix` | PRE-EXISTING FAILURES in other modules; no issues in `FragmentAxioms.lean` |
| 5 | `lake test` | PRE-EXISTING FAILURES (same 11 broken modules); our module passes |
| 6 | `lake build` (full) | PRE-EXISTING FAILURES (same 11 broken modules) |

**Pre-existing failures** (all unrelated to this task, confirmed by running on the original codebase):
- `Cslib.Logics.Propositional.SequentCalculus` — LK/LJ environment clash
- `Cslib.Logics.Bimodal.*` — multiple broken modules
- `Cslib.Logics.Modal.Denotation` and related
- `Cslib.Logics.Temporal.*`

### Zero-Debt Verification
- Sorry count in modified file: **0**
- New axioms introduced: **0**
- Vacuous definitions: **0**

## Plan Deviations

None. The implementation followed the plan exactly:
- Pure append after line 394, before `end Cslib.Logic.PL`
- Verbatim transcription of the research report's drop-in block (report lines 108-251)
- No new file, no new imports, no `mk_all` needed
- `ConjImpBotAxiom` left untouched

The module docstring was not updated (optional per plan — skipped to minimize risk).

## Artifacts

- Modified: `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (+143 lines)
- Plan: `specs/353_mpl_conjimpbot_fragment_axiom/plans/01_conjimpbotmin-axiom.md`
- Report: `specs/353_mpl_conjimpbot_fragment_axiom/reports/01_conjimpbotmin-axiom.md`
- Summary: `specs/353_mpl_conjimpbot_fragment_axiom/summaries/01_conjimpbotmin-axiom-summary.md`
