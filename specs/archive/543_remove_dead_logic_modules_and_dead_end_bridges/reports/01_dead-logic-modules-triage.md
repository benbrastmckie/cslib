# Research Report: Dead / Dead-End Logic Modules Triage

**Task type:** cslib
**Scope:** Three module groups flagged in the 2026-07-23 logic-trees review (M5-M7).
**Method:** Import-graph analysis (grep over `--include=*.lean`), file-header/docstring
inspection, successor-module confirmation, and test-target confirmation. No new definitions are
proposed, so the reuse-first protocol reduces to verifying that each module's *consumers* (not
Mathlib alternatives) actually exist.

## Executive Summary / Per-Module Decisions

| Group | Module(s) | Task premise | Verified reality | Decision |
|-------|-----------|--------------|------------------|----------|
| 1 | `Foundations/Logic/PropositionalTableau.lean` (212 L) | Deprecated, superseded, zero real imports | **Confirmed dead** | **DELETE** (file + barrel line + 2 provenance docstring refs) |
| 2 | `Foundations/Logic/Automation/HilbertSearch.lean` (268 L) | "imported by nothing" | **Premise refuted** — live tactic, exercised by a dedicated `lake test` suite | **KEEP** (retain; do not delete). Optional future enhancement is additive, not dead-code removal. |
| 3 | `Propositional/Semantics/Algebra/Bridge.lean` (130 L) + `KripkeBridge.lean` | dead-end bridges, docstrings overclaim reuse | **Confirmed dead-end but mathematically substantive** | **KEEP as independent showcase developments + fix overclaiming docstrings** (routing rejected as net-negative) |

**Net LOC direction:** DOWN. Group 1 removes ~213 lines (file + barrel). Groups 2 and 3 retain
code (the honest finding), so the net reduction is driven entirely by Group 1. Deleting Group 2
or 3 would remove working, tested, or mathematically-substantive material and is not recommended.

---

## Group 1 — `PropositionalTableau.lean`: DELETE (confirmed dead)

**Evidence:**
- File header line 7: `-- DEPRECATED: This file is superseded by Cslib.Foundations.Logic.Tableau.`
- Successor confirmed: `Cslib/Foundations/Logic/Tableau.lean` re-exports the refactored generic
  infrastructure (`Sign`, `SignedFormula`, `RuleResult`, `Branch`, `PropositionalRules`, …).
  `PropositionalRules.lean:15` docstring states the 8 rules were "refactored from
  `Cslib.Foundations.Logic.PropositionalTableau` into the generic `RuleResult F L` framework"
  (the task 297 shared-tableau refactor).
- Only real build entry: barrel `Cslib.lean:104`
  (`public import Cslib.Foundations.Logic.PropositionalTableau`).
- The only other two grep hits are **docstring prose**, not imports:
  - `Tableau/PropositionalRules.lean:15` — provenance ("refactored from …")
  - `Tableau/Sign.lean:19` — provenance ("unifies the `PropSign` from …")

**Action:**
1. Delete `Cslib/Foundations/Logic/PropositionalTableau.lean`.
2. Delete barrel line `Cslib.lean:104`.
3. **Dangling-reference cleanup** (recommended, otherwise two docstrings cite a deleted file):
   - `Tableau/PropositionalRules.lean:15` — reword "refactored from
     `Cslib.Foundations.Logic.PropositionalTableau`" to "refactored from the original monolithic
     propositional-tableau module" (drop the dead module path).
   - `Tableau/Sign.lean:19` — reword "unifies the `PropSign` from
     `Cslib.Foundations.Logic.PropositionalTableau`" similarly (drop the dead path); the sentence
     "This module supersedes both with a single canonical definition" already carries the point.
4. CI: barrel is edited by hand for a removal (`lake exe mk_all --module` regenerates on
   additions). Follow with `lake build` + `lake exe checkInitImports` + `lake shake`.

**Zero-debt note:** pure deletion; introduces no `sorry`, no axiom. Clean.

---

## Group 2 — `HilbertSearch.lean`: KEEP (task premise refuted)

The task states HilbertSearch is "imported by nothing" and that its only references are
"'when ported' comments" in Bimodal. **Both claims are incorrect.**

**Refutation evidence:**
1. **It has a dedicated, wired-in test suite.** `CslibTests/HilbertSearch.lean` opens with
   `public meta import Cslib.Foundations.Logic.Automation.HilbertSearch` and exercises the
   `hilbert_search` tactic across ~24 examples spanning propositional, modal, and temporal
   proof systems (Tier 1-3 positive tests + negative fuel-exhaustion tests). It is registered in
   the test barrel (`CslibTests.lean:11`), and `CslibTests` is the project **testDriver**
   (`lakefile.toml:4`), so these tests run under `lake test`. A proof-search *tactic* needs no
   library import to be "live" — being invoked and green in the test suite is exactly its use.
2. **The cited Bimodal references do not mention HilbertSearch.** `grep HilbertSearch` over
   `Cslib/Logics/Bimodal/` returns **nothing**. The lines the task cites are about an unrelated
   *Bimodal* automation module:
   - `AxiomMatcher.lean:48` — "Ported from `BimodalLogic/Automation/ProofSearch/Core.lean` …"
   - `ProofExtraction.lean:222` — "The full implementation will be provided when the **Automation
     module** is ported." (refers to the Bimodal `ProofSearch` port, not Foundations
     `HilbertSearch`.)

**Decision: KEEP.** Deleting it would delete a passing test suite (~222 test lines) and remove
coverage of a working tactic — a net regression, not dead-code cleanup.

**Optional (separate, additive) opportunity — out of scope for a LOC-reduction task:** the task's
alternative ("wire it into the Modal/Bimodal Hilbert derivations that hand-roll combinator
proofs") is a genuine enhancement that would *increase* utilization, but it is additive work with
its own risk surface (tactic robustness/fuel tuning across those derivations) and should be a
distinct feature task if desired — not folded into this dead-code sweep.

---

## Group 3 — `Bridge.lean` + `KripkeBridge.lean`: KEEP as showcase + fix docstrings

Both modules are imported only by the root barrel (`Cslib.lean:538` and `Cslib.lean:560`); no
`.lean` `import` outside the barrel pulls either, and no proof chain consumes their results. So
the "dead-end" characterization is accurate at the import-graph level. However, both are correct,
mathematically substantive developments, and the two task options ("route consumers through them"
vs "mark as independent showcase") resolve differently after inspecting the code.

### 3a. `Bridge.lean` (`propEvaluateEq`, `boolEvaluateEq`)
- Provides: `propEvaluateEq` (line 97) `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ`; and
  `boolEvaluateEq` (line 117) `BoolEvaluate v φ = AlgEvaluate (fun a => v a) false φ`. These tie
  the two concrete evaluators to the *algebraic* `AlgEvaluate` — the "three-evaluator story."
- **Routing is net-negative.** `Semantics/Bool.lean` already carries its **own direct**
  Bool↔Prop bridge that does not pass through the algebraic layer: `BoolEvaluate_eq_iff`
  (line 125), `Evaluate_eq_BoolEvaluate` (line 144), `tautology_iff_boolEvaluate_true`
  (line 167). Re-routing Bool.lean through `Bridge.lean` would force the basic Bool-semantics
  file to depend on `Semantics/Algebra` (`AlgEvaluate`), inverting the intended layering and
  *adding* code — the opposite of the task's LOC goal.
- **Docstring overclaim to fix:** `Bool.lean:41-46` tells future DPLL/Tseitin work to "reuse the
  existing `Bool↔Prop` bridge (`boolEvaluateEq`, `propEvaluateEq` … in `Semantics/Algebra/
  Bridge.lean`) rather than re-deriving it," and `Algebra.lean:49-51` calls `Bridge.lean` "the
  canonical narrative tying all three evaluators together." Nothing actually consumes it, and the
  *direct* bridge future work would reuse lives in `Bool.lean` itself, not `Bridge.lean`.

### 3b. `KripkeBridge.lean` (Kripke–algebraic Heyting duality)
- Provides the semantic soundness direction of the Kripke–algebraic duality for IPL:
  `kripkeAlgBridge`, `iValidOfHAValid`, `mValidOfGHAValid`, built on Mathlib's
  `HeytingAlgebra (LowerSet (OrderDual World))` (no new typeclass — good reuse).
- **The completeness chain deliberately bypasses it.** The module's own design note (lines 59-62)
  states the converse "is proved in `Algebra.Completeness` via the derivability route"
  (Lindenbaum–Tarski). So the IPL completeness chain intentionally uses a *different* route;
  rerouting it through this semantic duality would be a large refactor, likely LOC-up, and would
  discard the existing working completeness proof.

### Decision for Group 3: **KEEP both as independent showcase developments; relabel docstrings.**
Routing is rejected for both (net-negative, layering inversion / major refactor). These are the
kind of substantive duality results a formal library legitimately retains even without a
downstream consumer. Make the docstrings honest:
- `Bridge.lean` header + `Algebra.lean:49-51`: reframe from "canonical bridge reused by downstream
  work" to "self-contained development of the three-evaluator correspondence
  (`Evaluate`/`BoolEvaluate` ↔ `AlgEvaluate`); no in-tree consumer."
- `Bool.lean:41-46`: point future DPLL/Tseitin work at Bool.lean's *own* `BoolEvaluate_eq_iff` /
  `Evaluate_eq_BoolEvaluate` (the actual direct Bool↔Prop bridge), and demote the
  `Semantics/Algebra/Bridge.lean` mention to a "see also (algebraic reformulation)."
- `KripkeBridge.lean` header: add an explicit "independent showcase — the IPL completeness chain
  uses the derivability route in `Algebra.Completeness`, not this semantic duality" note (its
  design note already half-says this; make it unambiguous that no chain routes through it).

**Alternative if the maintainer prioritizes raw LOC over preserving the dualities:** both files
could be deleted (git preserves them), removing ~130 + KripkeBridge lines from the build. This is
*not* recommended — it discards correct, self-contained duality theorems — but is offered because
the task frames them as "dead-end bridges." The relabel-and-keep path is the recommended default.

---

## Reuse-First / Zero-Debt Compliance
- No new definitions or abstractions are proposed; the only additive suggestion (Group 2 wiring)
  is explicitly deferred to a separate optional task.
- No `sorry`, no new axiom, no vacuous placeholder is introduced by any recommended action.
- Group 1 is a clean deletion; Groups 2-3 are keep + docstring truth-fixes.

## Suggested Implementation Phasing (for the planner)
1. **Phase 1 (LOC down):** Delete `PropositionalTableau.lean`, drop `Cslib.lean:104`, fix the two
   provenance docstrings (`PropositionalRules.lean:15`, `Sign.lean:19`). Build + `checkInitImports`
   + `shake`.
2. **Phase 2 (truth-fix docstrings):** Relabel `Bridge.lean` header, `Algebra.lean:49-51`,
   `Bool.lean:41-46`, and `KripkeBridge.lean` header per Group 3. No code/proof changes.
3. **Phase 3 (verify):** `lake build` + `lake test` (confirms HilbertSearch suite still green,
   proving the Group-2 keep decision). Record final `git diff --stat` LOC delta in the summary.

## Verification Log
- Import graph: `grep -rn --include=*.lean` for each symbol/module across the tree (results in the
  per-group sections). Only barrel entries + docstring prose reference the flagged modules.
- Successor confirmation (Group 1): `Tableau.lean` re-export list; `PropositionalRules.lean:15`.
- Test-target confirmation (Group 2): `CslibTests.lean:11` + `lakefile.toml:4` (`testDriver =
  "CslibTests"`).
- Layering confirmation (Group 3): `Bool.lean` decl list shows its own direct bridge lemmas;
  `KripkeBridge.lean:59-62` design note on the derivability-route completeness proof.
