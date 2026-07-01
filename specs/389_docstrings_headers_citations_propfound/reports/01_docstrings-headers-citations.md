# Research Report — Task 389: Docstrings, Headers, Citations (Prop/Foundations Tier-2)

**Session:** sess_1782924983_6bcecb_389
**Date:** 2026-07-01
**Agent:** cslib-research-agent
**Scope source:** §4.3–4.6 + task 395 reconciliation

## Executive Summary

Task 389 has **four sub-parts (a)–(d)**. Verification against the live codebase shows that
**most of the originally-scoped work has already been completed by intervening tasks (406, 460)**.
The residual actionable work is small:

| Part | Original claim | Live-codebase status | Residual work |
|------|----------------|----------------------|---------------|
| (a) docstrings | 7 undocumented def/abbrev in FreeMeetExtension.lean | **All 7 already documented** (task 406, commit d11d0692) | Optional `fld`→`himpFold` rename only |
| (b) barrels | 4 Tableau barrels need copyright + Cslib.Init | **DROPPED** — all 4 verified present | None |
| (c) omit for 14 unusedSectionVars | mostly Classical/Completeness + Minimal | **Classical done** (task 460, commit 10055ea5); only Minimal/Soundness:118 remains live | 1 confirmed omit + linter-driven sweep after 317 |
| (d) references.bib NegriVonPlato2001 | missing entry cited by OrImpConservative | **Confirmed missing**; cited by ~21 files | Add 1 BibTeX entry |

**Net actionable work:** (d) add one bib entry (independent, safe); (c) one confirmed `omit`
edit in Minimal/Soundness plus a linter-driven sweep sequenced after task 317; (a) an optional
cosmetic rename. Parts (a)-docBlame and (b) are already satisfied.

**STALE SCOPING NOTE CORRECTION:** The delegation warned that Classical/Completeness.lean has
uncommitted 317 WIP that part (c) would interleave with. This is **no longer true**. The working
tree is clean for all Lean files (`git status --short` shows only `specs/` changes). Task 460
(commit 10055ea5, "fix all live lint warnings in Classical/Completeness.lean") already committed
the complete Classical/Completeness lint cleanup — 12 planned + 8 cascaded `omit` sites plus long-line
wraps. Task 317 is still `planned` (not implementing). **The Classical/Completeness portion of
part (c) is DONE and committed; there is no interleaving risk there.**

---

## Part (a) — FreeMeetExtension.lean docstrings

**File:** `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean`

### Finding: all 7 target def/abbrev already carry docstrings

Verified by reading the whole file. Every declaration named in the task already has a docstring
(added by task 406, commit d11d0692 "clear 33 lint violations … Foundations"):

| Declaration | Kind | Current line | Docstring present? |
|-------------|------|--------------|--------------------|
| `fld` | `abbrev` | 51 (doc 49–50) | Yes |
| `fmeLe` | `def` | 110 (doc 107–109) | Yes |
| `fmeEquiv` | `def` | 129 (doc 127–128) | Yes |
| `fmeSetoid` | `def` | 133 (doc 131–132) | Yes |
| `FreeMeetExtension` | `def` | 163 (doc 160–162) | Yes |
| `mk` | `def` (in `namespace FreeMeetExtension`) | 172 (doc 170–171) | Yes |
| `freeMeetEmbed` | `def` | 272 (doc 270–271) | Yes |

**Conclusion:** the docBlame obligation of part (a) is **already satisfied**. No docstring edits
are required. (Instances and theorems in the file are not docBlame targets under CSLib's Mathlib
linter config.)

### Residual: optional `fld` → `himpFold` rename

- `himpFold` does **not** exist anywhere in `Cslib/` (grep: no matches).
- `fld` is used **only inside FreeMeetExtension.lean** (grep across `Cslib/` finds no external
  users) — roughly 15 occurrences, all self-contained.
- `fld` is already lowerCamelCase and lint-compliant, so the rename carries **zero lint value**;
  it is purely the cosmetic naming reconciliation requested by task 395.

**Recommendation:** Treat the rename as OPTIONAL / low priority. If task 395's naming
reconciliation still wants it, it is a safe, self-contained `replace_all` of `fld` → `himpFold`
within this single file (update the `abbrev` and all ~15 references, including the docstring text
"`fld S t = …`"). Otherwise it can be dropped without any lint consequence. If done, rebuild
`Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension` to confirm.

---

## Part (b) — Tableau barrels (DROPPED, verified)

All four barrels carry both the copyright header and `import Cslib.Init` (verified via `head -12`):

- `Cslib/Logics/Propositional/Tableau.lean` — Copyright + `import Cslib.Init` ✓
- `Cslib/Logics/Propositional/Tableau/Classical.lean` — ✓
- `Cslib/Logics/Propositional/Tableau/Minimal.lean` — ✓
- `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` — ✓

**Conclusion:** Part (b) is correctly DROPPED. No work.

---

## Part (c) — `omit` for unusedSectionVars

### Ground-truth linter output (this session)

Ran `lake build` on the Minimal.Soundness + Minimal.Completeness dependency closure (which pulls
in the Intuitionistic Tableau modules) and captured the actual `linter.unusedSectionVars`
warnings. Confirmed live sites:

| File | Line | Declaration | Unused var(s) | Sorry-free? |
|------|------|-------------|---------------|-------------|
| `Tableau/Minimal/Soundness.lean` | 118 | `minimalTableau_sound` | `[Hashable Atom]` | Yes (soundness sorry-free since task 316) |
| `Tableau/Intuitionistic/Expansion.lean` | 162 | `intStepBranch_result_ne_notApplicable` | `[Hashable Atom]` | Yes |
| `Tableau/Intuitionistic/Scheme.lean` | 723 | `ILabelBound_extendMany` (private) | section var + `unusedDecidableInType` at 720 | Yes (this lemma) |

**Only `Minimal/Soundness:118` is explicitly named in the task description.** The two Intuitionistic
sites are not named in the description and live in files with task-317 sorries.

### Sites from the description that are already resolved / moot

- **Classical/Completeness (the bulk of the "14"):** DONE by task 460 — the file now carries ~24
  `omit` clauses and the commit message states "Scoped build now emits zero warnings." Verified: no
  Classical/Completeness unusedSectionVars remain.
- **Minimal/Completeness:89:** **No unusedSectionVars present** at line 89 in the current build. The
  line numbers have shifted (that region is now `minTruthLemma`/`minOpenBranch_countermodel` and
  `minimalTableau_complete`, which carries a `sorry` at ~line 104). Sorry-containing theorems do not
  trigger `unusedSectionVars`, so this site is currently silent.

### Critical sequencing insight (why part (c) is sequenced AFTER task 317)

The `unusedSectionVars` linter **skips theorems whose proof contains `sorry`** (it cannot determine
which section variables the eventual real proof will use). Several in-scope Tableau theorems still
have task-317 sorries (`Minimal/Completeness.lean:104` `minimalTableau_complete`,
`Intuitionistic/Completeness.lean:106`, `Intuitionistic/Scheme.lean` sorries, etc.). **When task 317
fills those sorries, new `unusedSectionVars` warnings will appear** and existing line numbers will
shift. This is exactly why the description sequences part (c) after 317.

### Recommended approach for part (c) at implement time

1. **Do NOT trust the description's line numbers** (they are already stale: Classical done,
   Minimal/Completeness:89 moot, Minimal/Soundness still at 118).
2. **Sequence after task 317** for the Minimal/Intuitionistic Completeness modules — running the
   sweep before 317 lands would both miss the soon-to-appear warnings and add churn that 317's
   proof-filling would relocate.
3. **Linter-driven sweep:** at implement time run
   `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness Cslib.Logics.Propositional.Tableau.Minimal.Completeness Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness 2>&1 | grep -i unusedSectionVars`
   (extend module list as needed), and add `omit [<Instance> …] in` immediately above each flagged
   declaration, matching the exact instance(s) the linter reports.
4. **Safe-now subset (independent of 317):** the sorry-free `minimalTableau_sound` at
   Minimal/Soundness:118 can be fixed immediately — insert `omit [Hashable Atom] in` on the line
   directly above `theorem minimalTableau_sound`. This mirrors the existing `omit [Hashable Atom] in`
   at Minimal/Soundness:62 and :172. (Optionally also Expansion:162 and Scheme:723, though those are
   not named in the task.)

### Exact edit for the one confirmed, safe-now site

`Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`, before line 118:

```lean
omit [Hashable Atom] in
theorem minimalTableau_sound (φ : Proposition Atom)
```

Note there is a second live warning at Minimal/Soundness:135:59 — `unusedSimpArgs`
(`List.zip_nil_left` is unused in a `simp only`). Not part of this task's scope (part (c) is
unusedSectionVars only), but flagging it in case the plan wants to fold it in.

---

## Part (d) — references.bib `NegriVonPlato2001` (CONFIRMED needed)

### Finding: entry missing, widely cited

- `grep -in "NegriVonPlato" references.bib` → **no entry**.
- The key `[NegriVonPlato2001]` is cited in **~21 files**, not just OrImpConservative. Confirmed
  citations include:
  - `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean:44`
  - `Cslib/Logics/Propositional/SequentCalculus/LJ/{Basic,Interpolation,Decidability,Completeness,SubformulaProperty,Soundness,CutElimination}.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/LK/{Basic,Interpolation,Decidability,Completeness,Soundness,CutFreeCompleteness,CutElimination,SubformulaProperty}.lean`
  - `Cslib/Logics/Propositional/SequentCalculus/Defs.lean:33`
- Citation text used consistently across files: `[S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001]`.

This is a genuinely-needed, fully-independent, safe addition.

### Validation / consumption

No dedicated bib-validation script exists in `scripts/` (contents: `bench`, `CheckInitImports.lean`,
`create-adaptation-pr.sh`, `gendocs.sh`, `nolints.json`, `pre-pr-check.sh`, `README.md`).
`references.bib` is consumed by doc-gen (`gendocs.sh`) to resolve `[Key]` markdown reference links,
so a missing key yields a broken doc link rather than a build/CI failure — but adding it is clearly
correct given 21 live citations.

### Exact BibTeX entry to add

Mirror the existing `@book{TroelstraSchwichtenberg2000, …}` format (the adjacent CUP proof-theory
reference). Append to `references.bib`:

```bibtex
@book{NegriVonPlato2001,
  author       = {Negri, Sara and von Plato, Jan},
  title        = {Structural Proof Theory},
  publisher    = {Cambridge University Press},
  year         = {2001},
  doi          = {10.1017/CBO9780511527340}
}
```

Notes:
- Authors: Sara Negri and Jan von Plato (matches "S. Negri, J. von Plato" in the citation text).
- DOI `10.1017/CBO9780511527340` is the CUP DOI for this book — **verify** during implementation
  (e.g. against a DOI resolver); if the plan prefers ISBN, the print ISBN is `978-0-521-79307-0`.
- Existing entries use either `doi` or `isbn`; either is acceptable per file conventions.

---

## Reuse Check (CSLib reuse-first)

- No new definitions or abstractions are introduced by this task. Part (a) reuses existing
  documented declarations; part (c) reuses the established `omit … in` idiom already present in the
  same files (Minimal/Soundness:62, :172; Classical/Completeness ×24); part (d) reuses the existing
  `references.bib` `@book` format. No Foundations/Mathlib abstraction search is applicable.

## Zero-Debt / Constraints

- No `sorry`, no new axioms, no vacuous definitions are involved. All residual edits are mechanical
  (one bib entry, one-to-few `omit` clauses, an optional rename). Part (c) must NOT touch the
  task-317 sorries themselves — only add `omit` clauses around already-sorry-free declarations.

## Recommended sequencing for the plan

1. **Now, independent & safe:**
   - Part (d): add `NegriVonPlato2001` to `references.bib`.
   - Part (c) safe subset: `omit [Hashable Atom] in` before `minimalTableau_sound`
     (Minimal/Soundness:118). Verify with a scoped build.
   - Part (a) optional: `fld`→`himpFold` rename only if task 395 still requires it.
2. **After task 317 lands:** run the linter-driven `unusedSectionVars` sweep across the
   Minimal/Intuitionistic Completeness modules and add `omit` clauses where the live linter points
   (line numbers to be taken from linter output, not from this report).
3. Verify: `lake build` (scoped to touched modules), then full `lake build`, `lake lint`,
   `lake exe checkInitImports`, `lake exe lint-style`.

## Files referenced (absolute paths)

- `/home/benjamin/Projects/cslib/Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean`
- `/home/benjamin/Projects/cslib/references.bib`
- `/home/benjamin/Projects/cslib/specs/460_vet_455_classical_lint_warnings/` (prior Classical lint cleanup)
