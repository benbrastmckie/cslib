# Implementation Plan: Task #389 — Docstrings, Headers, Citations (Prop/Foundations Tier-2)

- **Task**: 389 - Fix docBlame, barrel headers, unusedSectionVars, broken citation
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: Task 317 (planned) — required ONLY for the deferred post-317 Completeness `omit` sweep, which is explicitly out-of-scope for this plan. None of the in-scope phases below depend on 317.
- **Research Inputs**: reports/01_docstrings-headers-citations.md
- **Artifacts**: plans/01_docstrings-headers-citations.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Research (report 01) verified against the live codebase that **most of task 389's originally-scoped
work is already complete**: part (a) docstrings were added by task 406 (docBlame already satisfied),
part (b) barrels were verified present and correctly DROPPED, and the bulk of part (c)
(Classical/Completeness `unusedSectionVars`) was completed and committed by task 460. Only a small
residual remains: add one missing BibTeX entry (part d) and add one confirmed, sorry-free `omit`
clause (part c safe subset), plus optional cosmetic work. The definition of done is: the residual
mechanical edits land, CI is green, zero new sorries/axioms are introduced, and the deferred post-317
`unusedSectionVars` sweep is clearly recorded as follow-up rather than blocking 389.

### Research Integration

- **Part (d)** — `NegriVonPlato2001` is confirmed missing from `references.bib` yet cited by ~21
  files (OrImpConservative + SequentCalculus LJ/LK). Independent, safe. Report gives the exact
  entry mirroring the adjacent `TroelstraSchwichtenberg2000` `@book` format (verified present at
  references.bib:858). DOI `10.1017/CBO9780511527340` to be verified at implement time.
- **Part (c) safe-now** — `minimalTableau_sound` at `Minimal/Soundness.lean:118` is sorry-free and
  emits a live `linter.unusedSectionVars` for `[Hashable Atom]`. Add `omit [Hashable Atom] in`
  directly above it, mirroring the existing `omit [Hashable Atom] in` idiom at Soundness:62/:172.
  Optionally extend to the two other live sites (Intuitionistic/Expansion.lean, Intuitionistic/
  Scheme.lean) — but drive those from **live linter output**, not description/report line numbers.
- **Part (c) deferred** — the Minimal/Intuitionistic **Completeness** `omit` sweep must wait for
  task 317, because `unusedSectionVars` skips sorry-containing theorems; running it now would miss
  soon-to-appear warnings and churn line numbers. Out-of-scope for this plan (see Non-Goals).
- **Part (a) optional** — `fld`→`himpFold` rename has **zero lint value** (already lint-compliant,
  self-contained to one file). Included as an optional low-priority phase; safe to drop.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` provided; ROADMAP.md not consulted. Task topic is "Code Hygiene".

## Goals & Non-Goals

**Goals**:
- Add the `NegriVonPlato2001` `@book` entry to `references.bib` (part d).
- Add `omit [Hashable Atom] in` above `minimalTableau_sound` in `Minimal/Soundness.lean` (part c
  safe-now subset), plus any additional **currently-live** sorry-free `unusedSectionVars` sites the
  linter flags at implement time.
- Verify the full CI pipeline stays green with zero new sorries/axioms.

**Non-Goals**:
- The post-317 Minimal/Intuitionistic **Completeness** `unusedSectionVars` sweep. This is DEFERRED
  as a follow-up (gated on task 317 landing) and MUST NOT block completion of 389.
- Editing or filling any task-317 `sorry`. Part (c) only adds `omit` clauses around already
  sorry-free declarations.
- The `Minimal/Soundness:135:59` `unusedSimpArgs` warning (part (c) is `unusedSectionVars` only).
- Re-doing parts (a) docstrings, (b) barrels, or Classical/Completeness (c) — already complete.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| DOI `10.1017/CBO9780511527340` is wrong | L | L | Verify against a DOI resolver at implement time; fall back to ISBN `978-0-521-79307-0` per file conventions (both `doi` and `isbn` are used in references.bib). |
| Description/report line numbers are stale | M | M | Do NOT trust line numbers; locate `theorem minimalTableau_sound` by name, and drive extra (c) sites from live `lake build ... | grep -i unusedSectionVars` output. |
| Adding `omit` to a sorry-containing theorem (linter would not have fired) | M | L | Only add `omit` where the live linter actually reports `unusedSectionVars`; the linter never fires on sorry-containing theorems, so grep-driven edits are self-limiting. |
| Touching a 317 WIP region | M | L | Working tree is clean (report-verified); restrict edits to the named sorry-free declarations only. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel (each touches a distinct file with no overlap:
Phase 1 → `references.bib`, Phase 2 → `Tableau/Minimal/Soundness.lean` (+ optionally two
Intuitionistic files), Phase 3 → `Foundations/.../FreeMeetExtension.lean`).

### Phase 1: Add NegriVonPlato2001 to references.bib [COMPLETED]

**Goal**: Resolve the ~21 broken `[NegriVonPlato2001]` doc-gen citation links by adding the missing
`@book` entry (part d).

**Tasks**:
- [ ] Verify DOI `10.1017/CBO9780511527340` resolves to Negri & von Plato, *Structural Proof
      Theory*, CUP 2001 (or substitute ISBN `978-0-521-79307-0` if the DOI cannot be confirmed).
- [ ] Append the entry to `references.bib`, mirroring the adjacent `TroelstraSchwichtenberg2000`
      `@book` field layout (aligned `author`/`title`/`publisher`/`year`/`doi`):
      ```bibtex
      @book{NegriVonPlato2001,
        author       = {Negri, Sara and von Plato, Jan},
        title        = {Structural Proof Theory},
        publisher    = {Cambridge University Press},
        year         = {2001},
        doi          = {10.1017/CBO9780511527340}
      }
      ```
- [ ] Confirm the key is unique (`grep -n "NegriVonPlato" references.bib` shows exactly the new
      entry).

**Timing**: 15 min

**Depends on**: none

**Files to modify**:
- `references.bib` — append one `@book{NegriVonPlato2001, ...}` entry.

**Verification**:
- `grep -n "NegriVonPlato2001" references.bib` returns the new entry.
- No build impact expected (references.bib is consumed by doc-gen, not the Lean build).

---

### Phase 2: Add omit clause(s) for live unusedSectionVars (part c safe subset) [COMPLETED]

**Goal**: Silence the confirmed sorry-free `linter.unusedSectionVars` warning on
`minimalTableau_sound`, plus any other currently-live sorry-free sites, without touching 317 sorries.

**Tasks**:
- [x] Locate `theorem minimalTableau_sound` by name in
      `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` (do NOT rely on line 118).
- [x] Insert `omit [Hashable Atom] in` above the `theorem minimalTableau_sound` declaration
      *(altered: placed before the docstring, not between docstring and theorem — matches the
      existing idiom at Soundness:62 exactly; placing `omit` after the docstring is a parse error)*.
- [x] Run the linter-driven probe:
      `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme 2>&1 | grep -i unusedSectionVars`
- [x] For each **remaining live, sorry-free** site the linter reports: added
      `omit [Hashable Atom] in` above `intStepBranch_result_ne_notApplicable` in
      Intuitionistic/Expansion.lean, and extended the existing `omit [Hashable Atom] in` at
      Intuitionistic/Scheme.lean:720 to `omit [Hashable Atom] [DecidableEq Atom] in` above
      `ILabelBound_extendMany` (linter also flagged `[DecidableEq Atom]` there, resolving the
      companion `unusedDecidableInType` warning as a side effect).
- [x] Did NOT add `omit` to any Completeness module or any sorry-containing theorem (deferred).

**Timing**: 20 min

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` — add `omit [Hashable Atom] in` above
  `minimalTableau_sound` (confirmed).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — only if the linter flags it
  live (sorry-free).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — only if the linter flags it
  live (sorry-free).

**Verification**:
- Scoped rebuild of the touched modules reports **zero** `unusedSectionVars` for the edited
  declarations.
- No new errors/warnings introduced; no `sorry`/`axiom` added.

---

### Phase 3: OPTIONAL — fld → himpFold rename (part a, low priority) [ABANDONED]

**Goal**: Cosmetic naming reconciliation requested by task 395. Zero lint value — safe to DROP if
not desired.

**Tasks**:
- [x] Decide whether task 395's naming reconciliation still wants this rename. *(deviation:
      abandoned — delegation scope marks this phase optional/droppable, zero lint value, and
      purely cosmetic; skipped to keep the change surface minimal per the explicit
      "do only if cheap; droppable" instruction. `fld` occurs 26x in the file, `himpFold` is
      unused elsewhere — rename remains available as a future task-395 cosmetic follow-up.)*
- [ ] If proceeding: `replace_all` `fld` → `himpFold` … *(deviation: skipped — phase abandoned)*
- [ ] Rebuild `Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension` to confirm.
      *(deviation: skipped — phase abandoned)*

**Timing**: 15 min (or 0 if dropped)

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` — single-file `replace_all` (only
  if proceeding).

**Verification**:
- `Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension` builds clean; no external references
  break (grep confirms `fld` had no external users).

---

### Phase 4: CI verification and zero-debt check [COMPLETED]

**Goal**: Confirm the full pipeline is green and no new sorries/axioms were introduced.

**Tasks**:
- [x] `lake build` (full) — 3188 jobs, succeeded.
- [x] `lake exe checkInitImports` — clean, no output.
- [x] `lake exe lint-style` — clean, no output.
- [x] `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness Cslib.Logics.Propositional.Tableau.Minimal.Completeness Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness 2>&1 | grep -i unusedSectionVars`
      — zero matches; edited sorry-free sites silenced. Completeness-module sorry-containing
      theorems still emit no unusedSectionVars (linter skips them, as expected pre-317).
- [x] Zero-debt check: `git diff` on the 4 touched files introduces no `sorry` and no `axiom`.
      Additionally ran `lake lint` (scoped grep on touched files: clean), `lake test` (no failures),
      `lake exe mk_all --module` (no update necessary), and `lake shake` (pre-existing repo-wide
      import-hygiene debt noted across dozens of unrelated files including
      Intuitionistic/Expansion.lean's "add" suggestion; verified this is not caused by the one-line
      `omit` edit — out of scope for 389, consistent with ongoing separate shake-cleanup tasks
      457/458/460).

**Timing**: 15 min

**Depends on**: 1, 2, 3

**Files to modify**: none (verification only).

**Verification**:
- All four CI commands succeed.
- Edited declarations no longer emit `unusedSectionVars`.
- `git diff` shows zero new `sorry`/`axiom`.

## Testing & Validation

- [ ] `grep -n "NegriVonPlato2001" references.bib` shows the new entry (unique key).
- [ ] `lake build` (full) succeeds.
- [ ] `lake exe checkInitImports` succeeds.
- [ ] `lake exe lint-style` succeeds.
- [ ] `unusedSectionVars` grep confirms edited sorry-free sites are silenced.
- [ ] No new `sorry` or `axiom` in the diff.

## Artifacts & Outputs

- `plans/01_docstrings-headers-citations.md` (this plan)
- `references.bib` (part d entry)
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` (part c omit)
- Optionally `Cslib/Logics/Propositional/Tableau/Intuitionistic/{Expansion,Scheme}.lean` (part c,
  linter-driven) and `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` (part a rename)
- `summaries/01_docstrings-headers-citations-summary.md` (on implementation)
- Follow-up (out-of-scope, gated on task 317): Minimal/Intuitionistic Completeness
  `unusedSectionVars` sweep.

## Rollback/Contingency

- All edits are mechanical and isolated. To revert: `git checkout -- references.bib
  Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` (and any other touched files).
- If the DOI cannot be verified, substitute the ISBN in the `@book` entry rather than blocking.
- If a scoped rebuild reveals a site is not actually sorry-free / the linter does not fire, skip that
  `omit` edit — it belongs to the deferred post-317 sweep.
