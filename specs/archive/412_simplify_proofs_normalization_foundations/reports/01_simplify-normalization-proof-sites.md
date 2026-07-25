# Research Report: Simplify Proofs over Task-268 Normalization Lemmas

**Task:** 412 — Simplify proofs in `Foundations/Logic/` that use manual `simp only [...]` /
verbose tactic chains over the normalization lemmas, replacing with `grind`/`simp` where the
`@[simp, scoped grind =]` co-tags make explicit lemma lists redundant.

**Session:** sess_1784866674_c9da04_412 (orchestrator mode)

## Executive Summary

- The two co-tag source files still exist at the stated paths and carry the expected
  `@[simp, scoped grind =]` co-tags: `Cslib/Foundations/Logic/Metalogic/ListImplication.lean`
  (`listImp_nil`, `listImp_cons`) and `Cslib/Foundations/Logic/Theorems/BigConj.lean`
  (`bigconj_nil`, `bigconj_singleton`, `bigconj_cons_cons`, `negBigconj_def`).
- **The task's central premise is largely already satisfied.** A repo-wide grep finds
  **zero** verbose multi-lemma `simp only [listImp_nil, listImp_cons, bigconj_*, ...]` lists.
  Every remaining call site is already a **single-lemma** `simp only [X]` (22 sites total).
  The verbose redundancy this task targets appears to have already been removed — most
  plausibly by the completed hygiene pass (task 321, now archived) together with the co-tagging
  that introduced these lemmas.
- **Remaining opportunities are modest tactic-collapse polish, not lemma-list pruning.** The
  realistic, empirically-confirmed wins collapse 2–3-line `simp only [...] ; exact <deriv>`
  chains into a single `grind` (or `grind [<lemma>]` / `simpa`). These are optional style
  improvements with low reward.
- **SEQUENCING BLOCKER:** the depended-on task 41 (`abstract_completeness_infrastructure`) is
  **`not_started`**. Task 41 is precisely the completeness-infra abstraction that will most
  likely relocate `GenericMCS.lean` / `MCSProperties.lean` and the MCS-bridge machinery — the
  same files that hold most candidate sites. Proceeding now risks the exact "re-sweeping moved
  code" the task description warns against. Recommend deferring, or narrowing scope (below).
- **Zero-debt / lint:** every candidate is a proof-body tactic swap inside existing
  declarations; no new declarations, no docstrings, no `sorry`, no axioms. GenericMCS.lean is
  `sorry`-free (a stray `declaration uses sorry` line in a scratch `lean_multi_attempt` was a
  broken-snippet cascade artifact, not a real sorry — confirmed by grep).

## Dependency & Location Audit (orchestrator ask)

| Dep | Name | state.json status | Location / note |
|-----|------|-------------------|-----------------|
| 41 | abstract_completeness_infrastructure | **not_started** | UNMET. Will likely move Foundations/Logic/Metalogic completeness files. |
| 321 | code_hygiene_logics_foundations | **completed** (archived: `specs/archive/321_code_hygiene_logics_foundations`) | Satisfied. Likely already collapsed the verbose lists this task anticipated. |
| 278 | parent (split source) | expanded | 412 was split from here. |

Source files confirmed at stated paths (no relocation yet):
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` — `listImp` + co-tagged
  `listImp_nil` (L51), `listImp_cons` (L54).
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` — `bigconj`/`negBigconj` + co-tagged
  `bigconj_nil` (L72), `bigconj_singleton` (L76), `bigconj_cons_cons` (L79), `negBigconj_def` (L87).

Note: `Cslib/Logics/Temporal/Syntax/BigConj.lean` is a **different** (type-specific)
`bigconj`/`negBigconj` on `Formula Atom`; it is not governed by the generic co-tags and is out
of scope.

## Full Call-Site Inventory (22 sites)

The scoped-grind namespaces (`Cslib.Logic.Metalogic.ListImplication`, `...BigConj`) are `open`ed
in ListDeduction / MCSProperties / GenericMCS and inside BigConj's own namespace, so the
`scoped grind =` equations are active at these sites (verified via `open` lines).

### In-scope: `Foundations/Logic/`

| File:line | Current | Assessment |
|-----------|---------|------------|
| `Theorems/BigConj.lean:111-113` | `simp only [bigconj_singleton] at hconj; simp only [List.mem_singleton] at hmem; rw [hmem]; exact hconj` | **CONFIRMED collapse → `grind`** (closes all 3 lines; also `simp_all`). |
| `Theorems/BigConj.lean:115` | `simp only [bigconj_cons_cons] at hconj` (feeds manual `ModusPonens.mp lce_imp/rce_imp` + `ih`) | Keep as normalization; grind can't supply the derivability combinators cleanly. |
| `Theorems/BigConj.lean:128` | `simp only [bigconj_nil]` then `exact identity ⊥` | Keep (grind lacks `identity`); marginal. |
| `Theorems/BigConj.lean:133` | `simp only [bigconj_singleton]` then `exact h a (by simp)` | Keep; low value. |
| `Theorems/BigConj.lean:136` | `simp only [bigconj_cons_cons]` (feeds `pairing`/`ModusPonens`) | Keep as normalization. |
| `Metalogic/MCSProperties.lean:110` | `unfold ListDeriv; simp only [listImp_nil]; exact h_ax` | **Collapse → `unfold ListDeriv; grind`** (analogous to L125). |
| `Metalogic/MCSProperties.lean:125` | `unfold ListDeriv; simp only [listImp_nil]; exact h_thm` | **CONFIRMED → `unfold ListDeriv; grind`** or `simpa only [listImp_nil, ListDeriv] using h_thm`. |
| `Metalogic/ListDeduction.lean:77-78` | `simp only [listImp_cons]; exact listImp_axiom_k φ Ψ` | **CONFIRMED → `grind [listImp_axiom_k]`** (2 lines → 1). Debatable value vs explicit `exact`. |
| `Metalogic/ListDeduction.lean:82-83` | `simp only [listImp_cons]; exact ModusPonens.mp HasAxiomImplyK.implyK ih'` | Likely `grind [HasAxiomImplyK.implyK]` with `ih'` in context; **needs verification**. |
| `Metalogic/GenericMCS.lean:242` | `\| [], d, _ => by simpa only [listImp_nil] using d` (term-mode match arm) | Already minimal/idiomatic; leave. Not line-testable via `lean_multi_attempt`. |
| `Metalogic/GenericMCS.lean:244` | `simp only [listImp_cons] at d` (feeds recursive `HilbertTree.mp`) | Keep as normalization. |

### Out of stated scope: `Logics/` MCS bridges (same lemmas, different directory)

The task title says "proofs in `Foundations/Logic/`". These 12 sites live under `Logics/` and
are downstream *consumers*, not `Foundations/Logic/`:

- `Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean:191,192,197,198,203,206`
- `Logics/Modal/Metalogic/GenericMCSBridge.lean:142,146`
- `Logics/Temporal/Metalogic/GenericMCSBridge.lean:171,172,177,180`

Pattern is uniformly `unfold ListDeriv[ at ih]; simp only [listImp_nil][ at ih]; exact ih`,
collapsible to `unfold ListDeriv[ at ih]; grind`. **Recommend excluding** unless the orchestrator
explicitly widens scope — and note these are prime task-41 relocation candidates.

## Empirical Verification (`lean_multi_attempt`)

Ran non-destructive tactic attempts at representative sites:

1. `BigConj.lean:111` — `grind` → **no goals** (closes the whole singleton branch; follow-on
   lines report "No goals to be solved", i.e. they must be deleted). `simp_all` also works.
2. `MCSProperties.lean:125` — bare `grind` **fails** (can't see through `ListDeriv` to `h_thm`);
   `unfold ListDeriv; grind` **works**; `simpa only [listImp_nil, ListDeriv] using h_thm` **works**.
3. `ListDeduction.lean:77` — bare `grind` **fails**; `grind [listImp_axiom_k]` **works**;
   `exact listImp_axiom_k φ Ψ` (after the existing `simp only`) works.

**Implementation caveat:** every successful `grind` collapse leaves the *following* tactic lines
as dead code ("No goals to be solved"). Each rewrite is a **multi-line deletion**, not a
one-line swap. The implementer must remove the now-redundant `exact …` / `simp only …` / `rw …`
lines, then re-verify with `lake build`.

## Reuse-First Check

No new abstraction is warranted or proposed. The relevant abstractions already exist and are
correctly co-tagged (`@[simp, scoped grind =]`). `negBigconj_def` has **no** proof-body
consumers (only docstring mentions), so it offers no simplification target. This task is purely
proof-body polish over existing, reused infrastructure.

## Recommendations (priority order)

1. **Resolve sequencing first.** Task 41 (`not_started`) is an unmet, code-moving dependency
   over the same files. Recommend the orchestrator either (a) hold 412 until 41 lands, or
   (b) **narrow 412** to the two files task 41 is least likely to relocate:
   `Theorems/BigConj.lean` and `Metalogic/ListDeduction.lean` (stable syntactic infra), and
   defer all `GenericMCS`/`MCSProperties`/MCS-bridge sites until after 41.
2. **Recalibrate expectations.** The "verbose manual lemma list" premise is stale — those lists
   no longer exist. Frame the plan around the ~3–4 confirmed tactic-collapse edits, not a broad
   sweep. Reward is low; this may be a candidate for `[ABANDONED]` / fold-into-41 rather than a
   standalone implementation cycle.
3. **If implementing, do the high-confidence collapses only:**
   - `BigConj.lean:111-113` → `grind` (delete the 2 follow-on lines).
   - `MCSProperties.lean:110` and `:125` → `unfold ListDeriv; grind` (delete `exact` lines).
   - `ListDeduction.lean:77-78` and `:82-83` → `grind [<axiom lemma>]` (verify `:82` first).
   - Leave normalization-then-manual-MP sites (`BigConj:115,136`, `GenericMCS:244`) and the
     already-minimal `GenericMCS:242` untouched.
4. **Verification gate (must pass):** `lake build`, `lake test`, `lake exe checkInitImports`,
   `lake exe lint-style`, `lake shake`. No lint categories are implicated (no new decls).
5. **No sorry / no axioms.** All edits are total tactic swaps inside proven declarations; the
   zero-debt gate is trivially satisfied.

## Open Questions for Planner/User

- Should `Logics/*/GenericMCSBridge.lean` sites be in scope (task says `Foundations/Logic/`)?
- Given the stale premise and unmet task-41 dependency, is a standalone 412 still worthwhile, or
  should it be merged into task 41's refactor or abandoned?
