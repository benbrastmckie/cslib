# Task 416 — Research: Instantiate GenericLindenbaum (Phase 6)

**Task type**: cslib (consolidation / activation of dormant substrate)
**Status**: research — no Lean source modified
**Date**: 2026-06-29
**Source premise**: specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md §5, Rank 1
**Overlap**: task 393 (Zulip-first umbrella) — see §6

---

## 1. Headline Finding — The Named Debt Is Already Closed

**Task 416's core deliverable was already implemented by task 407 phase 6** (commit
`9242d243`, "task 407 phase 6: re-instantiate Min*/Int* on generic substrate; unify
bot_forces"). That commit is in `main` and is an ancestor of current HEAD `07792009`
(verified with `git merge-base --is-ancestor 9242d243 HEAD` → YES).

The commit message and the live source agree exactly with what task 416 asks for:

> MinLindenbaum.lean / IntLindenbaum.lean:
> - Import GenericLindenbaum; replace duplicated proof bodies with generic calls
> - min_deriv_from_closure_to_S → generic_deriv_from_closure_to_S (1 line)
> - min_deriv_imp_of_union → generic_deriv_imp_of_union (1 line)
> - int_deriv_from_closure_to_S → generic_deriv_from_closure_to_S (1 line)
> - int_deriv_imp_of_union → generic_deriv_imp_of_union (1 line)
> - min_imp_witness → generic_imp_witness with Cons=fun _ => True (trivial h_cons_ext)
> - int_imp_witness → generic_imp_witness with EFQ h_cons_ext + intDeductiveClosure_consistent
> Net: ~101 line reduction in Metalogic/ (170 deleted, 69 added)

The substrate `GenericLindenbaum.lean` is **NOT dormant**. Both Lindenbaum files import it
and delegate to it (verified by grep — only these two files import it, and they are the only
non-substrate references to the `generic_*` lemmas):

| Lemma (Min) | File:line | Body |
|---|---|---|
| `min_deriv_from_closure_to_S` | MinLindenbaum.lean:83-91 | one-line `generic_deriv_from_closure_to_S MinPropAxiom.mem_implyK …` |
| `min_deriv_imp_of_union` | MinLindenbaum.lean:99-107 | one-line `generic_deriv_imp_of_union …` |
| `min_imp_witness` | MinLindenbaum.lean:138-150 | `generic_imp_witness (Cons := fun _ => True)` + `h_cons_ext := fun _ _ => trivial` |
| `int_deriv_from_closure_to_S` | IntLindenbaum.lean:100-108 | one-line `generic_deriv_from_closure_to_S IntPropAxiom.…` |
| `int_deriv_imp_of_union` | IntLindenbaum.lean:116-124 | one-line `generic_deriv_imp_of_union …` |
| `int_imp_witness` | IntLindenbaum.lean:170-198 | `generic_imp_witness (Cons := PropSetConsistent IntPropAxiom)` + EFQ `h_cons_ext` |

The `h_cons_ext` explosion parameter is wired exactly as the substrate designed it:
`fun _ _ => trivial` for minimal, EFQ + `intDeductiveClosure_consistent` for intuitionistic.

## 2. Why the 415 Audit Reported It As Open

The 415 audit (Finding 3, "CONFIRMED ... additive, unused") was driven by the **stale
docstring** in `GenericLindenbaum.lean:43-52`, which still reads:

> "This file is **additive**: `MinLindenbaum.lean` and `IntLindenbaum.lean` are not
> modified. Re-instantiation of `MinTheory`/`IntDCCS` off this substrate is deferred to
> Phase 6 of the MPL-base structure-first redesign (task 407)."

That paragraph was written in the substrate's introduction commit (`e26b0b4f`, phase 5,
"additive") and was **never updated** when phase 6 (`9242d243`) actually performed the
re-instantiation. The audit's §5 line counts (Min 247 / Int 318) are the *current* sizes —
the audit assumed those whole files were duplicates, but they already delegate. This is a
documentation-vs-code drift, not a real consolidation gap.

## 3. Current CI / Debt State (verified)

- `lake build Cslib.…MinLindenbaum Cslib.…IntLindenbaum` → **"Build completed successfully
  (727 jobs)."**
- `grep sorry|admit|native_decide` across all three files → **NONE**.
- `grep '^axiom'` → **NONE**.
- Zero-debt policy: already satisfied; nothing to add.

## 4. The One In-Scope, Zero-Risk Deliverable: Fix the Stale Docstring

The only genuinely actionable, in-scope, zero-risk item is updating the now-false
"Design Notes" paragraph in `GenericLindenbaum.lean:45-52` so it states the substrate is
**active** (instantiated by `MinTheory`'s `min_*` and `IntDCCS`'s `int_*` Lindenbaum lemmas),
not "additive / deferred to Phase 6". This is a doc-only edit:

- No proof obligation, no behavior change, no new sorry/axiom.
- Docstrings already exist (no docBlame risk); pure prose replacement.
- Suggested replacement content: note that re-instantiation was completed in task 407 phase 6,
  list the two consumer files, and keep the explosion-parameterization explanation (which is
  still accurate and valuable).

This honestly "closes" task 416: the code debt is gone; only the doc claim lingers.

## 5. Residual Micro-Duplication (OUT OF SCOPE — hand to 393)

A second, smaller layer of duplication remains but is **NOT** the named debt and **touches
task-393 territory**. Min/Int still each define their own deductive-closure scaffolding that is
*definitionally equal* to the generic versions (IntLindenbaum.lean:195 explicitly notes
"`GenericDeductiveClosure IntPropAxiom = intDeductiveClosure` definitionally"):

| Min decl | Int decl | Generic equivalent |
|---|---|---|
| `minDeductiveClosure` (MinLindenbaum:112) | `intDeductiveClosure` (IntLindenbaum:129) | `GenericDeductiveClosure Axioms` (GenericLindenbaum:93) |
| `min_subset_deductive_closure` (:118) | `int_subset_deductive_closure` (:135) | `generic_subset_deductive_closure` (:215) |
| `minDeductiveClosure_is_theory` (:125) | `intDeductiveClosure_dccs_closed` (:142) | `genericDeductiveClosure_closed` / `_is_theory` (:224/:238) |

**Why this is out of scope:**

1. These named defs are **public downstream API**, not internal bodies. Consumers:
   - `minDeductiveClosure` → `MinStrongCompleteness.lean`
   - `intDeductiveClosure` → `IntStrongCompleteness.lean`, **`IntDecidability.lean`**
   Collapsing them means rewriting those three files to use
   `GenericDeductiveClosure (Min|Int)PropAxiom`. `IntDecidability.lean` and the two
   StrongCompleteness files are exactly the modules task 393's scope (a)/(b) governs, and the
   task-416 description says *"coordinate, do NOT double-edit the same decls."*
2. `MinTheory` / `IntDCCS` themselves must **stay** as named predicates (downstream references
   them by name across 5 files); they are not candidates for collapse into
   `GenericTheory _ (fun _ => True)`.
3. Net win is small (~6 decls / ~40 lines) and carries definitional-unfolding risk in the
   prime-exclusion wrappers (`min_prime_exclusion`/`int_prime_exclusion` pass the closure op as
   a positional argument to `Metalogic.prime_exclusion`).

Recommendation: leave this to task 393's umbrella consolidation; do not pursue under 416.

## 6. Coordination with Task 393

Confirmed sibling relationship (consistent with 415 §5 "Overlap with task 393"): 393 owns the
algebraic/quotient-Lindenbaum + Classical-completeness axis and the StrongCompleteness /
IntDecidability files. The deductive-closure Min/Int Lindenbaum slice that 416 targets is
already consolidated; the only residue (§5) lives in 393's files. There is **no remaining
non-393 work** beyond the doc fix of §4.

## 7. Recommendation to the Planner / Orchestrator

**Recommended disposition: close task 416 as substantively already-satisfied (by 407 phase 6),
with a single doc-only phase.**

- **Phase 1 (only phase, S, zero-risk):** Rewrite `GenericLindenbaum.lean:45-52` "Design Notes"
  to reflect that the substrate is active and instantiated (task 407 phase 6), naming the two
  consumer files. Re-run `lake build` on `GenericLindenbaum`, `MinLindenbaum`, `IntLindenbaum`
  + the full CI quartet (`lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake`). No proof changes, so CI risk is nil.

Do **not** manufacture the §5 closure-def dedup under this task — it is 393's territory and
carries non-zero risk for a ~40-line gain.

If the orchestrator policy requires task 416 to produce a *code-consolidation* deliverable
rather than a doc fix, the honest move is to **mark 416 [COMPLETED] citing 9242d243** (the named
debt is closed) and fold the §5 residue into task 393's plan — not to re-do already-landed work.

---

## Appendix — Verification Method

All claims verified by Read of the three source files, `git log`/`git show --stat` on
`9242d243`, `git merge-base --is-ancestor` for ancestry, repo-wide `grep` for imports/usages,
and a scoped `lake build` (727 jobs, success). No lean-lsp goal/hover calls were required: every
claim is a definition/commit/build fact readable directly. No Lean source was modified.
