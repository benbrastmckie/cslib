# Research Report: Intuitionistic Modal Truth-Lemma Sorries (Task 533)

## Bottom Line

**The premise of this task is stale. There are no sorries to discharge.** The intuitionistic
modal grid (`Cslib/Logics/Modal/Metalogic/Intuitionistic/`) is **already fully sorry-free and
axiom-clean**. `TruthLemma.lean`, `Completeness.lean`, and the concrete logics
`IK`/`IT`/`IS4`/`IS5` all build successfully and depend only on the three standard Mathlib
axioms. No implementation work is required.

The task description asserts "`TruthLemma.lean` carries 3 active sorries." This is not the case
in the current tree. The truth lemma was completed by a prior task's Phase 3a/3b/3c work,
committed as:

- `58eb704a` — task 480 phase 3c: complete implementation
- `eb7a9c14` — task 480 phase 3b: complete implementation
- `f7c85a12` — task 480 phase 3a: complete

The task 533 description was evidently authored against a pre-`58eb704a` snapshot.

## Evidence

### 1. No `sorry` / `admit` / `sorryAx` tokens

```
grep -rn "\bsorry\b|\badmit\b|sorryAx" Cslib/Logics/Modal/  →  no code hits
```

The only matches anywhere in the Modal tree are the strings `sorry-free` inside docstrings
(TruthLemma.lean lines 29, 152, 305) and the English word "admit" in unrelated `Constructive/CS5*`
docstrings. There are **zero** `sorry` tactic occurrences and **zero** `axiom` declarations in
the entire `Intuitionistic/` directory.

### 2. Successful build

```
lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK \
           Cslib.Logics.Modal.Metalogic.Intuitionistic.IT \
           Cslib.Logics.Modal.Metalogic.Intuitionistic.IS4 \
           Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5
→ Build completed successfully (602 jobs). EXIT: 0
```

These four modules transitively pull in `TruthLemma.lean`, `Completeness.lean`, `CanonicalModel.lean`,
`PrimeTheory.lean`, `Extension.lean`, and `Birelational.lean`. Only non-fatal style-linter
suggestions (`linter.flexible`) were emitted — no errors, no sorry warnings.

### 3. Axiom check via `lean_verify` (authoritative)

Every load-bearing theorem depends on **only** `[propext, Classical.choice, Quot.sound]` — the
standard classical Mathlib footprint — with **no `sorryAx` and no custom axioms**:

| Theorem | Axioms | sorryAx? |
|---|---|---|
| `Cslib.Logic.Modal.canonical_truth_lemma` | propext, Classical.choice, Quot.sound | no |
| `Cslib.Logic.Modal.ivalid_completeness` | propext, Classical.choice, Quot.sound | no |
| `Cslib.Logic.Modal.mvalid_completeness` | propext, Classical.choice, Quot.sound | no |
| `Cslib.Logic.Modal.ik_completeness` | propext, Classical.choice, Quot.sound | no |
| `Cslib.Logic.Modal.is5_completeness` | propext, Classical.choice, Quot.sound | no |

This is the strongest possible confirmation: `lean_verify` inspects the actual kernel-checked
axiom dependency graph. A `sorry` anywhere in the transitive proof would surface `sorryAx` here.
It does not.

## What the Truth Lemma Actually Rests On

The parametric design means "the truth lemma rests on unproven obligations" is a misreading of
the architecture, not a real gap:

- `canonical_truth_lemma` (TruthLemma.lean:465) takes the modal axiom schemata
  (`h_K`, `h_Kdia`, `h_Idb`, `h_Cd`, `h_dbot`) plus the intuitionistic base as **loose hypothesis
  parameters**, never global `axiom`s. It dispatches the seven `Proposition` constructors to the
  seven fully-proven case helpers (`truth_atom_case` … `truth_diamond_case`), all sorry-free.
- `ivalid_completeness` / `mvalid_completeness` (Completeness.lean:187/263) discharge those
  parameters by structural argument (`modal_prime_exclusion`, `canonical_bot_not_mem`, the
  consistent/inconsistent case split), again with no sorries.
- The concrete logics discharge the schemata against their concrete axiom sets:
  `ik_completeness` instantiates `ivalid_completeness` at `IKModalAxiom`; `it`/`is4`/`is5`
  instantiate the frame-conditioned generalization `ivalidFC_completeness` (Extension.lean:97)
  at `ITModalAxiom`/`IS4ModalAxiom`/`IS5ModalAxiom` with their respective `FC` predicates. Each
  also proves `*_consistent` and packages `*_soundness_completeness`.

This matches the classical cube's structure — the intuitionistic grid is closed.

## Reuse-First / Zero-Debt Notes

- No new definitions or abstractions are needed (nothing to build). The existing
  `CanonicalModel` / `PrimeTheory` / `Extension` / `Birelational` infrastructure is fully wired.
- Zero-debt policy is already satisfied: zero sorries, zero new axioms, standard axiom footprint.

## Recommendation

**No implementation phase should be dispatched.** Recommended dispositions, in order of
preference:

1. **Close the task** (mark `[COMPLETED]` / `[ABANDONED]` with a note) on the grounds that its
   objective — "intuitionistic modal grid fully sorry-free" — is already met by the current tree.
   A completion summary should record that the deliverable was satisfied by prior task-480 work
   (commits `f7c85a12` → `58eb704a`) and independently re-verified here.
2. If the user wants a durable guardrail instead of closing, the only *net-new* work that would
   make sense is a **CI regression guard** (e.g. an `#print axioms` / `lake`-level check, or a
   test asserting the completeness theorems carry no `sorryAx`) so a future edit cannot silently
   reintroduce a gap. This is a *new* deliverable, not part of the stated task, and should be
   confirmed with the user before creating it.

Because the task premise does not hold, an automated plan → implement pass would either be a
no-op or would invent scope. This report flags the situation for user review rather than
proceeding.

## Verification Commands (reproducible)

```bash
grep -rn "\bsorry\b" Cslib/Logics/Modal/Metalogic/Intuitionistic/   # → docstring-only
lake build Cslib.Logics.Modal.Metalogic.Intuitionistic.IK \
  Cslib.Logics.Modal.Metalogic.Intuitionistic.IT \
  Cslib.Logics.Modal.Metalogic.Intuitionistic.IS4 \
  Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5   # → success (602 jobs)
# lean_verify on ivalid_completeness/mvalid_completeness/canonical_truth_lemma/ik/is5 → clean
```
