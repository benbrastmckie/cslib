# Task 380 — Implementation Summary

## Result: COMPLETE (deliverable verified sound and sorry-free)

Proved the conservativity theorem `hilbertIplConservativeOverOrImp` for the
disjunctive-implicational fragment IPL⟨∨,→,⊤⟩ over its OrImp Hilbert system, via the
**proof-theoretic route** (LJ cut-elimination), and wired it into `ConservativeChain.lean`.
This is the route recommended by the task-380 research, which sidesteps the task-372 Phase-6
free-meet-completion NO-GO entirely.

## Files changed

- **New**: `Cslib/Logics/Propositional/Semantics/Algebra/OrImpConservative.lean` (255 lines)
  - `private lemma cutFreeLJ_toOrImp_aux` — structural induction over all 11 `LJProof`
    constructors. The and-bot-free invariant makes `botL`/`andL`/`andR` vacuous (via `hΓ`/`hC`)
    and `cut` vacuous (via `LJCutFree`, whose `cut` case is `False`, discharged by `hcf.elim`).
    Generalized over a list `L ⊇ Γ` to dissolve the Finset-`Ctx` ↔ List-`Deriv` plumbing.
  - `theorem cutFreeLJ_toOrImp` — public wrapper around the aux lemma.
  - `theorem hilbertIplConservativeOverOrImp` — public conservativity theorem. Signature is
    **`DecidableEq`-free** (parallel to `hilbertIplConservativeOverConjImp`); the required
    `DecidableEq Atom` is supplied inside the body via `letI : DecidableEq Atom := Classical.decEq Atom`.
    Routes: `hilbert_iff_lj.mp` → `LJProof.cutElim` → `cutFreeLJ_toOrImp`.
  - `theorem derivableOrImpOfDerivableInt` — subsumption (OrImp → MinProp → IntProp via `derivable_mono`).
  - `theorem hilbertIplConservativeOverOrImp_iff` — biconditional.
  - `theorem ipl_conservative_over_orImp` — ND corollary via `derivableInIplIffDerivableInt`.
- **Modified**: `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` (+16 lines)
  - `public import` of `OrImpConservative`.
  - `theorem orImpAxiom_iff_chain` — places IPL⟨∨,→,⊤⟩ ⊂ IPL on the chain (mirrors `conjImpAxiom_iff_chain`).
  - `theorem nd_chain_ipl_to_orImp` — ND-level chain corollary.
- **Modified**: `Cslib.lean` (+2 lines) — barrel regenerated via `lake exe mk_all --module`.

## Verification

- **Sorry-free, no new axioms** — confirmed by a fresh-kernel `#print axioms` (via `lake env lean`):
  - `cutFreeLJ_toOrImp` depends on `[propext, Classical.choice, Quot.sound]`
  - `hilbertIplConservativeOverOrImp` depends on `[propext, Classical.choice, Quot.sound]`
  - These are the three standard Mathlib axioms; `Classical.choice` is the deliberately-sanctioned
    `Classical.decEq` used to keep the public signature `DecidableEq`-free. **No `sorryAx`.**
  - (Note: the `lean_verify` MCP tool initially reported a spurious `sorryAx` due to a stale olean
    from an earlier non-compiling iteration of the file; the fresh kernel check is authoritative.)
- **Builds clean**: `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConservativeChain`
  succeeds (766 jobs, exit 0), transitively building the new file.
- **`lake exe lint-style`**: PASS (exit 0).
- **`Cslib.Init` import**: present (line 9).
- **Imports minimal/used**: `LJ.CutElimination`, `LJ.Completeness`, `ConjImpConservative`
  (`derivable_mono`), `HilbertConservativeGlivenko` (`derivableInIplIffDerivableInt`) — all
  directly referenced; compliant with `lake shake --keep-implied`.

## CI caveat — pre-existing branch breakage (NOT introduced by task 380)

The repo-wide CI gates (`lake build` full, `lake test`, `lake exe checkInitImports`, `lake shake`)
cannot run green on this branch because of **pre-existing failures unrelated to this task**, in:

- `Cslib/Logics/Bimodal/Metalogic/Separation/Duality.lean` (`simp made no progress`)
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean` (unsolved goals)
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Bridge.lean` (type mismatch)
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean`
- `Cslib/Logics/Modal/Tableau/Soundness.lean`
- plus long-standing `sorry`s in `Tableau/*` and `NaturalDeduction/Normalization/Termination.lean`

**Confirmed pre-existing**: stashing the task-380 code changes (`Cslib.lean`, `ConservativeChain.lean`)
and building `Bimodal.Metalogic.Separation.Duality` reproduces the identical failure at branch HEAD
(commit `ac18af0e`). None of the failing modules import the new `OrImpConservative` file, and the
task-380 changes are purely additive within the `Propositional` tree. These breakages should be
addressed as their own fix task(s); they are out of scope for task 380.

## Bottom line

The mathematical deliverable for task 380 is **complete, builds cleanly in isolation, is
kernel-verified sorry-free, and introduces no new axioms**. The only unmet hard-constraint item —
fully green repo-wide CI — is blocked exclusively by pre-existing, unrelated breakage in the
`Bimodal`/`Modal`/`Tableau` subtrees that predates this task.
