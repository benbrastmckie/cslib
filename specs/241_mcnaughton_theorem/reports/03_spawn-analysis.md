# Blocker Analysis: Task #241

**Parent Task**: #241 - mcnaughton_theorem (cslib / Lean 4)
**Generated**: 2026-06-30
**Blocker**: The forward inclusion lemma `buchiCongr_DMA_language_forward` (language na ⊆ language (buchiCongr_DMA na)) has overflowed a single agent dispatch three times with zero committed proof, even after prerequisite infrastructure (tasks 428 and 429) is fully committed. The proof assembly itself is too large for one dispatch and must be split into individually committable named sub-lemmas.

## Root Cause

**Category**: Scope creep — a single proof obligation is too large for one implementation dispatch.

Prerequisite blockers are fully resolved: tasks 428 (monoid + idempotent/absorption lemmas: `buchiCongruence_instMonoid`, `buchiCongruence_mk_append`, `buchiCongruence_idempotentPow`, `buchiCongruence_absorption`) and 429 (`buchiCongruence_recurrentPrefixClass` + `buchiCongr_recurrentClass`) are committed, green, and archived. Their lemmas are live in `BuchiCongruence.lean` and `OmegaRegularLanguage.lean`.

Despite this complete API being present, two fresh full-resource dispatches at `buchiCongr_DMA_language_forward` overflowed — one hit the output-token limit, one hit a "prompt too long" context limit — producing zero committed Lean code. A sorry-stub currently sits at ~line 435 of `OmegaRegularLanguage.lean`.

The forward direction proof requires assembling several non-trivial steps in sequence:
1. A Ramsey/recurrence argument: for any `xs ∈ language na`, use `buchiCongr_recurrentClass` to extract idempotent/absorbing classes `a, b` that land in `infOcc` of the DMA run, then use `buchiFamily_saturation` to conclude `(buchiFamily (a,b) ⊓ language na).Nonempty` — this is the hardest conceptual step.
2. Connecting that conclusion to the DMA's accept set definition `{S | ∃ b ∈ S, ∃ a, ((buchiFamily (a,b) ⊓ language na).toSet).Nonempty}` — requires unfolding `DA.Muller language` (DA/Basic.lean:117) and matching `infOcc((buchiCongr_DMA na).run xs)` against the accept set, using `buchiCongr_DMA_run_eq`.

Each of these steps involves enough case analysis and term construction to fill a dispatch on its own. Monolithic assembly has been confirmed infeasible after three overflow failures.

The backward direction (`buchiCongr_DMA_language_backward`: language (buchiCongr_DMA na) ⊆ language na) and the final combination step are smaller but also need to be isolated as committed milestones so that work can accumulate without context overflow.

## Proposed New Tasks

### New Task 1: Prove accept-membership Ramsey lemma for buchiCongr_DMA forward direction (SUB-A)
- **Effort**: 2-3 hours
- **Task Type**: cslib
- **Rationale**: This is the hardest and largest single proof step in the forward inclusion. It establishes that for any `xs ∈ language na`, the set `infOcc((buchiCongr_DMA na).run xs)` contains a Büchi-family class `b` witnessing `∃ a, (buchiFamily (a,b) ⊓ language na).Nonempty`. This is the core Ramsey/recurrence argument using `buchiCongr_recurrentClass` (gives idempotent `b`, absorbing `a`, with `a ∈ infOcc(run xs)`) + `buchiCongr_DMA_run_eq` (connects run states to congruence classes) + `buchiFamily_saturation` (gives the nonemptiness). Extracting this as a standalone private lemma (e.g. `buchiCongr_DMA_accept_mem`) makes it independently verifiable and dispatch-sized.
- **Files**: `Cslib/Computability/Languages/OmegaRegularLanguage.lean` (primary); `Cslib/Computability/Languages/Congruences/BuchiCongruence.lean` (for API reference, read-only unless a small helper is needed there)
- **Exact API**: `buchiCongr_recurrentClass` (OmegaRegularLanguage.lean, private); `buchiCongr_DMA_run_eq`; `buchiFamily_saturation` (BuchiCongruence.lean:181); `mem_buchiFamily` (BuchiCongruence.lean:107); `mem_infOcc` (InfOcc.lean:88); `frequently_in_finite_type` (InfOcc.lean:46)
- **CI**: `lake build`; `lean_verify` on the new lemma; zero sorries
- **Depends on**: None

### New Task 2: Replace sorry in buchiCongr_DMA_language_forward using SUB-A (SUB-B)
- **Effort**: 1-2 hours
- **Task Type**: cslib
- **Rationale**: Once the accept-membership lemma from SUB-A is available as a named lemma, the sorry-stub `buchiCongr_DMA_language_forward` (language na ⊆ language (buchiCongr_DMA na)) at ~line 435 of `OmegaRegularLanguage.lean` can be discharged by unfolding the `DA.Muller language` definition (language da xs ↔ (da.run xs).infOcc ∈ da.accept, DA/Basic.lean:117) and matching `infOcc((buchiCongr_DMA na).run xs)` against the accept set `{S | ∃ b ∈ S, ∃ a, ((buchiFamily (a,b) ⊓ language na).toSet).Nonempty}`. This step is blocked on SUB-A because the specific accept-membership witness it constructs (the `b` and `a` classes) is what gets substituted into the accept-set existential — the implementer needs to know exactly what SUB-A's lemma produces and in what form to use it here.
- **Files**: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`
- **Exact API**: The named lemma produced by SUB-A; `DA.Muller language` unfolding (DA/Basic.lean:117); accept set definition of `buchiCongr_DMA`
- **CI**: `lake build`; `lean_verify` on `buchiCongr_DMA_language_forward`; zero sorries
- **Depends on**: New Task 1 (SUB-A), because the forward proof applies SUB-A's lemma directly — the exact statement (variable names, implicit arguments, `∃` structure) determines how the unfolding step is written

### New Task 3: Prove backward inclusion buchiCongr_DMA_language_backward (SUB-C)
- **Effort**: 1-2 hours
- **Task Type**: cslib
- **Rationale**: The backward direction (language (buchiCongr_DMA na) ⊆ language na) is independent of SUB-A/B. It proceeds from accept-set membership: if `infOcc(run xs) ∈ accept`, there exists `b ∈ infOcc(run xs)` and `a` such that `(buchiFamily (a,b) ⊓ language na).Nonempty`, which directly gives a witness `ys ∈ language na`. The saturation argument then lifts that membership to `xs ∈ language na` via `buchiFamily_saturation`. This does not depend on the Ramsey/recurrence argument of SUB-A (which goes in the other direction), so it can be written in parallel with SUB-A and SUB-B.
- **Files**: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`
- **Exact API**: Accept set definition of `buchiCongr_DMA`; `buchiFamily_saturation` (BuchiCongruence.lean:181); `mem_buchiFamily` (BuchiCongruence.lean:107)
- **CI**: `lake build`; `lean_verify` on `buchiCongr_DMA_language_backward`; zero sorries
- **Depends on**: None

### New Task 4: Combine inclusions into buchiCongr_DMA_language_eq and close Phases 5-6 (SUB-D)
- **Effort**: 1-2 hours
- **Task Type**: cslib
- **Rationale**: Once both inclusions (SUB-B and SUB-C) are proven, `buchiCongr_DMA_language_eq` follows by `Set` / `ωLanguage` antisymmetry (le_antisymm). This unlocks: (a) wiring the `h_pkg` obligation in `to_da_muller_scaffold` (Phase 5 of the original plan); (b) closing `IsRegular.iff_da_muller` (~line 497 of OmegaRegularLanguage.lean, Phase 6); and (c) running the full CI pipeline to green. These three steps are small enough to group in one dispatch. This task depends on both SUB-B and SUB-C because the antisymmetry combination requires both `buchiCongr_DMA_language_forward` (from SUB-B) and `buchiCongr_DMA_language_backward` (from SUB-C) to be available with their exact types.
- **Files**: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`; any files touched in SUB-A/B/C that need docstrings or lint fixes
- **CI**: Full CSLib CI pipeline: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`; `lean_verify Cslib.ωLanguage.IsRegular.iff_da_muller`; zero sorries, zero new axioms
- **Depends on**: New Task 2 (SUB-B) and New Task 3 (SUB-C)

## Dependency Reasoning

- **Task 2 (SUB-B) depends on Task 1 (SUB-A)**: The forward-direction sorry-stub is discharged by applying SUB-A's accept-membership lemma. The exact form of that lemma (whether `b` is explicit or implicit, whether the nonemptiness is expressed as `Set.Nonempty` or `∃ x, x ∈ …`, how the infOcc membership is stated) determines how the unfolding step in SUB-B is written. The implementer of SUB-B cannot choose the correct unfolding tactics or existential witnesses without knowing the exact statement SUB-A committed.

- **Task 4 (SUB-D) depends on Task 2 (SUB-B)**: `buchiCongr_DMA_language_eq` requires `buchiCongr_DMA_language_forward` as a named theorem with its proven type — SUB-D directly applies `le_antisymm` (or `Set.Subset.antisymm`) to both inclusions.

- **Task 4 (SUB-D) depends on Task 3 (SUB-C)**: Same reason for the backward direction: `buchiCongr_DMA_language_backward` must be available as a named theorem for the antisymmetry combination.

- **Task 1 (SUB-A) and Task 3 (SUB-C) are independent**: They prove facts about opposite inclusions; SUB-A's Ramsey/recurrence argument (forward membership) shares no implementation decisions with SUB-C's accept-set unfolding (backward membership). Either can be done first.

## After Completion

Once all four spawned tasks are complete, resume the parent task #241 with `/implement 241`.

The blocker is resolved because: the three overflow failures all attempted to assemble the full forward proof in one dispatch; decomposing it into four single-dispatch lemmas (the hardest being SUB-A, which is now its own task) eliminates the overflow cause. Each sub-lemma is committable independently, so no dispatch need hold the entire proof in working context at once.
