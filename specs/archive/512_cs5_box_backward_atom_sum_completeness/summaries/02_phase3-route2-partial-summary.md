# Implementation Summary: Task #512 — Phase 3 Route-2 (Partial Progress)

- **Task**: 512 - cs5_box_backward_atom_sum_completeness
- **Status**: [PARTIAL] — Phases 1-2 remain landed (unchanged). Phase 3 advanced with real,
  sorry-free progress but the core obligation (`cs5Combined_seed_excludes`) is not yet fully
  closed. Phases 4-5 not attempted.
- **Plan**: `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md`
- **Research input**: `reports/02_phase3-seed-consistency.md` (route-2 recommendation).
- **Continuation handoff**: `handoffs/02_phase3-route2-continuation.md` (full technical detail).
- **Phases completed**: 2 of 5 (unchanged). Phase 3 `[PARTIAL]` (was `[BLOCKED]`, now has real
  landed progress and is not a proved obstruction); Phases 4-5 `[NOT STARTED]`.

## What Landed This Dispatch

All in `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` unless noted; all sorry-free,
`#print axioms` clean (only `propext`/`Quot.sound`/`Classical.choice`).

1. **`Proposition.map_id` / `Proposition.map_map`** (`Cslib/Logics/Modal/Basic.lean`): general
   functoriality facts for the atom-relabeling map (identity and composition), needed by the
   collapse projection below.
2. **`cs5Collapse` / `τ0`**: the atom-collapse `ProofSigHom` erasing the `τL`/`τR` tagging via
   `Sum.elim id id`. Both `crossLR`/`crossRL` collapse onto the SAME `CS5ModalAxiom.tBox`
   instance, so `τ0` reuses the exact `Deriv.map`/`ProofSigHom` machinery `τL`/`τR` already use —
   a new instance of an existing pattern, not new infrastructure.
3. **`cs5_lift_deriv_collapse`, `cs5_collapse_of_L_deriv`, `exists_preimage_list_of_forall_mem_image`,
   `cs5Combined_collapse_mem_L`**: the transport chain taking a `τL`-tagged `CS5Combined`-derivation
   from `τL '' H` down to a bare `CS5ModalAxiom`-derivation from `H`.
4. **`cs5Combined_bot_excluded`, `cs5Combined_boxA_excluded`**: using (3), these FULLY discharge
   two of the four seed-exclusion sub-obligations — `⊥` and `τL(□A)` provably cannot leak into
   `modalDeductiveClosure CS5Combined (τL '' H)`.
5. **`cs5Combined_boxInv_subset_HR`, `cs5Combined_HR_subset_H`, `cs5Combined_boxInv_HR_subset_H`,
   `cs5Combined_A_notMem_HR`**: the four `HR`-seed-pair facts (`HR := modalDeductiveClosure
   CS5ModalAxiom (boxInv H)`), a direct mechanical port of the sorry-free `cs5_pair_seed_mem`
   probe (report 02's "Step 1"). Reusable as-is by Phase 4's pair recovery.
6. **`cs5Combined_boxL_imp_boxR`, `cs5Combined_boxR_imp_boxL`**: `⊢ □(τL B) ↔ □(τR B)` for every
   `B`, the syntactic form of report 02's "crossRL-conservativity" lever, via necessitation + `K`
   + axiom `4`. Landed as a standalone verified lemma for the next dispatch to build on.

## What Remains Open

The obligation `cs5Combined_seed_excludes` needs, in addition to items 4 above:

- **`τR A` excluded** from the closure (the genuinely hard case).
- **The mixed `bigOr {τL(□A), τR A}` disjunction case.**

Both reduce (mechanically) to: for all `Ψ ∈ H`, `⊬_{CS5Combined} τL(Ψ) → τR(A)` (an empty-context
combined theorem question). This dispatch confirmed — independently of report 02, via an
explicit semantic countermodel argument (see the continuation handoff) — that no single
compositional/homomorphic translation can witness this, matching report 02 §5's general
impossibility result. A bespoke, non-homomorphic derivation-induction invariant (report 02's
"single hard node", ~150-220 estimated lines) is still required and was not completed. One
promising, unexplored lead — the "necessity transfer" conjecture `⊢CS5Combined τLΨ→τRA ⟹ ⊢CS5
Ψ→□A` — is documented in the continuation handoff as the recommended next attempt.

## Plan Deviations

- Phase 3 status changed from `[BLOCKED]` to `[PARTIAL]`: this dispatch does NOT claim a proved
  obstruction (the claim is still believed true, ~85-90% per report 02), so `[BLOCKED]` (which
  the plan reserves for the negative-result/obstruction pivot) is no longer the accurate marker;
  `[PARTIAL]` (interrupted, real progress, not yet complete) is used instead.
- Phases 4-5 remain not attempted — both consume Phase 3's full closure (`cs5Combined_seed_excludes`
  as a hypothesis), which is still open.
- No deviation in the landed lemmas: all new declarations follow the report-02 route-2 skeleton
  (Step 1 mechanical port, plus the collapse-projection tool the report's §5 anticipates as
  "the naive collapse, sharpened").

## Files Touched

- `Cslib/Logics/Modal/Basic.lean` — `Proposition.map_id`, `Proposition.map_map`.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — collapse projection, two
  fully-discharged exclusion obligations, `HR`-seed-pair facts, box-equivalence lemmas.
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md` — Phase 3
  heading and resumed-dispatch progress note.
- `specs/512_cs5_box_backward_atom_sum_completeness/handoffs/02_phase3-route2-continuation.md`
  (new) — full technical continuation handoff.

## Verification

- `lake build` (full project): green.
- `lake test`: green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: only the pre-existing project-wide
  "remove `import Cslib.Init`" false-positive (contradicts `checkInitImports`'s mandate; not
  acted on, matching existing convention for every other file in the library).
- Zero new `sorry` (verified via `grep -n "\bsorry\b"` on both touched files — only a
  "sorry-free" docstring mention, no actual tactic).
- No new `axiom` declaration.
- `#print axioms` on all seven new top-level lemmas: only `propext`/`Quot.sound`/
  `Classical.choice`.

## Next Steps (for the next dispatch)

1. Read `handoffs/02_phase3-route2-continuation.md` in full before writing any code.
2. Attempt the "necessity transfer" conjecture first (documented in the handoff) — highest
   expected value per effort if it goes through.
3. If that fails, attempt the full derivation-height induction on `CS5Combined`
   `DerivationTree`/`Deriv` report 02 §5 describes (budget ~150-220 novel lines).
4. Do not re-attempt the confirmed-dead-end routes listed in the handoff.
5. Phases 4-5 remain fully specified template-clone work in the plan file once Phase 3 lands.
