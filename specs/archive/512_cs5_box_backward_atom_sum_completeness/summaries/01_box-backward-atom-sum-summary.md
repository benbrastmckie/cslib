# Implementation Summary: Task #512 — CS5 Box-Backward via Doubled-Atom Combined System

- **Task**: 512 - cs5_box_backward_atom_sum_completeness
- **Status**: [PARTIAL] — Phases 1-2 landed sorry-free; Phase 3 (the go/no-go gate) genuinely
  blocked, documented, not forced.
- **Plan**: `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md`
- **Phases completed**: 2 of 5 (Phase 1, Phase 2). Phase 3 [BLOCKED]; Phases 4-5 not attempted
  (both depend on Phase 3's `cs5Combined_seed_excludes`).

## What Landed

### Phase 1 — `Proposition.map` (Cslib/Logics/Modal/Basic.lean)

- `Proposition.map (f : Atom → Atom') : Proposition Atom → Proposition Atom'` by structural
  recursion over all 7 constructors.
- `@[simp]` connective-commutation lemmas (`map_atom`, `map_bot`, `map_imp`, `map_and`, `map_or`,
  `map_box`, `map_diamond`), all `rfl`.
- `Proposition.map_injective`: `Proposition.map f` is injective whenever `f` is injective (proved
  via an auxiliary two-argument induction `Proposition.map_injective_aux`, since
  `Function.Injective`'s implicit binders do not generalize cleanly under `induction`).

Verified: `lake build` green; `#print axioms Proposition.map_injective` shows only `propext`.

### Phase 2 — `CS5Combined` + `τL`/`τR` transport (new file `CS5Canonical.lean`)

New file `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`, registered in `Cslib.lean`:

- `CS5Combined : Proposition (Atom ⊕ Atom) → Prop`: `base` (wraps all 17 `CS5ModalAxiom`
  constructors) plus `crossLR`/`crossRL` (the two cross-condition axioms internalizing
  `boxInv H' ⊆ T` / `boxInv T ⊆ H'`).
- `cs5_axiom_relabel`: `CS5ModalAxiom φ → CS5ModalAxiom (φ.map f)`, all 17 cases discharged
  definitionally via Phase 1's `rfl` commutation lemmas.
- `τL`/`τR : ProofSigHom (modalSig CS5ModalAxiom) (modalSig CS5Combined)`, built from
  `Proposition.map Sum.inl`/`Sum.inr`, reusing the task-419 `Metalogic.Deriv.map`/`ProofSigHom`
  machinery (`Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean`) and the Modal
  `modalSig`/`toDeriv`/`ofDeriv` bridge (`Cslib/Logics/Modal/Metalogic/InterSystem/
  LiftViaMorphism.lean`) — confirmed a corollary, not new infrastructure, as the research report
  predicted.
- `cs5_lift_toDerivationTree_L`/`_R` and `Deriv`-level wrappers `cs5_lift_deriv_L`/`_R`, via
  `ofDeriv (Metalogic.Deriv.map τL (toDeriv d))`.

Verified: `lake build` green; `#print axioms cs5_axiom_relabel` shows no axioms at all;
`#print axioms cs5_lift_deriv_L` shows only `propext`/`Quot.sound`.

### Full CI Pipeline (after Phases 1-2)

- `lake build` (full project): green.
- `lake test` (`CslibTests/`): green.
- `lake exe checkInitImports`: clean.
- `lake exe lint-style`: clean.
- `lake exe mk_all --module`: ran, `Cslib.lean` updated with the new module.
- `lake shake --add-public --keep-implied --keep-prefix`: clean for the touched files (the only
  suggestion for `CS5Canonical.lean` is "remove `import Cslib.Init`", the same pre-existing
  false-positive shake gives for every other file in the library — `Cslib.Init` is required by
  `checkInitImports`/project convention regardless).
- `sorry`/vacuous-definition/new-axiom sweep: zero introduced by this dispatch (121 pre-existing
  `sorry` hits and one pre-existing `:= trivial` match belong to unrelated files, unchanged by
  this task; axiom count unchanged — confirmed via `git diff` showing no added `axiom` lines).

## Phase 3 — Why It Is [BLOCKED], Not Forced

Phase 3's obligation, `cs5Combined_seed_excludes`, is the task's own designated go/no-go
adversarial gate. This dispatch invested substantial analysis (documented in full in the plan
file's Phase 3 section) before concluding it cannot be responsibly closed — in either direction —
within this session:

1. **Confirmed simplification**: `h_not : □A ∉ H` implies `H` is consistent (`⊥ ∉ H`), so the
   exploding-head case never needs separate handling in Phase 3/4.
2. **Two candidate semantic (route 1) constructions were checked and shown insufficient**: a
   "identify both copies" model (fails to refute `τR A` whenever `A ∈ H`, which is a live,
   consistent possibility given only `□A ∉ H`) and a naive 2-point discrete frame (fails to
   correctly track compound/boxed formula membership without already having the desired witness
   theory `T`, which is circular).
3. **The literal route-2 sketch (collapse-to-a-single-copy projection) was checked and shown too
   weak**: it only derives `H ⊢ A` from `τL''H ⊢ τR A`, which is not a contradiction (`A ∈ H` is
   consistent with `□A ∉ H`).
4. **No forced obstruction was written either**: my analysis suggests the seed-exclusion claim is
   most likely *true* (the cross axioms only transmit *boxed* content between the two tagged
   copies, mirroring genuine S5 cluster semantics where cluster-mates share box-formulas but can
   differ elsewhere) — so fabricating a "proved obstruction" theorem would very likely be
   asserting a false statement, which is strictly worse than an honest partial result. Per the
   escalation protocol, no `sorry` and no vacuous placeholder were introduced for this obligation.

A genuine discharge of Phase 3 needs either (a) a correctly-specified separating model at
canonical-model scale (not a hand-built toy frame — the plan's own route-1 sketch under-specifies
how the companion world's valuation is pinned down without circularity), or (b) a new
proof-theoretic logical-relation/invariant lemma by induction on `CS5Combined`-derivation
structure, tracking exactly which combined formulas are derivable from the pure-`τL`-tagged seed.
Both are novel proof developments comparable in scope to `CS5.lean`'s own ~150-line soundness
apparatus, not mechanical clones like Phases 2/4/5. Full detail, including the four specific
findings above, is recorded in the plan file's Phase 3 `BLOCKER` annotation for the next dispatch.

## Plan Deviations

- Phase 3 is marked `[BLOCKED]` per the Escalation Protocol rather than `[NOT STARTED]`, since
  substantial (if inconclusive) investigatory work was done and is recorded as a blocker
  annotation, not merely skipped.
- Phases 4-5 were not attempted (deviation: deferred — both consume Phase 3's
  `cs5Combined_seed_excludes` as a direct hypothesis and cannot be meaningfully started before it
  lands).
- No deviation within Phases 1-2: both landed exactly as planned, using the exact reused-asset
  names from the research report (`Metalogic.Deriv.map`, `ProofSigHom`, `modalSig`/`toDeriv`/
  `ofDeriv`).

## Files Touched

- `Cslib/Logics/Modal/Basic.lean` — `Proposition.map` + commutation + injectivity (Phase 1).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` (new) — `CS5Combined`,
  `cs5_axiom_relabel`, `τL`/`τR`, transport corollaries (Phase 2).
- `Cslib.lean` — registered the new module (`lake exe mk_all --module`).
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md` — phase
  status markers updated; Phase 3 blocker fully documented.

## Verification

- `#print axioms Cslib.Logic.Modal.Proposition.map_injective` → `propext` only.
- `#print axioms Cslib.Logic.Modal.cs5_axiom_relabel` → no axioms.
- `#print axioms Cslib.Logic.Modal.cs5_lift_deriv_L` → `propext`, `Quot.sound` only.
- Zero `sorry` in either touched file (verified via `grep`).
- No new `axiom` declaration anywhere in `Cslib/` (verified via `git diff`).
- Full CI pipeline (`lake build`, `lake test`, `checkInitImports`, `lint-style`, `mk_all`, `shake`)
  green.

## Next Steps (for the next dispatch)

1. Read the Phase 3 `BLOCKER` annotation in the plan file in full before starting.
2. Decide between route (a) canonical-scale semantic model or route (b) a derivation-induction
   logical-relation lemma; the report's original 2-point-frame sketch is confirmed insufficient
   and should not be retried as-is.
3. If a genuine, rigorous obstruction (sort-collapse) is found instead, that is still an acceptable
   outcome per the original plan — but this dispatch's analysis leans toward the claim being true,
   not false, so a real effort at proving it should come first.
4. Phases 4-5 are template-clone work (`quasi_prime_set_exclusion`, `ck_truth_lemma`) once Phase 3
   lands; both remain fully specified in the plan file, unchanged.
