# Continuation Handoff 04: `CS5Combined` Canonical-Model Scaffold Landed, Seed-Exclusion Still Open

## State at end of this dispatch

- Phases 1-2: landed, committed, CI-green (unchanged).
- Phase 3 (`cs5Combined_seed_excludes`): still `[PARTIAL]`, not `[BLOCKED]`. Per handoff 03's
  strategic reframe (agreed by all three prior dispatches: stop searching for a standalone
  "cheap gate"; build the full `CS5Combined` canonical model directly, mirroring
  `CS5Segment`/`cs5Mreach`), this dispatch ported `CS5.lean`'s entire canonical-model
  construction to `CS5Combined` over the doubled atom space `Atom ⊕ Atom`. This is real,
  substantial, sorry-free, axiom-clean progress, but it does **not** close
  `cs5Combined_seed_excludes` itself — see "What remains open" below for why, and for the
  concrete next-step recommendation this dispatch identifies.
- Phases 4-5: not started (both consume Phase 3's full closure, which has not been reached).

## What was landed (all sorry-free; `lean_verify`/`#print axioms` show only
`propext`/`Classical.choice`/`Quot.sound`, several structural facts show no axioms at all)

All in `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`, appended after the
necessity-transfer section (commit "task 512 phase 3: land CS5Combined canonical-model
scaffold + symmetric-tail-gap finding"):

1. **Reuse audit (the key enabling finding this dispatch made before writing any code):**
   confirmed by reading signatures that almost all of `CS5.lean`'s canonical-model plumbing is
   **already generic over an arbitrary axiom predicate `Axioms : Proposition Atom → Prop`**, not
   hardcoded to `CS5ModalAxiom`: `mem_head_mp`/`mem_of_axiom` (`CKTruthLemma.lean:57/64`),
   `box_mem_of_boxed_context`/`quasi_prime_exclusion`/`box_refuting_theory`
   (`SegmentLindenbaum.lean:109/73/177`), `list_split_union`/`bigAnd`/
   `bigAnd_mem_of_forall_mem`/`derivImpBigAndOfAppend` (`SegmentLindenbaum.lean:300/336/342/419`
   — `list_split_union`/`bigAnd` don't even depend on an axiom system, purely list-theoretic),
   `modal_deriv_imp_of_union`/`modalDeductiveClosure_closed`/`modal_subset_deductive_closure`
   (`PrimeTheory.lean:173/127/84`), `Metalogic.prime_set_exclusion`, `CKSegment`/`cmreach`/
   `QuasiPrime` (`Segment.lean`, fully generic), and `cs5FC''` itself (`CKExtension.lean:184`,
   generic over any `World`/relation). This means porting `CS5.lean`'s CS5-specific layer to
   `CS5Combined` is a **direct mechanical substitution** (`CS5ModalAxiom.X` → `CS5Combined.base
   (.X)`, `Atom` → `Atom ⊕ Atom`), not new mathematics — confirmed by the port going through
   cleanly with zero proof-strategy changes needed, only syntactic substitution.
2. **The ported canonical-model layer** (mirrors `CS5.lean` lines ~612-1244 exactly):
   `cs5Combined_box_four`, `cs5Combined_boxInv_subset`, `cs5CombinedTail` (def) +
   `cs5CombinedTail_refl`/`_symm`/`_trans`, `cs5Combined_symmetric_tail_box_gap` (see finding
   below), `cs5Combined_dia_bot_imp_bot`, the private `bigOr`/box combinatorics
   (`cs5Combined_box_mono`, `cs5Combined_or_box_imp_box_bigOr`,
   `cs5Combined_dia_or_box_imp_bigOr`, `cs5Combined_extract_box_list`,
   `cs5Combined_quasiPrime_bigOr_mem`), `cs5Combined_quasi_prime_set_exclusion` (private clone of
   `quasi_prime_set_exclusion`), and `cs5Combined_diam_witness` (the diamond-witness theorem for
   the combined symmetric tail).
3. **The `CS5Combined` world type**: `cs5CombinedSeg`, `CS5CombinedSegment` (structure),
   `cs5CombinedMreach`, `CS5CombinedSegment.ofHead`, `cs5Combined_refl`/`_trans`/`_symm`.
4. **The frame-condition proof**: `cs5Combined_fcsymbox_theory`, `cs5Combined_fc4_theory` (the
   two theory-level obligations), their segment lifts `cs5Combined_fcsymbox`/`cs5Combined_fc4`,
   and the capstone `cs5CombinedFC''_cs5CombinedMreach : cs5FC'' (@cs5CombinedMreach Atom)` — the
   combined canonical model satisfies the same weakened frame condition `CS5.lean`'s own model
   does.
5. **Key structural finding** (mechanized, not just argued): `cs5Combined_symmetric_tail_box_gap`
   is a direct port of `cs5_symmetric_tail_box_gap` (`CS5.lean:712`). Its proof uses *only*
   primality of a tail member `T` and the two tail clauses (`hsub`/`hsym`) — no
   `CS5ModalAxiom`-specific fact, per that theorem's own docstring ("no `CS5` axiom... applies to
   every symmetric-tail design"). Since `cs5CombinedTail` has the identical two-clause shape,
   the SAME proof ports verbatim (confirmed by actually landing it, not just asserting it).
   **Consequence**: a fully general `cs5Combined` truth lemma — one covering *arbitrary*
   `CS5Combined`-quasi-prime heads `H`, the way a real "completeness of `CS5Combined`" theorem
   would need — faces the identical box-backward gap that `CS5` itself has. Building
   `CS5Combined`'s own general completeness is therefore **not easier** than closing `CS5`'s
   box-backward case directly; the reframe does not purchase a shortcut at the "cover all
   worlds" level.
6. Lint hygiene: this dispatch also renamed six pre-existing `def`s in this file
   (`cs5_lift_toDerivationTree_L`/`_R`/`_collapse` → `cs5LiftToDerivationTreeL`/`R`/`Collapse`,
   `cs5Combined_impTrans` → `cs5CombinedImpTrans`, `cs5Combined_boxL_imp_boxR`/`_boxR_imp_boxL` →
   `cs5CombinedBoxLImpBoxR`/`cs5CombinedBoxRImpBoxL`) after `lake lint` (run for the first time
   on this file this dispatch, not previously run — environment linters are not in PR CI and
   were not part of prior dispatches' verification commands) flagged them as
   `defsWithUnderscore` violations. No external references existed (grep-confirmed), so this was
   a safe, contained rename. `lake lint` now reports zero warnings for `CS5Canonical.lean`.

## What remains open, and why the reframe alone does not close it

`cs5Combined_seed_excludes` needs a **specific** designated-pair existence claim: a
`CS5Combined`-quasi-prime `H+ ⊇ τL '' H` (the seed) that omits both `τR A` and `τL(□A)`. This is
NOT the same as needing the *general* truth lemma for `CS5Combined` (which finding 5 above shows
is exactly as hard as `CS5`'s own open problem). Two observations from this dispatch's analysis
(not yet mechanized — recorded here for the next dispatch):

1. **Why "just build the designated world in the new canonical model" is still circular as
   stated**: the natural candidate designated pair is `(H, HR)` with
   `HR := modalDeductiveClosure CS5ModalAxiom (boxInv H)` (already landed, satisfies both
   cross-conditions and `A ∉ HR`, per the Phase-3 Step-1 facts in this file). The obstacle
   remains exactly what report 02 identified: `HR` is not prime, and extending it to a prime `T`
   while preserving `boxInv T ⊆ H` needs either (a) `prime_set_exclusion` with `DerivExcludes`
   at the seed — which IS `cs5Combined_seed_excludes` itself, circular — or (b) a directly-built
   witness, which is exactly Phase 4's pair-recovery problem.
2. **A concrete, NOT-yet-tried lead worth investigating first next dispatch (the "cluster"
   idea)**: rather than a *single* R-witness world, build the semantic soundness argument using
   **all** prime extensions of `HR` as a cluster of R-worlds, all mutually accessible (S5
   equivalence class) and all accessible from a single L-designated world `w0` with head `H`.
   The single-formula `prime_exclusion`/`quasi_prime_exclusion` (already generic, landed) gives,
   for any `B ∉ HR`, a prime extension of `HR` omitting `B` — this is exactly the contrapositive
   needed to validate the semantic `crossRL` condition (`∀ B, (∀ T ∈ cluster, B ∈ T) → B ∈ H`)
   **without** needing `cs5Combined_seed_excludes` as an input, ONLY needing `HR ⊆ H` (already
   landed) and the basic single-formula Lindenbaum lemma. The open technical work is: (i)
   defining the full two-sorted valuation at every world in `{w0} ∪ cluster` (not just the
   designated formulas), (ii) proving `CS5Combined`-soundness of the base 17 axioms plus
   `crossLR`/`crossRL` over this specific frame shape, and (iii) checking that the compound-
   formula truth lemma for the *propositional* connectives goes through using ordinary
   quasi-primality (disjunction property) — which does NOT require negation-completeness (this
   dispatch's re-reading of the standard canonical-model argument suggests Pacheco's flaw
   (Lemma 16/18) was specifically about deriving NON-membership facts compositionally, not the
   ordinary membership-preserving induction every quasi-prime canonical model already uses; this
   should be double-checked carefully before relying on it). This is a genuinely new avenue, not
   on the "confirmed dead ends" list (that list covers single-witness models and homomorphic
   translations, not a genuine multi-world cluster construction) — but it is a substantial new
   soundness proof, not a quick close, and was NOT attempted in Lean this dispatch (analysis
   only, to leave a scoped, concrete next step rather than a vague "try semantics again").

## Prohibited workarounds

No `sorry`, no `def _ := True`/vacuous placeholder was introduced for `cs5Combined_seed_excludes`
or any other obligation this dispatch — confirmed absent via grep across the touched file.

## Files touched this dispatch

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — added the full
  `CS5Combined` canonical-model scaffold (~520 new lines) plus the six lint-driven renames.
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md` — Phase 3
  progress note appended.
- `specs/512_cs5_box_backward_atom_sum_completeness/handoffs/04_canonical-model-scaffold.md`
  (this file).

## Verification commands (all run this dispatch, all green)

```bash
cd ~/Projects/cslib
lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical   # green, no warnings
lake build                                                          # full project green
lake exe checkInitImports                                           # clean
lake exe lint-style Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean  # clean
lake lint 2>&1 | grep CS5Canonical                                  # clean (after renames)
grep -n "\bsorry\b" Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean  # none (only prose)
grep -n "^axiom " Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean    # none
# lean_verify on cs5CombinedFC''_cs5CombinedMreach, cs5Combined_diam_witness,
# cs5Combined_fc4_theory -> propext, Classical.choice, Quot.sound (clean)
# lean_verify on cs5CombinedTail_trans, cs5Combined_symmetric_tail_box_gap -> clean/no axioms
```

`lake test` was NOT re-run this dispatch (no test-suite-relevant behavior changed; the module
adds pure theorems/defs with no new test surface). Recommend the next dispatch runs the full
7-step pipeline (including `lake test`, `lake shake`) once Phase 3 is closer to resolution, since
running it mid-scaffold on an intermediate state adds little signal.

## Next dispatch instructions

1. Read this handoff in full (and handoff 03 for the algebraic-route dead-end confirmations)
   before writing any code.
2. Do NOT re-attempt: the necessitation/K/cross-axiom algebraic route; any homomorphic/
   compositional atom-substitution translation; any atom-indexed (mirrored/L-uniform/naive
   2-point/naive-identify-both) semantic model; or a fully general `cs5Combined` truth lemma
   attempt aimed at covering arbitrary heads (finding 5 above proves this is not easier than the
   original problem).
3. Attempt the "cluster" semantic lead described above ("What remains open", point 2) as the
   most promising untried avenue: build the multi-world R-side cluster (all prime extensions of
   `HR`), prove `CS5Combined`-soundness over that specific frame shape (reusing
   `cs5_axiom_sound''`'s style for the 17 base cases, two new cases for `crossLR`/`crossRL` using
   the single-formula Lindenbaum contrapositive), and read off `cs5Combined_seed_excludes` from
   soundness (NOT completeness) at the designated world. Budget: this is a substantial new
   soundness proof (likely 150-300 lines), not a quick fix — scope accordingly.
4. Alternatively, if the cluster idea proves as hard as feared, the derivation-height induction
   (report 02 §5) remains the other pre-identified route, now with the full `CS5Combined`
   canonical-model scaffold (this dispatch's landed work) available as supporting infrastructure
   should the induction need to construct canonical worlds directly.
5. Zero-debt holds throughout: no `sorry`, no new axiom. If exhausted again, land whatever
   builds green, update this handoff, and keep Phase 3 `[PARTIAL]` (not `[BLOCKED]` unless a
   genuine obstruction is PROVED — still assessed as unlikely per report 02's confidence figures
   and four dispatches' worth of failed leak-finding attempts, which is itself weak evidence
   against a collapse).
