# Implementation Summary: CK Soundness + Completeness (Task 493)

- **Task**: 493 — CK (constructive modal logic K) soundness + completeness
- **Plan**: plans/01_ck-segment-completeness.md (9 phases; Phase 4a contingency NOT triggered)
- **Status**: implemented — all phases complete, zero debt, CI green
- **Mode**: `--hard --lit` (H2/H3/H7/H9)
- **Session**: sess_1784011298_752245_493_impl

## What Was Built

Five new files under `Cslib/Logics/Modal/Metalogic/Constructive/` (1,331 lines), namespace
`Cslib.Logic.Modal`, all parametric over `Axioms` for task 501 reuse:

| File | Contents |
|------|----------|
| `Forcing.lean` (196) | `CKForces` (Wijesekera ∀∃-diamond forcing), simp lemmas, `ckforces_persistence` (no frame conditions), `CKValid` (explosion-conditioned fallible-model validity), `ckforces_of_exploding` (ianshil `Expl`) |
| `Segment.lean` (226) | `QuasiPrime` (= `PrimeAdmissible` at trivial `Cons`), `boxInv`/`diaInv`, `CKSegment` (head/tail + 4 constraints), `cexpl`, `CKSegment.ofHead` (maximal tail), `Preorder` (head ⊆), `cmreach`/`cval`/`cbotForces`, canonical explosion-condition lemmas |
| `SegmentLindenbaum.lean` (271) | `quasi_prime_exclusion` (Lindenbaum at trivial `Cons`), `box_mem_of_boxed_context` (closed-set K-lemma), `imp/box/dia_refuting_theory`, `quasi_head_realization`, `segment_realization` |
| `CKTruthLemma.lean` (211) | `mem_of_axiom`/`mem_head_mp` closure helpers, `diamRefutingSegment`, `ck_truth_lemma` (full induction, all 7 cases) |
| `CK.lean` (427) | `CKModalAxiom` (9 int-prop + Kb + Kd; no cd/idb/dbot), `ck_axiom_sound`/`ck_soundness`/`ck_soundness_derivable` (CKValid), `ck_completeness`, `ck_consistent`, `ck_soundness_completeness`; secondary `EValid` block (birelational soundness-only) |

Headline theorems:
- `ck_soundness_derivable : Derivable CKModalAxiom φ → CKValid φ`
- `ck_completeness : CKValid φ → Derivable CKModalAxiom φ`
- `ck_soundness_completeness : Derivable CKModalAxiom φ ↔ CKValid φ`
- `ck_consistent : ¬ Derivable CKModalAxiom ⊥`

## Plan Deviations

Two settled plan premises were mathematically false; both corrected with concrete
counterexamples and re-grounded against ianshil/CK `Kripke/kripke_sem.v` (fetched verbatim
via `gh api`). Full statement in the plan's "DESIGN CORRECTION" section.

1. **`ck_soundness : Derivable → MValid` is unprovable.** `efq` (`⊥ → p`) is refuted by
   `botForces ≡ True`, `val ≡ False` — `MValid` lacks the fallible-model explosion
   conditions (`val_expl`/`mreach_expl`/`ireach_expl` in ianshil). The research report's H4
   pass checked the `k`/`kdia`/non-modal cases but missed that `efq`'s proof
   (`hbot.elim`, IK.lean:144-146) depends on `botForces = False`.
2. **`ck_completeness : MValid → Derivable` is false; no `BForces`-based completeness is
   possible for bare CK.** `Cd = ◇(p∨q) → ◇p∨◇q` is `MValid` (the `∃`-diamond clause
   distributes over `∨` with no frame condition — see `ik_axiom_sound`'s `cd` case) and
   `Idb` is `MValid` via the baked-in `F2`; neither is CK-derivable. `BForces`+F1/F2
   semantically characterizes CK+Cd+Idb. Ground truth: ianshil's forcing uses the ∀∃
   diamond clause over frames with **no** confluence conditions.

   **Fix**: new `Forcing.lean` defines `CKForces` (∀∃ diamond) and `CKValid` (explosion
   conditions, no F1/F2) — the headline pair is stated over `CKValid`. All frozen files
   (Birelational.lean, Intuitionistic/*, PrimeExclusion.lean) byte-identical.

3. **File count**: 5 new files, not 4 (`Forcing.lean` added).
4. **Phase 5 (f1/f2 for the segment model) is obsolete**: `CKForces` persistence needs no
   frame conditions, and the raw segment model provably does not satisfy F1 (tails of
   head-comparable segments are unrelated) — consistent, since `CKValid` imposes none.
5. **Phase 4 needed no STOP/4a**: in the ianshil-faithful design, tails are set
   comprehensions (`ofHead`'s maximal tail; `diamRefutingSegment`'s restricted tail), so
   only single-theory prime extensions were required. `PrimeExclusion.lean` untouched.
6. **Soundness statement shape**: `ck_soundness` takes the explosion conditions as five
   loose hypotheses (v_uc, bf_uc, bf_val, bf_r, bf_r_wit) mirroring `ik_soundness`'s loose
   `r`/`f1`/`f2` style.
7. **`EValid` retained as a documented secondary result**: CK is sound (not complete) for
   the birelational `∃`-clause semantics with explosion conditions; useful for relating the
   task-490 layer to the constructive layer, and documents why `MValid` was abandoned.

## Verification

- `lake build` (full): green (only pre-existing task-317 sorry warning in
  `Propositional/Tableau/Minimal/Completeness.lean`, outside this task).
- `lake test`: green. `lake exe checkInitImports`: green. `lake exe lint-style`: green.
  `lake exe mk_all --check`: "No update necessary" (Cslib.lean wired).
- `lake lint`: one pre-existing failure in frozen `PrimeExclusion.lean:324`
  (`unusedArguments` on `DerivExcludes` `_D`) — task-480 file, read-only mandate, not
  introduced by 493; zero findings in `Constructive/`.
- `lake shake`: informational only (commented out in `.github/workflows/lean_action_ci.yml`);
  its `Cslib.Init`-removal suggestions conflict with the enforced `checkInitImports` policy.
- `lean_verify`: `ck_completeness`, `ck_soundness_completeness`, `ck_consistent`,
  `ck_truth_lemma` depend only on `propext`/`Classical.choice`/`Quot.sound`;
  `ck_soundness_derivable` is axiom-free.
- Zero `sorry`/`admit`/`axiom`/`native_decide`/vacuous definitions in the 5 new files.
- UNTOUCHED gates: `git diff` empty for `Intuitionistic/`, `Semantics/`, `Foundations/`.

## Commits

- `7cb14f24` phase 1: CKModalAxiom
- `e8c2e34e` phase 3: EValid + BForces soundness (later demoted to secondary)
- `a4f1a1e9` phase 2: Forcing.lean + Segment.lean (design correction)
- `fbdb4359` phase 4: SegmentLindenbaum.lean
- `f1a3e037` phases 6-7: CKTruthLemma.lean
- (phase 8 commit) CK.lean completeness capstone
- `6c65155d` phase 9: Cslib.lean wiring + full CI

## Downstream Notes (Task 501)

- `CKSegment`, the refuting theories, `diamRefutingSegment`, and `ck_truth_lemma` are all
  `Axioms`-parametric; CT/CS4/CS5 add constructors + frame-class hypotheses on `cmreach`.
- 501 must extend `CKValid` with frame-class parameters (ianshil `ClassF`); the euclidean
  concern for CS5 flagged in the plan still stands.
- If a future task wants bare-CK-vs-birelational bridges, the lemma
  `BForces ↔ CKForces` on F1-frames is straightforward (not needed here, not proved).
