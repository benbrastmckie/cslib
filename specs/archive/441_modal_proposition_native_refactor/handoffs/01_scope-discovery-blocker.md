# Task 441 Handoff: Critical Scope Discovery (Phase A blocked pending re-scope)

## Status

No code changes are committed or left in the working tree. The tree was restored to the
clean HEAD (`ebd6bb1d`) after the investigation below revealed that the plan's stated
consumer set is significantly incomplete, and that the missing consumers require new
mathematical infrastructure (not a mechanical port) to fix. Per the "no vacuous
placeholders / no unscoped invention of new axioms" guardrails, I stopped and am handing
back for re-planning rather than improvising a fix to files outside the plan's design
discussion.

## What Was Verified to Work (re-usable directly, no rework needed)

I fully drafted and *individually verified* (`lake build <module>`, zero errors, zero
new warnings) a Phase A patch making `Modal.Proposition` native in
`atom, bot, imp, and, or, box, diamond`:

- `Cslib/Logics/Modal/Basic.lean` -- inductive redefinition; `Satisfies` gets native
  `.and`/`.or`/`.diamond` cases; `Satisfies.and_iff`/`or_iff`/`diamond_iff` become
  `Iff.rfl`; `Satisfies.dual` (`◇φ ↔ ¬□¬φ`) rewritten as a genuine semantic proof
  (no longer definitional) using `rintro`/`push Not`. **Builds green, zero warnings.**
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- `Proposition.Context` extended with
  `andL/andR/orL/orR/diamond`; `congruence` proof extended with matching cases.
  **Builds green.**
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- `toBimodal` gets
  `.and/.or/.diamond` cases (mapping to `Bimodal.Formula.and/or/diamond`, which remain
  Łukasiewicz-encoded on the Bimodal side -- unaffected). **Builds green.**
- `Cslib/Logics/Modal/Denotation.lean` -- `Proposition.denotation` and
  `satisfies_mem_denotation` extended with `.and/.or/.diamond` cases (this file was
  **not** in the plan's Phase A file list but has an exhaustive `induction φ` that
  breaks without the datatype change -- a real gap in the plan). **Builds green.**
- `Cslib/Logics/Modal/FromPropositional.lean` -- `PL.Proposition.toModal_and`/`toModal_or`
  restated: since `PL.Proposition.embed` (the shared generic embedding skeleton in
  `Cslib/Logics/Propositional/Embedding.lean`, task-173 territory, NOT touched) still
  produces the raw Łukasiewicz-encoded shape for `and`/`or` regardless of the target's
  native capabilities, these lemmas' RHS must name the raw nested-`imp`/`bot` shape
  instead of `φ.toModal.and ψ.toModal` (a *different*, non-defeq term once `and` is
  primitive). The `induction φ` proof body of `modal_satisfies_toModal_iff_evaluate` was
  **unchanged** and still builds. **Builds green.**

These five files/patches are safe to re-apply verbatim in a future session; the exact
diffs are reconstructable from this description (they were not saved to disk since I
reverted). I recommend re-deriving them fresh rather than trusting a stashed diff, given
the file-watcher noise in this session.

## The Blocker: Making `diamond` Primitive Breaks the Metalogic/Hilbert Layer

Making `Proposition.diamond` a **primitive constructor** (per the plan's explicit design
goal, since that's what lets tableau rules match `.diamond` directly) destroys a
definitional identity that `Cslib/Logics/Modal/Metalogic/**` and
`Cslib/Logics/Modal/ProofSystem/Instances/**` rely on **structurally**, not just by
notation:

- `Cslib/Foundations/Logic/Axioms.lean:163-165` (`Axioms.AxiomB`, shared generic
  Hilbert-axiom infrastructure, used by every modal/bimodal logic in the repo) defines
  axiom B as the **raw** term `φ → □((□(φ → ⊥)) → ⊥)`, built from `HasBot`/`HasImp`/
  `HasBox` only (deliberately, since `ModalConnectives` does not register `HasDia`).
- Before task 441, `Proposition.diamond` was an `abbrev` for exactly this raw shape, so
  `Modal.Proposition.diamond φ` and `Axioms.AxiomB`'s inner term were **the same Lean
  term** (defeq). Every modal-B/5/D axiom-schema inductive that wrote `□◇φ` using
  `Proposition.diamond`/`◇` notation (`Metalogic/DerivationTree.lean:82`
  `ModalAxiom.modalB`; `ProofSystem/Instances/{B,TB,KB5,DB}.lean` `*Axiom.modalB`) was
  silently relying on this defeq to match the `HasAxiomB` typeclass obligation.
- Once `diamond` is a **distinct primitive constructor**, `□◇φ` (native) and
  `□((□(φ → ⊥)) → ⊥)` (raw) are **different, non-equal terms** in the free inductive
  type. The 5 sites above fail to typecheck (`Application type mismatch`).
  **This part is a mechanical fix** (I verified it): restate each `modalB` constructor
  as `... (Axioms.AxiomB φ)` (the canonical abbrev) instead of manually writing
  `φ.imp (Proposition.box (Proposition.diamond φ))`. I applied and verified this fix for
  `DerivationTree.lean`, `B.lean`, `TB.lean`, `KB5.lean`, `DB.lean` (needs one added
  import: `public import Cslib.Foundations.Logic.Axioms` in `DerivationTree.lean`) --
  all five rebuilt green in isolation.
- **The deep, non-mechanical problem** is in `Cslib/Logics/Modal/Metalogic/MCS.lean`
  and `Cslib/Logics/Modal/Metalogic/Completeness.lean` (canonical-model completeness
  for the B/S4/S5/KB5/TB/DB/D45/D5 Hilbert systems). `MCS.lean:164-174`
  (`mcs_box_diamond`) concludes native `(□◇φ) ∈ S` from a raw-shaped axiom hypothesis
  `h_B`, and `Completeness.lean`'s canonical-model proofs (`canonical_symm`,
  `canonical_eucl`, `canonical_eucl_from_5`, ~lines 100-260) do **syntactic surgery**
  on the diamond term's structure -- e.g. `modal_implication_property` is applied
  directly to a term of type `(◇¬φ) ∈ T` expecting it to structurally unify with
  `(?m → ⊥) ∈ T` (an implication membership), which only worked because `◇¬φ` used to
  **be**, at the term level, `(□(¬¬φ → ⊥)) → ⊥` -- i.e. an actual `.imp` node.
  With `diamond` primitive, `◇¬φ` is a `Proposition.diamond` node, not an `.imp` node,
  so it cannot structurally unify this way. **Fixing this requires either:**
  (a) restating all of MCS.lean/Completeness.lean's diamond-adjacent lemmas to use the
      raw encoded shape explicitly everywhere (never native `◇`) inside the
      canonical-model proofs -- feasible but does not give the canonical model theorems
      a **native**-diamond truth lemma, which the exhaustive `induction φ`s at
      `Completeness.lean:282,417,640,666` (which fail to compile post-datatype-change
      with "Missing cases (Proposition.and _ _)(Proposition.or _ _)(Proposition.diamond _)")
      will need regardless; or
  (b) adding genuine new axiomatic infrastructure -- a `HasDia (Proposition Atom)`
      instance plus `AxiomDiaDualityFwd`/`AxiomDiaDualityBack` (both already defined
      generically in `Cslib/Foundations/Logic/{Connectives,Axioms,ProofSystem}.lean` but
      **not instantiated** for `Modal.Proposition`, `Cslib/Foundations/Logic/Axioms.lean:206-217`)
      threaded through every one of the ~9 affected axiom-schema inductives (`B`, `TB`,
      `KB5`, `S5`, `DB`, `D45`, `D5`, `K45`, `K5`) and their `Systems/*/{Soundness,
      Completeness,ConservativeExtension}.lean` counterparts, so that the canonical-model
      "existence lemma" for native `◇` (`◇φ ∈ S → ∃ T, R S T ∧ φ ∈ T`) can be proved from
      real derivability facts instead of definitional unfolding.

Route (b) is genuinely new mathematical design (which axioms, which systems, soundness
+ completeness re-proof for each) that a plan/user should sign off on before an
implementation agent invents it. Route (a) is more mechanical but still requires
touching `MCS.lean` + `Completeness.lean` + the canonical-model truth lemma (adding
native `and`/`or`/`diamond` cases) with real new proof content for the diamond case
(the existence lemma), not just notation surgery -- and I could not scope how large
that proof content is without first committing to route (a) vs (b).

## Full List of Files Empirically Confirmed Broken by the Phase A Datatype Change

(via `lake build` after applying the five verified patches above; this is the complete
set from a from-scratch `lake build`, i.e. root-cause failures -- files transitively
downstream of these were skipped by `lake` and were not individually re-checked, so the
true blast radius is larger, e.g. `Systems/{B,TB,KB5,S5,DB}/{Soundness,Completeness,
ConservativeExtension}.lean` almost certainly also break once their upstream axiom
files are patched, since they consume `ModalAxiom`/`BAxiom`/etc.):

- `Cslib/Logics/Modal/Tableau/Defs.lean` (expected -- Phase B territory; `modalComplexity`
  and `modalPropHash` have non-wildcard exhaustive matches needing `.and/.or/.diamond`
  cases; `modalDiaOf?_dia`'s `rfl` also breaks since `◇a` is no longer defeq to the
  Łukasiewicz shape it decomposes)
- `Cslib/Logics/Modal/ProofSystem/Instances/{DB,KB5,TB,S5,B}.lean` (fixed by the
  mechanical `Axioms.AxiomB` substitution above, EXCEPT `S5.lean` which also pulls in
  `Metalogic/Systems/S5/Soundness.lean`'s deeper problem below)
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Soundness.lean:57` -- `introN` tactic failure
  in the `modalB` case: the soundness proof for axiom B (`Satisfies m w (φ → □◇φ)`)
  previously unfolded `◇` to the encoded existential-negation form for free; now needs
  an explicit `Satisfies.dual`/`Satisfies.diamond_iff`-mediated rewrite. This is
  small in isolation but signals every `Systems/*/Soundness.lean` that proves axiom
  B/5/D soundness needs the same treatment.
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- the deep blocker described above
  (5 distinct error sites: lines 139, 170, 217, 240, and the exhaustive-induction
  failure at 282).

Also confirmed present but not yet reached in the build order (same root cause, will
surface once upstream is fixed): `Metalogic/MCS.lean` (`mcs_box_diamond` at 164-174 is
internally self-consistent post-patch, i.e. it did NOT itself error, but everything that
*calls* it with the intent of doing syntactic surgery on the result does).

## Recommendation

Do not resume task 441 by directly continuing this patch. Instead:

1. Re-scope the plan (new plan version, `/revise 441` or a fresh planning pass) to
   explicitly cover `Cslib/Logics/Modal/Metalogic/**` and
   `Cslib/Logics/Modal/ProofSystem/Instances/**` as first-class Phase A+ consumers, not
   an afterthought. The plan needs a decision on route (a) vs (b) above **before**
   implementation resumes -- this is a design question, not an implementation detail.
2. Given route (b)'s size (~9 systems × 3 files each, new axiom schemata, new
   soundness+completeness proofs), consider whether task 441 should be split: a
   "Phase A: native datatype + Basic/LogicalEquivalence/ModalEmbedding/Denotation/
   FromPropositional consumers" sub-task that lands independently (it is fully
   self-contained and I verified it builds green in isolation with NOTHING else
   touched), followed by a **separate** task for "port Metalogic Hilbert/MCS layer to
   native diamond" (task 441b?), followed by the original Tableau-focused phases B-F
   (which also still need FmpMeasure.lean [3011 lines] and CompletenessLoop.lean [1096
   lines] -- added by tasks 442/462 after this plan was written -- brought into scope;
   see below).
3. Note for the re-plan: `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (3011 lines) and
   `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (1096 lines) did not exist when
   plan `01_modal-proposition-native-refactor.md` was written (added by tasks 442/462)
   and are **not** in its Phase A-F file lists at all, despite depending pervasively on
   `modalNegOf?/modalOrOf?/modalAndOf?/modalImpOf?/modalDiaOf?` and doing exhaustive
   `induction φ` in multiple places. The plan's phase file lists need updating to
   include these two files (likely under Phase E, since they're completeness/FMP
   territory) before implementation resumes.

## Territory / Concurrency Note

No files were left modified. `git status --short -- Cslib/` is clean at HEAD `ebd6bb1d`.
Verified via targeted `lake build` on `Modal.Basic`, `Modal.Metalogic.Completeness`,
`Modal.ProofSystem.Instances.S5`, `Modal.Tableau.Defs` -- all green post-revert. Safe for
any other concurrent agent/CI to build against.
