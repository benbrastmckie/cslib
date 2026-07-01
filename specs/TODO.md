---
next_project_number: 448
---

# TODO

## Task Order

*Updated 2026-07-01. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,180,226,317,390,396,400,404,407,415,419,438,440,442,444,445,447 | -- | Bimodal Porting, Modal Logic, Temporal Logic, ... |
| 2 | 39,40,181,215,299,375,389,405,409,430,439 | 36,37,180,317,404,407,442 | Bimodal Porting, Modal Logic, Temporal Logic, ... |
| 3 | 41,300,391,392,413,426,441 | 39,40,299,375,389,439 | Foundations, Modal Logic, Temporal Logic, ... |
| 4 | 393,412,425 | 41,391,426 | Foundations, Temporal Logic, PL-Hygiene |
| 5 | 301 | 425 | Temporal Logic |
| 6 | 414 | 181,215,300,301,444,445 | Code Hygiene |

**Grouped by Topic** (indented = depends on parent):

### Bimodal Porting

36 [BLOCKED] — Port discrete completeness (completeness_discrete theorem) and We
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 215 [BLOCKED] — Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal (see above)
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 
  └─ 412 [NOT STARTED] — [Split from task 278.] Simplify proofs in Foundations/Logic/ that

### Modal Logic

396 [NOT STARTED] — Evaluate and salvage the architecture-independent proof-engineeri
404 [RESEARCHED] — Replace the local private re-proofs of List.Forall2 lemmas in Csl
  └─ 405 [NOT STARTED] — Simplify the proof machinery in the task-402 modal tableau soundn
419 [NOT STARTED] — [Spawned from task 415 audit — supports the structure-first visio
442 [IMPLEMENTING] — Fix the Phase 6 blocker in task 299 (modal K tableau completeness
  └─ 299 [BLOCKED] — Implement tableau decision procedure for basic modal logic K with
    └─ 300 [NOT STARTED] — Extend modal K tableau (task 299) with frame-specific rules for r
    └─ 441 [PLANNED] — Refactor Modal.Proposition from the Lukasiewicz encoding (primiti

### Temporal Logic

180 [PR READY] — Add allFuture (G) and allPast (H) as primitive constructors to Te
  └─ 439 [RESEARCHED] — Complete Phase 3 of task 426 (temporal_tableau_ordconstraints_red
    └─ 426 [BLOCKED] — [Decomposed from task 301, blocker A.] Redesign the time-ordering
      └─ 425 [NOT STARTED] — [Decomposed from task 301, blocker C.] Establish the finite model
        └─ 301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Code Hygiene

414 [NOT STARTED] — [Split from task 278.] Simplify Modal/, Temporal/, and Bimodal/ p

### PL Tableau

317 [PLANNED] — Fill the propositional tableau completeness sorries (7 real sorri
  └─ 430 [RESEARCHED] — Prove the atom-persistence / upward-closure structural lemma for 

### Pr Review

440 [NOT STARTED] — PR review: GitHub PR https://github.com/leanprover/cslib/pull/648

### PL Docs

390 [NOT STARTED] — [Refreshed post-merge vet.] The Propositional section (~ORGANISAT
389 [NOT STARTED] — [Reconciled by task 395.] Tier-2. (a) Foundations/Order/HilbertAl
  └─ 391 [NOT STARTED] — [Reconciled by task 395.] Tier-3. Remove internal task/process ja

### PL Hygiene

392 [NOT STARTED] — [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls
393 [NOT STARTED] — Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING befo
413 [NOT STARTED] — [Split from task 278.] Simplify Propositional/ proofs that use ma

### PL Semantics

226 [RESEARCHED] — Cherry-pick propositional semantics from the local codebase into 

### PL Equivalence

375 [NOT STARTED] — Complete the cross-system equivalence story by folding the tablea

### PL Connectives

400 [BLOCKED] — [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/

### PL Base

407 [PR READY] — DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat
  └─ 409 [NOT STARTED] — SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- O
415 [RESEARCHED] — Audit how the structure-first propositional base (MPL/IPL/CPL: pr

### Uncategorized

438 [NOT STARTED] — Upstream the comment/docstring cleanups identified by the task 43
444 [NOT STARTED] — Vet fix for task 180 (High), elevated scope. Do not merely rename
  └─ 414 [NOT STARTED] — (Code Hygiene: [Split from task 278.] Simplify Modal/, ) (see above)
445 [BLOCKED] — Vet fix for task 180 (Medium severity, PR-BLOCKING). HARD REQUIRE
  └─ 414 [NOT STARTED] — (Code Hygiene: [Split from task 278.] Simplify Modal/, ) (see above)
447 [IMPLEMENTING] — Vet (tasks 321/406/431/433/435) found 17 lake shake --add-public 

## Tasks

### 447. Apply lake shake import-minimization fixes to files touched by tasks 321/406/431
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [447_apply_shake_import_minimization_fixes_tasks_321_406_431/reports/01_shake-import-minimization-verification.md]
- **Plan**: [447_apply_shake_import_minimization_fixes_tasks_321_406_431/plans/01_apply-shake-import-fixes.md]

**Description**: Vet (tasks 321/406/431/433/435) found 17 lake shake --add-public --keep-implied --keep-prefix import-minimization suggestions across files touched by tasks 321, 406, and 431. CI otherwise passes (build/test/checkInitImports green; zero sorries). Apply the genuine import-hygiene fixes and verify (do NOT blindly --fix):

FALSE-POSITIVE CANDIDATES (import Cslib.Init removals -- Cslib.Init sets up default linting/tactics, not a term-level dependency; verify, and if legitimately needed add the shake preserve-comment per 'lake shake --help' rather than removing):
- Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean (remove import Cslib.Init)
- Cslib/Logics/Modal/Tableau/Saturation.lean (remove import Cslib.Init; add public import Cslib.Logics.Modal.Tableau.Rules)
- Cslib/Logics/Modal/Tableau/LoopInduction.lean (remove import Cslib.Init + public import ...Saturation; add public import Cslib.Logics.Modal.Basic, Batteries.Data.List.Basic)
- Cslib/Logics/Modal/Tableau/Soundness.lean (remove import Cslib.Init)
- Cslib/Logics/Temporal/Tableau/Rules.lean (remove import Cslib.Init; add public import Cslib.Foundations.Logic.Tableau.PropositionalRules)
- Cslib/Logics/Temporal/Tableau/Saturation.lean (remove import Cslib.Init)

GENUINE IMPORT-HYGIENE FIXES:
- Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean (remove public import Mathlib.Data.Multiset.Basic)
- Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean (swap MCSProperties -> GenericMCS)
- Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean (swap MCSProperties -> GenericMCS)
- Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean (swap MCSProperties -> GenericMCS)
- Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/BurgessHelpers.lean (remove Finset.Max + Tactic.Linarith; add Tactic.NormNum)
- Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean (remove re-export of ...Elimination -- verify barrel still builds)
- Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/Structures.lean (remove Mathlib.Logic.Encodable.Basic) paired with Elimination.lean (add Mathlib.Logic.Encodable.Basic)
- Cslib/Logics/LTL/Semantics/GNBA/Closure.lean (remove Satisfies + Set.Finite.Powerset + Set.Finite.Lattice; add LTL.Syntax.Formula) paired with GNBA/Atoms.lean (add Satisfies)
- Cslib/Logics/Temporal/Metalogic/DenseMCS.lean (remove DeductionHelpers)

After edits, re-run: lake build, lake test, lake exe checkInitImports, lake exe lint-style, and lake shake --add-public --keep-implied --keep-prefix on the touched files to confirm the suggestions are resolved. Scope is limited to these files only -- do NOT attempt the codebase-wide shake backlog. Source: /vet session sess_1782884590_732b0b.

---

### 446. Comprehensive citation and reference-section hygiene across the Temporal metalogic modules
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Dependencies**: Task 445
- **Research**: [446_fix_temporal_burgess_citation_hygiene/reports/01_burgess-citation-hygiene.md]
- **Plan**: [446_fix_temporal_burgess_citation_hygiene/plans/01_burgess-citation-hygiene.md]
- **Summary**: [446_fix_temporal_burgess_citation_hygiene/summaries/01_burgess-citation-hygiene-summary.md]

**Description**: Vet fix for task 180 (Low), elevated scope. Bring every literature reference in the task-180 Temporal work to one uniform, unambiguous, elegant standard.

Core fix: convert the plain-prose "Burgess 1982" citations in TruthLemma.lean (:34, :274), Soundness.lean (:28), DenseSoundness.lean (:28), and RRelation.lean (:21) to the bracket `[Description][BibKey]` format used elsewhere in the diff (e.g. Formula.lean's `[H. Kamp, ...][Kamp1968]`), disambiguating `Burgess1982I` ("Since"/"Until") vs `Burgess1982II` ("Time Periods") at every site.

Ambitious cleanup:
- Audit ALL reference sections and inline citations across the Temporal metalogic tree for consistency: uniform bracket-BibKey format, consistent author/title rendering, and a single house style for the top-of-file "## References" block.
- Verify every cited BibKey actually resolves in references.bib; add any missing entries (e.g. confirm Boudou2017 is present and well-formed; add Burgess entries if the disambiguation reveals a gap). Cross-check that no citation points to a non-existent key.
- Tidy the surrounding module docstrings so reference lists read cleanly and elegantly, matching the phrasing conventions used in the Syntax layer.

Definition of done: every literature citation in task-180 Temporal files uses uniform bracket-BibKey format with correct, resolvable keys; `lake build` green; references.bib validated against all cited keys.

---

### 445. Eliminate the domain-mismatch sorry in Bimodal to Temporal conservativity and refactor the model-transfer layer for generality
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Dependencies**: None
- **Research**: [445_fix_temporal_conservativity_domain_mismatch_sorry/reports/02_literature-grounded-conservativity-obstruction.md]

**Description**: Vet fix for task 180 (Medium severity, PR-BLOCKING). HARD REQUIREMENT: absolutely no sorries are acceptable in any PR. `temporal_valid_of_bimodal_derivable` (TemporalConservativity.lean:269) must be proved outright and BOTH `set_option warn.sorry false in` (:248) and the `sorry` (:269) removed. Disclosure is NOT an acceptable outcome. (The sorry is pre-existing from task 277, but task 180's PR includes this file, so it must be closed here.)

SUPERSEDES task #275 (abandoned): #275 ("Prove Bimodal TM is conservative over Temporal BX") was the original tracking task for exactly this theorem; its goal is fully subsumed here. Close out the conservativity story end-to-end.

Prove the model-transfer result described in the module's "Domain Mismatch Resolution" section: bimodal validity is established on AddCommGroup domains (`temporal_valid_on_addcommgroup`), while Temporal satisfaction is quantified over an arbitrary `Nontrivial`, `NoMaxOrder`, `NoMinOrder` `LinearOrder D`. Close the gap by transporting a countermodel: given a Temporal model over D falsifying phi, transfer it (via an order-embedding of the relevant sub-order into an ordered abelian group such as the rationals, or an order-completion/Hahn-embedding argument) to an AddCommGroup domain preserving `Satisfies`, then contrapose against `temporal_valid_on_addcommgroup` using the proven semantic bridge `bimodal_truthAt_toBimodal_iff_temporal_satisfies`.

Ambitious refactor (not just plugging the hole):
- State the transfer as a general, reusable lemma over any target domain meeting a clearly-specified order interface, so it is not welded to one concrete group; factor out the order-embedding and the satisfaction-transport as independent, named, docstringed lemmas.
- Replace the current "known gap" prose in the module docstring with an elegant, self-contained account of the completed argument and the interface the transfer requires.
- Sweep the surrounding conservativity development for uniformity with the rest of the Bimodal metalogic (naming, section variables, import minimality).

Verification: `lean_verify` on `temporal_valid_of_bimodal_derivable` and `bimodal_conservative_over_temporal` must report only `[propext, Classical.choice, Quot.sound]` with zero sorry; full `lake build`/`lake lint`/`lake test` green. If a genuinely load-bearing mathematical obstruction is found, escalate to the user with the exact open goal state and candidate lemmas — do NOT reintroduce a sorry or a vacuous (`:= True`/`trivial`) placeholder.

Root of the 444/445/446 chain (no task deps): the foundational proof/refactor work; 446 (citations) then 444 (uniformity sweep) run after it.

---

### 444. Uniformity pass: mathlib-conformant naming, style, and docstrings across the entire task-180 Temporal diff
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: Task 446

**Description**: Vet fix for task 180 (High), elevated scope. Do not merely rename the two flagged defs — bring the task-180 diff to a single, uniform, mathlib-conformant standard.

Hard fix (blocks PR): rename `allFuture_iff_neg_someFuture_neg` (Theorems.lean:51) and `allPast_iff_neg_somePast_neg` (Theorems.lean:68) to lowerCamelCase (they are data-carrying `noncomputable def`s returning `DerivationTree`, not `theorem`/`lemma`), updating every call site.

Ambitious cleanup:
- Audit every declaration introduced or modified by task 180 across Cslib/Logics/Temporal/{Syntax,Semantics,ProofSystem,Metalogic,Theorems} and the two Bimodal consumers (Embedding/TemporalEmbedding.lean, Metalogic/ConservativeExtension/TemporalConservativity.lean) for naming uniformity: data-returning `def`s in lowerCamelCase; propositions as `theorem`/`lemma` in snake_case; one consistent convention for the bridge-axiom wrappers, the MCS bridge lemmas (`mcs_allFuture_iff` family), and the Chronicle/TruthLemma helpers.
- Make `lake lint` fully green on these files for defsWithUnderscore, defLemma, docBlame, dupNamespace, topNamespace, simpNF, unusedSectionVars — not just the two flagged lines.
- Ensure every public declaration carries a concise, elegant docstring in the house style; unify the recurring "D3 honesty caveat" comment so it reads identically wherever it appears.
- Remove dead code, leftover scaffolding comments, and any development-only `set_option`s no longer needed.

SCOPE EXCLUSION (conflict avoidance): do NOT touch Cslib/Logics/Temporal/Tableau/ (Defs, Rules, Completeness, Saturation, ...). That subtree is being actively redesigned by the task-301 tableau line (426/439/425); its naming/style cleanup is owned there. Coordinate rather than double-edit.

Depends on 446 (which depends on 445): run last so this sweep sees the final, settled declarations — including any new lemmas introduced by the #445 conservativity proof and the corrected citations from #446 — and can name/document them uniformly without churn.

Definition of done: `lake build`, `lake lint`, `lake exe lint-style` green on every in-scope task-180 file; consistent naming and docstrings verified by inspection; no behavioural change to any proof (renames + docs only).

---

### 442. Modal tableau fmp fuel measure
- **Effort**: 400-800 lines, multiple dispatches
- **Status**: [IMPLEMENTING]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [299_modal_k_tableau/reports/06_spawn-analysis.md]
  - [442_modal_tableau_fmp_fuel_measure/reports/01_fmp-fuel-measure-research.md]
- **Plan**: [442_modal_tableau_fmp_fuel_measure/plans/01_fmp-fuel-measure-plan.md]

**Description**: Fix the Phase 6 blocker in task 299 (modal K tableau completeness) by revising the fuel bound and formalizing the finite-model-property (FMP) termination measure. Constraints: ZERO sorry, ZERO new axioms; NO datatype or rule change (world-subset blocking is "option B", already tracked as task 441, and is explicitly OUT OF SCOPE here -- do not touch modalNextWorld's world-reuse behavior or any rule's output shape). Three-part scope: (1) Revise modalFuel (Cslib/Logics/Modal/Tableau/Saturation.lean:89) upward from the current polynomial O(n^2) to an exponential (or double-exponential, if the measure proof requires it) bound in the formula size. This step alone is soundness-safe: modalExpandBranches_closed_unsat (Soundness.lean:226) is fuel-agnostic (closed implies unsat holds for arbitrary fuel), so only the numeric value of modalFuel changes -- no soundness proof needs rework. (2) Formalize the FMP termination measure that discharges the fuel = 0 case of modalExpandBranches: an a-priori world-count / world-label bound (needed because modalNextWorld-minted labels are currently unbounded a priori); a finite signed-subformula universe U(phi); a subformula-closure lemma covering all four modal rules' outputs (witness + boxProps + diaNegProps) plus the propositional rule outputs, showing every formula produced during expansion lies in U(phi); output-disjointness (new formulas produced by a rule firing are fresh on the branch); and a per-branch weight ~3^R (where R measures unconsumed universe elements) to absorb the <=2-way propositional branching, mirroring the classical 3^complexity measure used in classicalExpandBranches_hintikka. (3) Prove modalStepBranch_none_saturated and then modalExpandBranches_hintikka by fuel induction plus inner Forall2-accessibility induction, mirroring classicalExpandBranches_hintikka (Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924) and reusing the acc-threading pattern already established in modalExpandBranches_closed_unsat (Cslib/Logics/Modal/Tableau/Soundness.lean:165). Then discharge modalTableau_complete via the already-proven modalOpenBranch_countermodel (task 299 Phase 5d, green), and finally modalTableau_decides plus its Decidable instance (task 299 Phase 7, currently gated on this work). Reference templates: classicalExpandBranches_hintikka (Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:924), classicalStepBranch_none_saturated / classicalStepBranch_hintikka_inv (same file, lines 694/722), and the hoisted forall2_* worklist helpers already available in Cslib/Logics/Modal/Tableau/LoopInduction.lean. Full reference-signature detail and the precise per-rule dispatch obligations are recorded in task 299's plan (specs/299_modal_k_tableau/plans/05_modal-k-tableau-plan.md, Phase 6 "DECISIVE FINDING" addendum and "Precise residual obligation" list) and should be read as background before starting. Definition of done: modalStepBranch_none_saturated, modalExpandBranches_hintikka, modalTableau_complete, modalTableau_decides, and a Decidable instance all compile with ZERO sorry and ZERO new axioms; #print axioms on each shows only standard axioms; whole-library lake build stays green.

---

### 441. Modal proposition native refactor
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 299
- **Plan**: [441_modal_proposition_native_refactor/plans/01_modal-proposition-native-refactor.md]

**Description**: Refactor Modal.Proposition from the Lukasiewicz encoding (primitives atom/bot/imp/box; and/or/neg/diamond encoded as nested imp) to NATIVE constructors atom/bot/imp/and/or/box/diamond (diamond primitive), mirroring the propositional layer (PL.Proposition has native and/or). Goal: highest-quality mathematical foundations — one tableau rule/decomposer per connective, structural-induction truth lemma, no unsound uniform-imp bridge lemmas, no view/strong-induction workarounds. Cascades through Modal/Basic.lean (datatype+Satisfies+complexity+axiom theorems), Modal/LogicalEquivalence.lean (Context), all Modal/Tableau/*, and Bimodal/Embedding/ModalEmbedding.lean. Design captured in plans/01 (was task 299 plan v6). Depends on task 299 (encoding-based tableau) landing first; this then re-bases it onto native constructors. Zero sorry/admit/new-axiom. Est 1,500-2,000 lines touched.

---

### 440. Review pr leanprover cslib 648
- **Status**: [NOT STARTED]
- **Task Type**: pr
- **Topic**: pr-review
- **Dependencies**: None

**Description**: PR review: GitHub PR https://github.com/leanprover/cslib/pull/648 — address ctchou CHANGES_REQUESTED feedback (Gentzen/Avigad references, Semantics restructuring confirmation, reviewer reply, coordinate #587/#607)

---

### 439. Refactor processnext to mutual def and prove instantstrict t
- **Effort**: 3-5 hours
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 180
- **Research**: [426_temporal_tableau_ordconstraints_redesign/reports/03_spawn-analysis.md]

**Description**: Complete Phase 3 of task 426 (temporal_tableau_ordconstraints_redesign). Phases 1, 2, 4, 5 are already done and green. Only Phase 3 remains.

The blocker: in Cslib/Logics/Temporal/Tableau/Saturation.lean, `processNext` is a `let rec` nested inside `temporalExpandBranches`. The two functions are mutually recursive: `processNext` (line ~219) calls `temporalExpandBranches`, and `temporalExpandBranches` (line ~231) calls `processNext`. This mutual recursion is currently expressed via closure (nesting). Lean 4 generates no standalone recursion principle for `let rec` bindings, so the `InstantStrict` threading proof cannot be expressed as designed.

Step 3.1 (mechanical refactor): Convert the nested `let rec processNext` + `temporalExpandBranches` into a `mutual ... end` block at top level. The termination argument is lexicographic: `temporalExpandBranches` recurses on `fuel` (Nat), `processNext` recurses structurally on `List.length pending`; `processNext`'s call to `temporalExpandBranches` uses `fuel'` (strictly smaller). Verify with `lake build Cslib.Logics.Temporal.Tableau.Saturation` before attempting any proof. Commit the green refactor.

Step 3.2 (threading proof): Now that `processNext` is a top-level def in a `mutual` block, it has a recursion principle. Prove `InstantStrict` is preserved through the run by induction on fuel (for `temporalExpandBranches`) and structural induction on `pending` (for `processNext`), using the Phase 2 edge-by-edge lemmas (`InstantStrict.addFuture`, `InstantStrict.addPast`) as the inductive step. Commit green.

Step 3.3 (wire and finalize): Use the run-level `InstantStrict` result to discharge the order-preservation component of `openBranch_branchSat` for the D=Z/f=instant model, as far as the FMP boundary allows (Until/Since remain FMP-blocked, leave documented, no sorry). Run `lake build && lake test` and `lake exe checkInitImports`. Update task 426 to completed; update summary.

Reference: specs/426_temporal_tableau_ordconstraints_redesign/plans/02_phase3-streamlined.md for full step details. Files: Cslib/Logics/Temporal/Tableau/Saturation.lean (refactor), Cslib/Logics/Temporal/Tableau/Completeness.lean (wire). Territory constraint: serialize with task 427 on Completeness.lean (never parallelize). Zero-debt: no sorry allowed.

---

### 438. Pr task431 comment cleanups
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Dependencies**: None

**Description**: Upstream the comment/docstring cleanups identified by the task 431 audit via a CSLib PR. The edits are already applied and committed locally at 35436d7e (chore): (1) deleted the commented-out Term.subst_comm TODO stub in Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean, (2) reworded the stale 'removing the sorry' docstring in Cslib/Logics/LTL/Semantics/GNBA.lean:37 to past tense. Both are comment-only (no proof/build impact). Remaining work: submit to leanprover/cslib via /pr (user-only command) with a 'chore'/'doc' prefixed title. Optionally bundle any further doc-hygiene found in those two modules. Source: task 431 audit.

---

### 430. Prove atom persistence upward closure for intexpan
- **Effort**: 2-3 hours
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: PL-Tableau
- **Dependencies**: Task 317
- **Research**:
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/01_atom-persistence-upward-closure.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/02_team-research.md]
  - [430_prove_atom_persistence_upward_closure_for_intexpan/reports/03_falsification-spike.md]

**Description**: Prove the atom-persistence / upward-closure structural lemma for open branches produced by `intExpandBranches`, and use it to discharge the two validity-bridge sorries in task 317.

## Context

Task 317 has two remaining validity-bridge sorries:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:112` (`intuitionisticTableau_complete`): needs `IValid φ → ∀ b, IForces (intExtractValuation b) (fun _ => False) 0 φ`.
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:109` (`minimalTableau_complete`): needs `MValid φ → ∀ b, IForces (intExtractValuation b) (minBranchBotForces b) 0 φ`.

Instantiating `IValid`/`MValid` at the branch model (World = Nat, val = intExtractValuation b) requires supplying upward-closure of `intExtractValuation b`:
  `T(atom p)@w ∈ b ∧ w ≤ w' → T(atom p)@w' ∈ b`

This atom-persistence property is NOT in `IBranchSaturation` (which covers compound-formula saturation only). The orchestrator handoff `.orchestrator-handoff.json` identifies this as blocker B3.

## What needs to be proved

Prove `intExpandBranches_openBranch_atom_persist` (or equivalent): if `intExpandBranches ... = .openBranch b`, then `intExtractValuation b` is upward-closed under the appropriate world accessibility relation.

Key structural facts to use:
- `propagatePersistence` (Rules.lean) copies ALL T(α) from parent world w to fresh child world w' when F(φ→ψ)@w fires (`intFImpRule`). So atoms propagate from direct parents to direct children.
- `applyAllTImpRules`/`applyPersistenceFixpoint` (Expansion.lean) run the T(φ→ψ) modus-ponens fixpoint across the edge list. Atoms are not directly handled here, but the T(→) consequences of atom propagation are.
- The explicit edge list `edges : IEdges` tracks `(child, parent)` pairs; `isAccessible edges w w'` is the reachability relation.

## Design decision the implementer must make

There are two viable paths:

**Path A (recommended if provable)**: Prove upward-closure under `≤` on Nat. This is the current countermodel's Preorder. Requires showing that whenever `T(atom p)@w ∈ b` and `w' > w` is a world on the branch, then `T(atom p)@w' ∈ b`. This follows from transitivity of `propagatePersistence` across the world tree, because new worlds are assigned strictly increasing labels and each inherits all T(α) from its parent. Verify with `lean_goal` at the sorry site whether this holds for the expansion invariant.

**Path B (fallback)**: If `≤` on Nat does not match the edge-list accessibility (sibling worlds may share `≤` ordering but not be accessible to each other), define the countermodel Kripke accessibility using `isAccessible edges` instead of `≤`. This requires:
- Defining a custom `Preorder` on Nat for the specific branch `b` and its edge list (or passing the edge list from `openBranch_countermodel` down to the validity bridges).
- Proving `intExtractValuation b` is upward-closed under `isAccessible edges`.
- Updating `openBranch_countermodel` to pass the edge list and use `isAccessible`-based Preorder.

## Exposition target

Expose the atom-persistence fact as ONE of:
1. A new field `sat_atom_persist` in `IBranchSaturation` (simplest if it can be proved from the expansion).
2. A standalone `private lemma intExpandBranches_openBranch_atom_persist` in `Scheme.lean`.
3. A wrapper helper `intExtractValuation_uc` proved inline at the sorry sites.

The chosen form must be sufficient to supply the upward-closure argument to `IValid`/`MValid` instantiation in both `intuitionisticTableau_complete` and `minimalTableau_complete`.

## Files to modify

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — add the persistence structural lemma (or new `IBranchSaturation` field + proof in `intExpandBranches_openBranch_sat`).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` — fill sorry at ~L112.
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` — fill sorry at ~L109.
- Possibly `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` and/or `Rules.lean` if invariants need to be stated there.

## Non-goals

- Do NOT touch the T(imp) sorry at Scheme.lean:330 (task 317's remaining obligation).
- Do NOT touch the `intExpandBranches_openBranch_sat` leaf sorries at Scheme.lean:481/536/550 (task 317's remaining obligation).
- Do NOT touch `*/Soundness.lean` (task 316 territory).

## Verification

After implementation:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` and `…Minimal.Completeness` succeed with the two validity-bridge sorries gone.
- `grep -n sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` returns nothing.
- `grep -n sorry Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` returns nothing.
- Build remains green (no regressions in Scheme.lean or Soundness files).

---

### 426. Temporal tableau ordconstraints redesign
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 439
- **Research**: [426_temporal_tableau_ordconstraints_redesign/reports/01_ordconstraints-redesign.md]
- **Plan**: [426_temporal_tableau_ordconstraints_redesign/plans/02_phase3-streamlined.md]
- **Summary**: [426_temporal_tableau_ordconstraints_redesign/summaries/01_partial-summary.md]

**Description**: [Decomposed from task 301, blocker A.] Redesign the time-ordering scheme in the temporal tableau so the ordering invariants hold. The lemma ordConstraints_strict (Cslib/Logics/Temporal/Tableau/Completeness.lean) is FALSE as stated: addPast t tNew adds the constraint (tNew, t) with tNew > t, violating the claimed invariant (a,b) in constraints -> a < b. Choose and implement a correct scheme (e.g. topological sort of the constraint graph, or a signed/relative integer time domain) so that extractModel builds a well-founded strict order, then prove the corrected ordConstraints lemma sorry-free. Start from green commit 7f052834. Independent of tasks 424 and 425.

---

### 425. Temporal tableau ptl fmp decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 426

**Description**: [Decomposed from task 301, blocker C.] Establish the finite model property (FMP) for Propositional Temporal Logic and use it to discharge temporalTruthLemma_untl and temporalTruthLemma_snce (Until/Since eventuality fulfilment), which in turn unblock eventualityDefect_unsat, temporalTableau_sound, openBranch_branchSat, temporalTableau_complete, and the final instDecidableValid in Cslib/Logics/Temporal/Tableau/. This is the theoretical gate for full decidability. Mirror the approach of COMPLETED task 421 (min_fmp_decidability), which added a sorry-free Decidable instance via FMP — reuse its pattern/infrastructure where possible. The hardest sub-part; gates task 301 completion. Independent of tasks 423 and 424 in principle, but final wiring of instDecidableValid needs all three landed.

---

### 419. Generalize derivation lifting to a cross-logic InferenceSystem layer (spike)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [419_generalize_derivation_lifting_intersystem/reports/02_virtuous-unification.md]
- **Plan**: [419_generalize_derivation_lifting_intersystem/plans/02_proof-system-morphism-overlay.md]

**Description**: [Spawned from task 415 audit — supports the structure-first vision; SPIKE.] Investigate hoisting liftDerivation / Derivable_mono (Modal/Metalogic/InterSystem/Lifting.lean:47) and Bimodal's liftDerivationWith onto the shared InferenceSystem / algebraicDerivationSystem abstraction already used by GenericMCSBridge, yielding ONE axiom-subsumption derivation-lifting result reusable by Modal, Bimodal, and PL. SPIKE FIRST: commit only if the necessitation / temporal_duality constructor variance is cleanly abstractable; otherwise document precisely why and stop (mark BLOCKED, never sorry). Benefits from task 417's Foundations placement (soft dependency). Effort L (abstraction risk). CI green if landed. Source: report §6, Rank 4.

---

### 415. Audit propositional->modal/temporal/bimodal lifting vs structure-first vision
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: PL-Base
- **Dependencies**: None
- **Research**: [415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md]

**Description**: Audit how the structure-first propositional base (MPL/IPL/CPL: primitive nullary bot, gated efq/botL, property-module typeclasses) actually LIFTS into the Modal, Temporal, and Bimodal logics, and assess the result against the CSLib Zulip "Propositional Logic" thread (606970606) structure-first / fragment-genericity expectations -- with the explicit goal of identifying where the architecture can SURPASS those expectations. This is an infrastructure-verification (research/review) task; it produces a report and SPAWNS concrete follow-on implementation tasks, it does not itself refactor proofs.

THREE SEED FINDINGS to verify and deepen (from prior exploration):
1. CPL-ONLY EMBEDDING: toModal/toTemporal/toBimodal encode and/or via Lukasiewicz (Modal/FromPropositional.lean:35-41, Temporal/FromPropositional.lean:34-40, Bimodal/Embedding/PropositionalEmbedding.lean:33-41) -- classically valid but NOT intuitionistically valid. So only the CLASSICAL collapse of the propositional base lifts; the minimal/intuitionistic structure-first base does NOT survive the lift. Confirm with exact embedding defs + the semantic-preservation theorem statements (modal_satisfies_toModal_iff_evaluate:106 etc.), and characterize precisely what a structure-preserving (native and/or) embedding would require.
2. CONSERVATIVITY ASYMMETRY: Modal uses a PARAMETRIC conservativity lemma (modal_conservative_extension_param, Modal/Metalogic/ConservativeExtension.lean:54) while Temporal (ConservativeExtension.lean:87) and Bimodal (Metalogic/ConservativeExtension/PropositionalConservativity.lean:60) re-prove it CONCRETELY. Assess whether a single parametric/Foundations-level conservativity-lift framework can subsume all three.
3. GENERICLINDENBAUM DEBT: GenericLindenbaum.lean:47 defines a parametric explosion-parameterized substrate but Min/Int Lindenbaum, soundness, and strong-completeness remain ~50% duplicated; re-instantiation is "deferred to Phase 6" (task 407 residual). Scope the consolidation and its overlap with task 393.

ALSO: check the InterSystem liftDerivation (Modal/Metalogic/InterSystem/Lifting.lean:47) and whether the per-system structural metatheory (weakening/subst/cut across ND/LJ/LK) admits a shared parametric layer.

DELIVERABLE: a report at specs/415_*/reports/01_*.md that (a) verifies/refutes each finding with file:line evidence, (b) maps the lift architecture against the Zulip structure-first vision (met / partial / open), (c) for each gap gives a concrete Lean-level sketch of the fix and an effort estimate, and (d) proposes a prioritized set of spawnable follow-on tasks (e.g. structure-preserving embedding; unify conservativity; GenericLindenbaum Phase-6). Honor the Zulip AI policy (any prose intended for upstream must be human-authored). No code changes in this task.

---

### 414. Simplify proofs normalization modal family
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 180, Task 181, Task 215, Task 299, Task 300, Task 301, Task 444, Task 445, Task 446

**Description**: [Split from task 278.] Simplify Modal/, Temporal/, and Bimodal/ proofs that use manual `simp only [listImp_*, bigconj_*, toTemporal_*, toBimodal_*]` lists or verbose tactic chains over the task-268 normalization lemmas (including the Temporal/FromPropositional and Bimodal/Embedding/TemporalEmbedding embedding simp lemmas); replace with `grind`/`simp` where the new co-tags make the explicit lists redundant. Sequence after the modal-family proof-development settles: Modal 299/300; Temporal 180 (G/H primitives rewrite FromPropositional.lean), 241, 301; Bimodal 181 (propagates constructors through TemporalEmbedding.lean), 215, 275; plus the file-structure pass 321. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake.

---

### 413. Simplify proofs normalization propositional
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Hygiene
- **Dependencies**: Task 317, Task 375

**Description**: [Split from task 278.] Simplify Propositional/ proofs that use manual `simp only [listImp_*, bigconj_*]` lists or verbose tactic chains over the task-268 normalization lemmas; replace with `grind`/`simp` where the new co-tags make the explicit lists redundant. Covers Hilbert/ND/completeness/decidability proof sites in Cslib/Logics/Propositional/. Sequence after the major PL proof-development tasks land (317 tableau completeness, 370 int/min decidability, 375 proof-system equivalence) and the Logics/Foundations file-structure pass (321). Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake.

---

### 412. Simplify proofs normalization foundations
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 41

**Description**: [Split from task 278.] Simplify proofs in Foundations/Logic/ that use manual `simp only [listImp_nil, listImp_cons, bigconj_nil, bigconj_singleton, bigconj_cons_cons, negBigconj_def, ...]` or verbose tactic chains over the task-268 normalization lemmas; replace with `grind`/`simp` where the @[simp, scoped grind =] co-tags (ListImplication.lean, Theorems/BigConj.lean) make the explicit lemma lists redundant. Audit ListImplication, BigConj, and downstream Foundations/Logic proof sites. Sequence after the Foundations completeness-infra abstraction (41) and the Logics/Foundations file-structure pass (321) to avoid re-sweeping moved code. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake.

---

### 409. Literal ⊥-rule-free base ND inductive (option B): split MinDerivation + Explosion; re-cut Curry-Howard & normalization
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Base
- **Dependencies**: Task 407

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- OPTIONAL / advanced. Task 407 adopts option C (re-frame the task-398 gated efq constructor as the explosion property module; the base relation is ⊥-rule-free UP TO the IsIntuitionistic gate). Option B is the LITERAL structure-first ND: split Theory.Derivation into a genuinely ⊥-rule-free base inductive MinDerivation (no efq constructor) plus an Explosion extension, prove all structural metatheory once on the base, and recover IPL-ND by adjoining efq. TRIGGER CONDITION: only pursue if a concrete downstream consumer needs a physically ⊥-free derivation object (e.g. a minimal-ND normalization theorem, or a lambda-calculus without an abort/efq combinator). COST/RISK: re-opens the single genuinely hard point from task 398 -- the subformula property under efq -- and forces re-cutting Curry-Howard (Theory.Term mirror) and Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) against the split. Reuse the task-398 decided strategy (atomic restriction + permutation conversions); treat any non-green proof as [BLOCKED], never sorry. HIGH effort -- use --hard. Depends on 407 (and ideally 408). Source: task 407 report 01 §5 option B / §7 W6, report 02 §5. ALIGNMENT NOTE: this two-inductive split is the Design-B-flavored route that the universal-algebra approach (task 407 option C) deliberately AVOIDS, because it duplicates derivation structure (exclude-then-add at the derivation level). Default remains task 407 option C: ONE derivation type with explosion as a property module. Pursue 409 ONLY if the trigger condition above fires.

---

### 407. Research & design: make MPL the structure-first base logic (⊥ as nullary connective; explosion/leastness/initiality as independent property modules)
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: PL-Base
- **Dependencies**: None
- **Research**:
  - [407_mpl_base_structure_first_redesign/reports/01_mpl-base-structure-first.md]
  - [407_mpl_base_structure_first_redesign/reports/02_mpl-base-with-vs-without-bot.md]
  - [407_mpl_base_structure_first_redesign/reports/03_design-verification-plan-readiness.md]
- **Plan**: [407_mpl_base_structure_first_redesign/plans/04_mpl-base-waves-1-4-v2.md]
- **Summary**:
  - [407_mpl_base_structure_first_redesign/summaries/04_mpl-base-waves-1-4-v2-summary.md]
  - [407_mpl_base_structure_first_redesign/summaries/05_initial-object-witness-summary.md]
- **Design_note**: [407_mpl_base_structure_first_redesign/mpl-base-design-note.md]

**Description**: DESIGN SOURCE: user's ChatGPT design conversation (specs/tmp/chat.md) + codebase synthesis. Adopt the STRUCTURE-FIRST account: one fixed language ⟨Atom,⊥,∧,∨,→⟩; ⊥ is a primitive NULLARY connective whose meaning is intentionally underdetermined (a Johansson 'designated constant' supplied by every model, no intrinsic proof rule). MPL is the BASE proof theory (no rule/axiom mentions ⊥; ¬A:=A→⊥; A,A→⊥⊢⊥ is just impE). IPL = MPL + explosion (⊥/A) as an INDEPENDENT module; CPL = IPL + classical principles. Semantically, leastness (⊥≤a), initiality (universal property 0→A), and explosion-soundness are INDEPENDENT properties added by conservative strengthening, not changes to syntax or recursive clauses. Modularity organized around PROPERTIES (typeclasses/mixins), not connectives, so structural metatheory (weakening, substitution, admissibility, cut) is proved ONCE at MPL. RELATION TO 398: this is the deeper redesign 398 postponed (398 report §5). 398 took the OPPOSITE commitment (IPL-as-base via a gated ND efq constructor). Recommendation (report §5) is option (C): re-frame 398's gate as the explosion PROPERTY MODULE rather than revert it. FINDINGS (report 01): codebase is already ~70-80% structure-first. ALIGNED: algebraic semantics (AlgEvaluate with arbitrary bot_val; BrouwerianBot vs PointedBrouwerian; IsBotFree; conservativity chains) and Hilbert axioms (MinPropAxiom→IntPropAxiom+efq→PropositionalAxiom+peirce; IsIntuitionistic/MinimalAxioms typeclasses). GAPS: (1) ND inverted by 398 (gated efq = IPL-base); (2) sequent calculus LARGE gap (LJ/LK hard-code botL; no minimal LM; structural results per-system); (3) metalogic ~50% Min*/Int* duplication, Lindenbaum hard-wires EFQ; (4) semantic leastness/initiality/explosion present only implicitly (OrderBot + per-axiom proofs), not as a NAMED property hierarchy. SCOPE: research+design done (report 01). Plan should cover the cheap additive waves first: W1 design canonicalization+ND re-framing (C), W2 named semantic property hierarchy, W3 metalogic genericization, W4 tableau unification; and SPAWN W5 (minimal sequent calculus LM) and optional W6 (literal ⊥-rule-free ND, option B) as separate --hard tasks. Preserve ALL MPL/conservativity assets (do not revert 398). --hard recommended for planning. Honor Zulip AI policy. See OPEN QUESTIONS in report §9 (ND reconciliation C vs B; task scope; categorical/initiality timing; property naming; relation to task 400).

---

### 405. Proof style cleanup modal soundness
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 404

**Description**: Simplify the proof machinery in the task-402 modal tableau soundness redesign before any upstream PR. Targets in Cslib/Logics/Modal/Tableau/Soundness.lean: modalApplyOne_fresh (uses unfold + extract_lets + `repeat first | Or.inl rfl | Or.inr ... | split` plus an apply_ite/ite_self cleanup) and the modalExpandBranches_closed_unsat per-branch accs/Forall2 reformulation. Improve readability/robustness without changing statements. Verify scoped + full lake build green, zero sorry, lint-style pass. Touches the same file as task 404 (sequence after it); overlaps code-hygiene task 321.

---

### 404. Forall2 mathlib cleanup soundness
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**: [404_forall2_mathlib_cleanup_soundness/reports/01_forall2-mathlib-cleanup.md]

**Description**: Replace the local private re-proofs of List.Forall2 lemmas in Cslib/Logics/Modal/Tableau/Soundness.lean (forall2_append_aux, forall2_drop_aux, forall2_take_aux, forall2_of_zip_mem) with canonical Mathlib lemmas. These were added during task 402 because Mathlib.Data.List.Forall2 is not transitively imported by Cslib.Init. Either add the Mathlib import and switch call sites to library lemmas (List.Forall2.append/length_eq/etc.), or document why the local helpers are kept. Verify scoped + full lake build green, zero sorry, lint-style pass. Low-priority polish; helpers are correct as-is.

---

### 400. Unbundle connective typeclasses; reconcile with fmontesi PR #607 (Waring's flag a)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: PL-Connectives
- **Dependencies**: None
- **Research**:
  - [400_reconcile_connectives_pr607/reports/01_pr607-engagement.md]
  - [400_reconcile_connectives_pr607/reports/02_engagement-strategy.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/01_comparison-tables.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/02_falsum-bridge-sketch.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/03_grind-direction-finding.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/04_review-packet.md]
- **Plan**: [400_reconcile_connectives_pr607/plans/02_pr607-engagement.md]

**Description**: [ENRICHED 2026-06-29 — see specs/400_reconcile_connectives_pr607/reports/01_pr607-engagement.md] Engage fmontesi PR #607 (feat(Logic): logical operators) to land the connective typeclasses there instead of in #648 (Waring, Zulip 606970606). PREREQ DONE: our Connectives.lean removed from #648 (commit 85db79a6 on feat/propositional-ipl-base). PRIMARY POINT for the #607 review: #607 makes negation primitive (HasNot) and has NO HasBot; for IPL/MPL, neg is definitionally (phi -> bot), so #607 needs a HasBot (and HasTop) class with neg/top DERIVED, else the five-primitive Proposition (primitive bot) cannot register faithfully. SECONDARY: naming HasImpl/impl vs HasImp/imp; notation precedence conflicts (-> 25 vs 30, or 30 vs 35); bundle-vs-a-la-carte (PropositionalConnectives); notation ownership (typeclass notation + _def lemmas vs direct-on-Proposition). DELIVERABLE: human-authored review on #607 (Zulip AI policy), then register Proposition instances via #607 once the falsum question settles. Independent of the IPL-base work.

---

### 396. Salvage reusable lemmas from task-299 Soundness refactor for the per-branch-accessibility soundness redesign
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Evaluate and salvage the architecture-independent proof-engineering lemmas left on branch wip/task-299-soundness-refactor (commit 27d93e2d) by the stopped task-299 modal-K soundness re-attempt. Portable (acc-free) candidates: sfSat, sfSat_pos, sfSat_neg, RuleResultSat, and recognizer characterization lemmas (e.g. modalNegOf?_eq_some) in Cslib/Logics/Modal/Tableau/Soundness.lean, plus the branchSatisfiable Type (vs Type*) universe simplification. The FULL 299 refactor is UNBUILT and rewrites modalStepBranch_preserves_sat on the now-superseded global-Accessibility architecture, so do NOT merge it wholesale. Goal: decide which lemmas help the modal-tableau soundness-gap-redesign effort (the per-branch Accessibility 'task 384' tracked in the cslib-364 worktree / branch task-364-soundness-drift) and cherry-pick or restate them there if the propositional-rule recognizer layer hits the 'stuck on variable antecedent / consumed-scrutinee' friction documented in specs/364_modal_tableau_soundness_drift_repair/handoffs/BLOCKED-repair-guide.md (section 4). NOTE: 'task 384' here means the soundness-gap-redesign task in the cslib-364 worktree, which is a DIFFERENT task than main's own #384 (tableau_completeness_sorries) — task numbering diverged across worktrees. Reference branch: wip/task-299-soundness-refactor. Parent context: task 299 modal_k_tableau.

---

### 393. Consolidate duplicated Lindenbaum/Classical/conservativity constructions (Zulip first)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Hygiene
- **Dependencies**: Task 391

**Description**: Tier-3, cross-cutting — coordinate on Zulip per CONTRIBUTING before refactor. (a) Factor one generic quotient-Lindenbaum construction over the 3 parallel builds (~2100 lines): HilbertLindenbaum, HilbertLindenbaumRel, HilbertAlgCompleteness (4th in Bimodal). (b) Make litCtx_congr public and parameterize the 3 Classical completeness files (~700 lines, litCtx_congr' copied 3x) over the axiom predicate via GenericMCSBridge/HasMinimalAxioms. (c) Assess 3 Soundness modules + 8 conservativity modules + LJ/LK helper duplication. Source: §5.5.

---

### 392. Remove dead declarations and fix underscore/Extention naming
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Hygiene
- **Dependencies**: Task 317, Task 389

**Description**: [Reconciled by task 395.] Tier-3. Delete grep-verified dead decls: Tableau/Classical/Soundness.lean:73-136 (12 classicalApplyOne_* private simp lemmas, 0 calls) + :486, Classical/Completeness.lean:435/447, Tableau/Defs.lean:81 propImpOrNegOf?, Intuitionistic/Rules.lean:114/203, Intuitionistic/Soundness.lean:431/505, NaturalDeduction/Equivalence.lean:305 hilbertAxiomToND, LK/Completeness.lean:69/73 mem_insert_*. Fix Extention->Extension typo (Equivalence.lean:256-257, Defs.lean:190/195). Rename underscore defs: modus_ponens constructor (Derivation.lean:77), lift_int_to_cl, goodSelection_seq, HasFresh to_infinite, emptyHrelation_apply. The LK/LJ cutAdm_*/ljCutAdm_* renames are DROPPED from this task — task 386 OWNS them (defsWithUnderscore). Sequence after 386. Source: §5.3-5.4 + 395.

---

### 391. Strip task-number jargon and fix stale docstrings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Docs
- **Dependencies**: Task 317, Task 389

**Description**: [Reconciled by task 395.] Tier-3. Remove internal task/process jargon from public docstrings: ClassicalConjImpCompleteness.lean (task 352, CL-B rung), ClassicalConjImpBotCompleteness.lean (task 378, CL-C rung), ConservativeChain.lean:44-45, HilbertLindenbaumRel.lean:21-23 (Route A2, 341 proof files), Tableau/RuleResult.lean:35, Foundations/Logic/Tableau/PropositionalTableau.lean:7, ListImplication.lean:83-139. Connectives.lean jargon (PR#607/task 340/173) is OWNED by task 400 (Connectives owner) — coordinate, do NOT double-edit. Stale-count fixes: re-verify post-task-398. NOTE StrongCompleteness 3-case counts (atom/bot/imp) remain CORRECT (398 changed derivation constructors, not formula structure). Fix only genuinely-stale counts: IntSoundness, MinSoundness, IntLindenbaum:320 misattached docstring, Tableau Int/Min DecisionProcedure sorry counts, Minimal/Completeness:50-51. Source: §5.1-5.2 + 395.

---

### 390. Update ORGANISATION.md Propositional section (post-merge tree)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Docs
- **Dependencies**: None

**Description**: [Refreshed post-merge vet.] The Propositional section (~ORGANISATION.md:100-105) is a 4-item stub. Update to reflect the actual 95+-file tree: SequentCalculus/{LJ,LK} (Interpolation, CutElimination, SubformulaProperty, Decidability); CurryHoward/{Defs,Isomorphism,Reduction}; Semantics/Algebra (25+ files: Brouwerian, HilbertAlgebra, Kripke, Glivenko, Conservative variants); Tableau/{Classical,Intuitionistic,Minimal} (Completeness/Soundness/DecisionProcedure); Subformula.lean; ProofSystemEquivalence.lean. Also update the Namespace Convention section re Cslib.Logic.PL vs Cslib.Logic.Propositional (task 387). Do before the PR lands.

---

### 389. Fix docBlame, barrel headers, unusedSectionVars, broken citation
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Docs
- **Dependencies**: Task 317

**Description**: [Reconciled by task 395.] Tier-2. (a) Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean: add docstrings to 7 undocumented def/abbrev (fld:50 also rename himpFold, fmeLe:106, fmeEquiv:123, fmeSetoid:125, FreeMeetExtension:152, mk:159, freeMeetEmbed:257) — only hard docBlame in Foundations. (b) DROPPED — the 4 Tableau barrels already carry copyright + import Cslib.Init (verified post-merge). (c) Add omit for 14 unusedSectionVars (mostly Tableau/Classical/Completeness, Minimal/Soundness:118, Minimal/Completeness:89). (d) Add references.bib entry NegriVonPlato2001 (Negri & von Plato, Structural Proof Theory, CUP 2001) cited by OrImpConservative.lean. Sequence the Tableau/Classical+Minimal Completeness edits AFTER task 317. Source: §4.3-4.6 + 395.

---

### 375. Proof system equivalence tableau sequent edges
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: PL-Equivalence
- **Dependencies**: Task 317

**Description**: Complete the cross-system equivalence story by folding the tableau (and remaining sequent) decision systems into the proof-system TFAE. Cslib/Logics/Propositional/ProofSystemEquivalence.lean currently proves Hilbert<->ND<->LK for CPL (cplProofSystemsTfae) and Hilbert<->ND<->LJ for IPL (iplProofSystemsTfae), plus the MPL Hilbert<->ND two-way. Add the missing edges so the equivalence is genuinely complete across all proof systems: classical Tautology <-> LK provability <-> closed classical tableau, and intuitionistic validity <-> LJ provability <-> closed intuitionistic tableau, extending the TFAE lists accordingly. Requires the tableau soundness+completeness to be green (task 316 done for soundness; task 317 for completeness) and the classical tableau build repaired (task 363). No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 317, 363.

---

### 317. Propositional tableau completeness
- **Status**: [PLANNED]
- **Task Type**: cslib
- **Topic**: PL-Tableau
- **Dependencies**: None
- **Plan**: [plans/03_b2-fuel-sufficiency.md]

**Description**: Fill the propositional tableau completeness sorries (7 real sorries; soundness is already sorry-free after task 316). The open obligations are the truth-lemma / countermodel-extraction proofs in the three Completeness modules. Classical (Tableau/Classical/Completeness.lean): classicalExpandBranches_hintikka (line ~462) -- note the module's separate build break (bad Mathlib lemma ref + unsolved goals) is repaired first under task 363. Intuitionistic (Tableau/Intuitionistic/Completeness.lean): intTruthLemma (line ~89), intuitionisticOpenBranch_countermodel (~98), intuitionisticTableau_complete (~112). Minimal (Tableau/Minimal/Completeness.lean): minTruthLemma (~168), minOpenBranch_countermodel (~179), minimalTableau_complete (~190). Core technique: Hintikka-set argument -- a saturated open branch satisfies Hintikka conditions, from which a countermodel is extracted (a Boolean valuation for classical; a finite Kripke model for intuitionistic/minimal) and a truth lemma by formula induction matches forced/not-forced to the signed formulas at each world. Because task 369 parameterizes the intuitionistic and minimal tableau over (closurePred, modelBot), the int and min cases should be discharged ONCE as a single parametric truth-lemma/countermodel pair rather than duplicated. The tableau Decidable instances become genuinely sorry-free once these land. No new axioms; CI green (lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake). Depends on 316, 323, 363, 369.

---

### 301. Temporal tableau
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 426, Task 425
- **Research**: [301_temporal_tableau/reports/01_temporal-tableau-decision-procedure.md]
- **Plan**: [301_temporal_tableau/plans/01_temporal-tableau-decision-procedure.md]

**Description**: Implement tableau decision procedure for temporal logic (Cslib.Logic.Temporal.Formula) with until/since decomposition rules, time labels, and temporal ordering tracking. Most complex new tableau: until/since rules have no modal analogue, requiring branching decomposition with event-witness and guard-continue alternatives. Adapt patterns from bimodal decidability system (TimeOrdering, temporal rule structure, frame-class rules) but build fresh implementations on shared Foundations infrastructure. Include density and discreteness frame-class rules. Formula type has atom, bot, imp, untl, snce primitives using Lukasiewicz encoding. Files under Cslib/Logics/Temporal/Tableau/: Defs.lean, Rules.lean, TimeOrdering.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 2,000-2,500 lines.

---

### 300. Modal extensions t s4 s5
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 299

**Description**: Extend modal K tableau (task 299) with frame-specific rules for reflexive (T), transitive (S4), and equivalence-relation (S5) frames. T: reflexivity rule (box phi at w implies phi at w). S4: transitivity-aware propagation with loop-checking for termination. S5: equivalence-class simplification (mirrors bimodal approach). Include rules for B (symmetric) and 5 (Euclidean) to cover full modal cube. Each extension needs own completeness proof showing extracted countermodel satisfies frame condition. Files: FrameRules.lean, LoopChecking.lean, S5Simplification.lean, FrameSoundness.lean, FrameCompleteness.lean. Estimated: 1,200-1,800 lines.

---

### 299. Modal k tableau
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 442
- **Research**:
  - [299_modal_k_tableau/reports/03_completeness-decomposition.md]
  - [299_modal_k_tableau/reports/04_truth-lemma-architecture.md]
- **Plan**: [299_modal_k_tableau/plans/05_modal-k-tableau-plan.md]

**Description**: Implement tableau decision procedure for basic modal logic K with world labels, box/diamond rules on top of propositional rules from shared infrastructure. Introduces world labels (accessibility relation tracking) and fundamental modal rule pattern: box-positive is universal/persistent, diamond-positive is existential (fresh accessible world). Use Lukasiewicz encoding for and/or. Prove soundness against Kripke semantics and completeness by extracting finite Kripke countermodels. Modal formula type: Cslib.Logic.Modal.Formula with atom, bot, imp, box primitives. Files under Cslib/Logics/Modal/Tableau/: Defs.lean, Rules.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 1,500-2,000 lines.

---

### 296. Tableau calculi architecture
- **Status**: [EXPANDED]
- **Task Type**: formal
- **Topic**: Foundations
- **Dependencies**: None
- **Research**: [296_tableau_calculi_architecture/reports/01_tableau-arch-research.md]
- **Plan**: [296_tableau_calculi_architecture/plans/01_tableau-arch-plan.md]

**Description**: Research and design a unified tableau calculi architecture for CSLib spanning propositional, modal, temporal, and bimodal logics. The existing PropositionalTableau.lean provides generic rule infrastructure (PropSign, PropSignedFormula, PropTableauRule, applyPropRule) already consumed by the bimodal decidability system (~5,900 lines). The goal is to determine how to build a complete propositional tableau system (branch construction, closure, termination, soundness, completeness, decision procedure) that naturally extends to modal and temporal tableau systems, sharing resources with and relating cleanly to the existing bimodal tableau. Investigate: (1) what generic tableau infrastructure should live in Foundations/ vs logic-specific modules, (2) how modal tableau rules (box/diamond) and temporal rules (until/since) layer on top of propositional rules, (3) whether the bimodal tableau can be refactored to consume shared infrastructure or whether it should remain standalone, (4) what the dependency chain should be between propositional, modal, temporal tableau tasks, (5) how tableau completeness relates to the existing MCS-based completeness proofs and the planned sequent calculus (task 279). Output: a set of precisely scoped implementation tasks with dependency graph covering the full tableau pipeline from propositional through bimodal.

---

### 279. Propositional sequent calculus lk lj
- **Status**: [EXPANDED]
- **Task Type**: cslib
- **Topic**: PL-Base
- **Dependencies**: None
- **Research**:
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-a-findings.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_team-research.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-b-findings.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-c-findings.md]
  - [279_propositional_sequent_calculus_lk_lj/reports/01_teammate-d-findings.md]
- **Plan**: [279_propositional_sequent_calculus_lk_lj/plans/02_sequent-calculus-plan.md]

**Description**: Implement a two-sided Gentzen-style sequent calculus (LK for classical, LJ for intuitionistic) for propositional logic with cut elimination. Use Finset-based contexts on both sides, following the CLL sequent calculus in Cslib/Logics/LinearLogic/CLL/Basic.lean as a template. Prove soundness, completeness, cut elimination (Hauptsatz), and equivalence bridges to the existing Hilbert and natural deduction systems (hilbert_iff_lk, nd_iff_lk). This completes the proof-system triad (Hilbert + ND + SC) for propositional logic and would be the first LK/LJ formalization in Lean 4.

---

### 278. Simplify proofs with normalization tags
- **Status**: [EXPANDED]
- **Task Type**: cslib
- **Topic**: Foundations
- **Dependencies**: Task 41, Task 180, Task 181, Task 299, Task 301, Task 317, Task 321, Task 370, Task 375

**Description**: Simplify proofs using new simp/grind normalization tags. After task 268 adds @[simp, scoped grind =] tags to Hilbert system definitional lemmas, audit all proofs in Propositional/, Modal/, Temporal/, and Bimodal/ that use manual `simp only [listImp_nil, listImp_cons, bigconj_nil, ...]` or verbose tactic chains involving these normalization lemmas. Replace with `grind` or `simp` where the new tags make the explicit lemma lists redundant. Also check Foundations/Logic/ proofs. Must pass lake build, lake test, lake exe checkInitImports, lake exe lint-style, lake shake

---

### 226. Propositional semantics upstream pr
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: PL-Semantics
- **Dependencies**: None
- **Research**:
  - [226_propositional_semantics_upstream_pr/reports/01_upstream-pr-research.md]
  - [226_propositional_semantics_upstream_pr/reports/02_three-way-comparison.md]

**Description**: Cherry-pick propositional semantics from the local codebase into a <500 LOC follow-up PR stacked on PR #648. PR #648 contributes the formula type and natural deduction; this follow-up adds the semantics layer. Scope: (1) Semantics/Algebra.lean — GHA evaluation with bot_val parameter for minimal/intuitionistic/classical logic. (2) Semantics/Bool.lean — BoolEvaluate with bridge to AlgEvaluate. (3) Semantics/SemanticConsequence.lean — semantic consequence and tautology definitions. (4) Semantics/Kripke.lean — Kripke semantics with botForces for minimal logic (include if LOC budget permits). All four files already exist locally with full implementations. Task is to select, trim, and package for upstream submission. Ensure lake build, lake test, lake exe checkInitImports, lake exe lint-style, and lake shake all pass on the PR branch. Write PR description referencing the Zulip Propositional Logic thread.

---

### 215. Fill sorry declarations in Bimodal BXCanonical and Bundle files
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: Task 36, Task 37
- **Research**: [215_fill_bimodal_sorries/reports/01_sorry-analysis.md]

**Description**: Fill 20 sorry declarations across 5 files in Cslib/Logics/Bimodal/Metalogic/:
- Bundle/SuccRelation.lean: 7 sorries (lines 253, 258, 263, 269, 275, 281, 285)
- BXCanonical/Chronicle/ChronicleToCountermodel.lean: 10 sorries (lines 66, 143, 144, 147, 153, 157, 163, 171, 172, 177)
- Bundle/UntilSinceCoherence.lean: 2 sorries (lines 37, 41)
- BXCanonical/Frame.lean: 1 sorry (line 159)

Note: countermodel_dense (ChronicleToCountermodelBasic.lean:825) and completeness_dense (Dense.lean:122) carved off to task 231.

9 sorries blocked on task 37 (strict Until/Since semantics gap: BX8/BX9/temporal-T axioms removed as unsound). 11 sorries blocked on task 36 (discrete completeness pipeline requires unported GoodStructuresModelSurgery infrastructure).

---

### 181. Bimodal primitive dia always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Porting
- **Dependencies**: Task 180
- **Research**: [181_bimodal_primitive_dia_always_historically/reports/01_bimodal-primitive-expansion-research.md]

**Description**: Propagate primitive diamond, allFuture, and allPast constructors to the Bimodal layer, giving {atom, bot, imp, and, or, box, dia, untl, snce, allFuture, allPast} (11 primitives). This is the union of Modal (task 179) and Temporal (task 180) primitive sets. Scope: (1) Syntax/Formula.lean: add .dia/.allFuture/.allPast constructors, update all match cases. (2) Semantics/Truth.lean: structural truthAt clauses. (3) ProofSystem: axiom constructors for diamond duality and G/H axioms. (4) Embedding: extend ModalEmbedding (.dia), TemporalEmbedding (.allFuture/.allPast). (5) Metalogic: propagate through ~50 files (Core, Soundness, Completeness, BXCanonical, ConservativeExtension, Separation, Decidability, Algebraic). Follow task 177 playbook. (6) Classical equivalences become theorems. Verify full CI. Estimated ~50 files, ~2000 lines, similar scope to task 177.

---

### 180. Temporal primitive always historically
- **Status**: [PR READY]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: None
- **Research**:
  - [180_temporal_primitive_always_historically/reports/01_primitive-always-historically-research.md]
  - [180_temporal_primitive_always_historically/reports/02_implementation-attempt-status.md]
  - [180_temporal_primitive_always_historically/reports/03_metalogic-obligations-research.md]
- **Plan**: [180_temporal_primitive_always_historically/plans/03_primitive-gh-metalogic-plan.md]

**Description**: Add allFuture (G) and allPast (H) as primitive constructors to Temporal.Formula, giving {atom, bot, imp, and, or, untl, snce, allFuture, allPast}. Currently G is derived as neg(someFuture(neg phi)) and H as neg(somePast(neg phi)), which are only valid classically. Making them primitive enables intuitionistic temporal logics. Note: someFuture (F) and somePast (P) remain derivable without negation (F = top U phi, P = top S phi). Scope: (1) Syntax/Formula.lean: add .allFuture/.allPast constructors, update complexity, subst, atoms, encodeNat, temporalDepth, swapTemporal. (2) Semantics: structural clauses for universal future/past quantification. (3) ProofSystem: temporal axioms referencing G/H now use primitive constructors. (4) Metalogic: cases in Soundness, Chronicle/TruthLemma, MCS, Completeness. (5) Classical equivalences become theorems. Verify full CI. Reference: Boudou et al. for intuitionistic temporal logic.

---

### 41. Abstract completeness infrastructure
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Foundations
- **Dependencies**: Task 39, Task 40

**Description**: Abstract shared completeness infrastructure between temporal and bimodal logic once concrete completeness proofs are finished for both.

The temporal (tasks 31, 38, 39) and bimodal (tasks 34, 35) completeness proofs share structural patterns that can be factored into a generic completeness scaffold in Cslib/Foundations/Logic/Metalogic/, extending the existing generic MCS framework (Task 29).

Candidate abstractions (to be confirmed once concrete implementations exist):
1. Generic neg_consistent_of_not_derivable: if φ is not derivable then {¬φ} is consistent — identical structure in both logics, parameterized over DerivationSystem
2. Generic completeness contrapositive skeleton: not derivable → consistent → Lindenbaum → MCS → canonical model → countermodel — the overall proof shape is shared
3. Dense/discrete case split pattern: the three-way case split on □(F'T) / □(U(T,⊥)) / mixed is structurally similar (temporal uses G/H instead of □)
4. Canonical order construction patterns: both define canonical_lt via G-sets (temporal) or box-sets (bimodal); the linearity/irreflexivity/transitivity proofs follow parallel structures
5. Dense indicator elimination: both dense completeness proofs eliminate the non-dense branch by showing the dense indicator axiom is a theorem — identical pattern

Scope: Identify which abstractions yield genuine code savings vs. premature generalization, implement those that do, and refactor both temporal and bimodal completeness to use the shared infrastructure.

Target: Cslib/Foundations/Logic/Metalogic/Completeness.lean (or similar)
Depends on: Tasks 35 (dense bimodal), 38 (dense temporal), 39 (discrete temporal) — transitively includes 31 (base temporal) and 34 (base bimodal MCS)

---

### 40. Temporal continuous completeness
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 37

**Description**: Continuous temporal completeness: completeness for temporal logic over Dedekind-complete (continuous) linear orders, e.g. the reals.

Scope: Define a Continuous frame class extending Dense, add any required axioms (e.g., Dedekind completeness schema or equivalent), prove soundness over conditionally complete linear orders, prove completeness via canonical model on Real or equivalent.

Blocked: The continuous case has not been developed for either the temporal or bimodal logic upstream. Requires foundational research into which additional axioms (if any) are needed beyond density to characterize continuous time. The standard result (Burgess 1982) is that the Until/Since temporal logic over the reals has the same theorems as over the rationals (density suffices), which would make this task trivial — but this equivalence itself needs to be formalized.

Target: Cslib/Logics/Temporal/Metalogic/ContinuousCompleteness.lean
Blocker: Research needed on whether continuous frames require additional axioms beyond density

---

### 39. Temporal discrete completeness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Temporal Logic
- **Dependencies**: Task 36

**Description**: Discrete temporal completeness: prove that every formula valid on all discrete serial linear orders is derivable in the Discrete temporal proof system.

Scope:
1. Add discrete-specific axioms to Temporal.Axiom: `prior_UZ` (F(φ) → U(φ,¬φ)), `prior_SZ` (P(φ) → S(φ,¬φ)), `z1` (G(Gφ→φ) → (F(Gφ)→Gφ)), and discrete uniformity axioms (discrete_symm_fwd/bwd, discrete_propagate_fwd/bwd), gated to FrameClass.Discrete via minFrameClass.
2. Prove discrete soundness: each discrete axiom valid on SuccOrder+PredOrder+IsSuccArchimedean.
3. Prove discrete completeness via contrapositive + MCS + canonical model on Int. The non-discrete branch is eliminated by deriving U(⊤,⊥) as a Discrete theorem.

New development (not a port). The canonical model specializes the base temporal canonical order to Int. The discrete uniformity axioms (minus discrete_box_necessity which is bimodal-only) ensure U(⊤,⊥) propagates uniformly.

Target: Cslib/Logics/Temporal/Metalogic/DiscreteCompleteness.lean + axiom additions to Axioms.lean
Estimated scope: ~500-700 lines (new axioms + discrete soundness + discrete completeness)

---

### 37. Port continuous completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task BimodalLogic:continuous_extension

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic. This task is blocked pending upstream development of continuous frame completeness.

**Source**: Not yet developed in BimodalLogic
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic continuous extension development
**Parent task**: 8 (expanded)

---

### 36. Port discrete completeness bimodal
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: Bimodal Porting
- **Dependencies**: Task BimodalLogic:discrete_sorry_elimination

**Description**: Port discrete completeness (completeness_discrete theorem) and WeakCanonical/IntegerModel/ infrastructure (~6 files). The discrete branch constructs countermodels on Int via the Reynolds pipeline. Currently blocked: upstream BimodalLogic has sorryAx tracing through chronicle_gap_contradiction → succ_cofinal → limitDomSubtype_isSuccArchimedean → succ_embed_surjective. Port after upstream sorry elimination completes.

**Source**: BimodalLogic/Theories/Bimodal/Metalogic/WeakCanonical/IntegerModel/ (~6 files), discrete branch of BXCanonical/Completeness.lean
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic discrete completeness sorry elimination (36 sorries across IntegerModel/)
**Parent task**: 8 (expanded)
