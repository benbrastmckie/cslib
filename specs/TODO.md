---
next_project_number: 625
---

# TODO

## Task Order

*Updated 2026-08-10. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 36,37,181,300,425,497,534,554,568,569,590,594,599,600,607,608,610,612,613,614,615,616,617,618,619,620,623,624 | -- | propositional logic, modal logic, temporal logic, ... |
| 2 | 39,40,215,301,450,537,551,571,576,588,589,595,611,621 | 36,37,181,425,534,554,568,594,610,620 | propositional logic, modal logic, temporal logic, ... |
| 3 | 41 | 39,40 | foundations |

**Grouped by Topic** (indented = depends on parent):

### Foundations

41 [NOT STARTED] — Abstract shared completeness infrastructure between temporal and 

### Propositional Logic

497 [RESEARCHED] — [RETARGETED 2026-08-10 — this task is NO LONGER an identifier ren
614 [NOT STARTED] — Give `ctxToImp` a computable definition so the four context-based
615 [NOT STARTED] — Add algebraic semantic validity as a further equivalent node in t
616 [NOT STARTED] — Repair the stale and self-contradictory documentation layer in th
617 [NOT STARTED] — CRITICAL. Library consumers importing `Cslib` receive a `Decidabl
618 [NOT STARTED] — Close the remaining coverage gaps in the propositional metatheory
619 [NOT STARTED] — Reconcile this fork's `Cslib/Foundations/Logic/Connectives.lean` 
620 [NOT STARTED] — Rebase the open PR #648 ("feat(Logics/Propositional): five-primit
  └─ 621 [NOT STARTED] — Change this fork's five `Cslib/Logics/Propositional/Defs.lean` co
623 [RESEARCHED] — The intuitionistic tableau sub-barrel `Cslib/Logics/Propositional

### Modal Logic

300 [BLOCKED] — Umbrella task for modal frame extensions T/S4/S5 (and the derived
534 [NOT STARTED] — COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree 
  └─ 588 [NOT STARTED] — Resolve the five import-reachability duplicate families in Cslib/
554 [BLOCKED] — [RESCOPED 2026-07-26 by explicit user decision, adopting report 0
  └─ 537 [BLOCKED] — Prove the general labelled SOUNDNESS direction nik_TS5_soundness 
  └─ 551 [BLOCKED] — Deliver NATIVE Hilbert canonical-model completeness for construct
590 [NOT STARTED] — Re-establish the six out-of-tree probe verdicts under a dedicated
599 [NOT STARTED] — Prototype the Euclidean rule combinator identified as an open, un
600 [NOT STARTED] — Retire the unordered S4 stepper stack at Cslib/Logics/Modal/Table
610 [NOT STARTED] — Wire the D (serial) corner through to a `Decidable` instance. The
  └─ 611 [NOT STARTED] — Correct the decidability-matrix documentation block in `Cslib/Log

### Temporal Logic

425 [NOT STARTED] — [Decomposed from the temporal tableau umbrella, blocker C.] BLOCK
  └─ 301 [BLOCKED] — Implement tableau decision procedure for temporal logic (Cslib.Lo
569 [NOT STARTED] — [Created by the blocked-task review to break a two-task deadlock.
39 [NOT STARTED] — Discrete temporal completeness: prove that every formula valid on
40 [BLOCKED] — Continuous temporal completeness: completeness for temporal logic

### Bimodal Logic

36 [NOT STARTED] — Port discrete completeness (completeness_discrete) from upstream 
  └─ 215 [BLOCKED] — Fill the discrete-gated sorry declarations in Cslib/Logics/Bimoda
37 [BLOCKED] — Port continuous extension completeness once developed upstream. T
  └─ 571 [BLOCKED] — [Carved off the bimodal sorry task by the blocked-task review. Ho
181 [NOT STARTED] — Propagate primitive diamond, allFuture, and allPast constructors 
  └─ 450 [NOT STARTED] — Core corrected conservativity result. PR-BLOCKING for task 180. S

### Bimodal And Temporal Logic

568 [BLOCKED] — [Follow-on created by the blocked-task review, at explicit user r
  └─ 576 [NOT STARTED] — Resolve the `namespace Chronicle` / `structure Chronicle` NAME CO

### Code Hygiene

613 [NOT STARTED] — Fix the two unusedDecidableInType lint warnings in Cslib/Logics/P
589 [NOT STARTED] — Fix repo-wide unusedArguments lint findings across the Lean sourc

### Agent System

594 [NOT STARTED] — METATASK. Bring all open task records in specs/state.json into ag
  └─ 595 [NOT STARTED] — Build the validation gate that would have caught the task-graph f
608 [NOT STARTED] — Discovered during task 596's ROADMAP realignment (2026-08-09; see
612 [NOT STARTED] — Batch of small, independent corrections surfaced by the 2026-08-0

### Bimodal Metalogic

607 [NOT STARTED] — Tracked decision (created by task 596's ROADMAP realignment, per 

### Documentation

624 [RESEARCHED] — Document that `lake env lean <file>` is unsafe for module-system 

## Tasks

### 624. Document that lake env lean skips --setup and is unsafe for module-system files
- **Status**: [RESEARCHED]
- **Task Type**: markdown
- **Topic**: Documentation
- **Dependencies**: None
- **Research**: [624_document_lake_env_lean_hazard/reports/01_lake-env-lean-hazard-doc-home.md]

**Description**: Document that `lake env lean <file>` is unsafe for module-system files in this repository, and
that `lake build <Module.Name>` is the correct way to build a single module.

=== OBSERVED ===

A bare `lake env lean Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` DIVERGES —
it was killed after 19 minutes at ~101-128% CPU with RSS pinned at 1,340,544 KB and no diagnostic.
The identical invocation WITH Lake's `--setup` argument
(`lake env lean --setup Scheme.setup.json Scheme.lean`) exits 0 in 23.78 s. `lake build` always
passes `--setup`; `lake env lean` never does. Without it, Lean 4.33's module system lacks the
`module`/`public import` exposure configuration and elaboration blows up.

Two further hazards of the same command: it bypasses dependency resolution, so it happily
consumes stale `.olean` files from earlier builds; and without `-o` it never writes an `.olean`,
so the absence of one after a run is a property of the command line and NOT evidence that the
module has never built.

=== WHY IT MATTERS ===

Every one of those symptoms reads exactly like a pathological or non-terminating file. The
missing-`.olean` detail in particular inverts cleanly into a false conclusion. A contributor
reaching for the obvious single-file build command gets a convincing false positive with no
diagnostic pointing at the command itself.

=== SUGGESTED APPROACH ===

Add a short subsection to the contributor-facing build documentation (check `CONTRIBUTING.md`
first for the right home) stating the rule, the failure signature, and the correct alternative.
Keep it symptom-first so a contributor mid-hang can match what they are seeing.

=== PROVENANCE ===

Surfaced during the Scheme.lean build investigation (task 622), which established this as the
actual root cause of a reported 92-minute stall. The research explicitly recommended NOT bundling
this into that task's closure.

---

### 623. Reconcile Intuitionistic.lean sub-barrel omitting Scheme while Cslib.lean imports it directly
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [623_intuitionistic_barrel_omits_scheme/reports/01_barrel-scheme-omission.md]

**Description**: The intuitionistic tableau sub-barrel `Cslib/Logics/Propositional/Tableau/Intuitionistic.lean` omits the `Scheme` module, even though `Cslib.lean:636` imports it directly with `public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`.

=== OBSERVED ===

`Intuitionistic.lean` currently carries five `public import` lines — Rules, Expansion, Soundness,
Completeness, DecisionProcedure — and no `Scheme`. The root barrel `Cslib.lean` imports `Scheme`
directly instead, so the module IS reachable and the tree builds green; this is a consistency
gap, not a build break.

=== WHY IT MATTERS ===

A reader importing the sub-barrel `Cslib.Logics.Propositional.Tableau.Intuitionistic` gets four
of the five siblings plus `Completeness` — which itself carries `public import ...Scheme` — so
`Scheme` arrives transitively and invisibly rather than by declaration. Anyone pruning
`Completeness`'s imports would silently drop `Scheme` from the sub-barrel's surface.

=== SUGGESTED APPROACH ===

Decide which is intended and make it explicit: either add `public import
Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` to the sub-barrel (and consider
dropping the direct line from `Cslib.lean` if sub-barrels are the convention), or record why
`Scheme` is deliberately excluded. Check sibling barrels under `Cslib/Logics/` for the prevailing
convention before choosing.

=== PROVENANCE ===

Surfaced incidentally during the Scheme.lean build investigation (task 622), which the research
explicitly recommended NOT bundling into that task's closure. Independent of that task's
NOT-A-BUG verdict.

---

### 622. Investigate why Tableau/Intuitionistic/Scheme.lean never completes a build, blocking full lake build
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**: [622_investigate_scheme_build_stall/reports/01_scheme-build-stall-root-cause.md]

**Description**: A full `lake build` on `main` does not complete. It stalls indefinitely while elaborating
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`.

=== OBSERVED, 2026-08-10 ===

Discovered incidentally while build-testing a connective-notation change; the stall is NOT
caused by that change (the change was to `Propositional/Defs.lean` and was reverted; the stall
reproduces independently of it).

  - Single `lean` worker pegged at ~101% CPU for 92 minutes with no completion.
  - Resident memory ~1.3 GB and stable (not obviously an unbounded leak).
  - The file is 9,884 lines with ~485 connective-notation occurrences.
  - NO cached `.olean` exists for this module anywhere under `.lake/build` — i.e. it has never
    successfully built in this checkout, as opposed to being merely stale.
  - It sits in `namespace Cslib.Logic.PL` and opens `Cslib.Logic.Tableau`; it is a
    single-logic-namespace file, so multi-namespace notation overloading is not implicated.

The build was terminated with SIGTERM (`lake` exit 143) rather than allowed to finish, so the
upper bound on elaboration time is unknown — it may be very slow rather than truly
non-terminating. Distinguishing "pathologically slow" from "diverges" is the first thing to
establish.

=== WHY IT MATTERS ===

`lake build` is step 1 of the CSLib CI verification order, so a tree that cannot complete it
cannot pass CI. Any task requiring final green-build verification is gated behind this, including
the propositional-notation reconciliation work. Targeted per-module builds (`lake build
Module.Name`) still work and are unaffected, which is why this has not blocked day-to-day work
and may have gone unnoticed.

=== SUGGESTED STARTING POINTS ===

  - Establish termination: run the single module with a generous wall clock and
    `set_option maxHeartbeats 0` behaviour characterised, to separate slow from divergent.
  - Profile it: `lean_profile_proof` on the heaviest declarations, or `set_option profiler true`,
    to find the hot declaration rather than guessing.
  - Check `set_option maxHeartbeats` / `maxRecDepth` overrides already present in the file, which
    could be masking a runaway elaboration.
  - Determine whether the module is reachable from the `Cslib.lean` barrel import, and whether it
    is new/unfinished work that was never green rather than a regression.
  - Bisect against history if it ever built: `git log --follow` the file and test an older
    revision.

=== SCOPE NOTE ===

`file_scope` is set to the single stalling file, which is where investigation starts. If the root
cause turns out to be in a dependency (e.g. the shared `Tableau` infrastructure), widen it then
rather than assuming it now.

---

### 621. Switch the five Propositional connective notations from infix to infixr at upstream precedences
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 620

**Description**: Change this fork's five `Cslib/Logics/Propositional/Defs.lean` connective notation declarations from non-associative `infix` to right-associative `infixr` at upstream's precedences.

SOURCE: `specs/400_reconcile_connectives_pr607/reports/03_falsum-representation-decision.md` §6, filed there as an independent finding to act on REGARDLESS of the falsum decision.

=== THE DIVERGENCE ===

  fork:     and infix:36,  or infix:35,  imp infix:30,  iff infix:20,  not prefix:40
  upstream: and infixr:36, or infixr:30, imp infixr:25, iff infixr:20, not notation:max

Relative precedence ORDERING is preserved between fork and upstream; the associativity is not.

=== WHY IT MATTERS ===

Empirically verified: `a -> b` parses and `a -> (b -> c)` parses, but `a -> b -> c`, `a AND b AND c`, and `a OR b OR c` ALL FAIL in the fork. This is not confined to the arrow — all five connectives are affected.

The failure mode is the hazard: because the fork's notations are non-associative, Lean's own Prop-level `And`/`Or`/`->` win the overload, so a chained expression surfaces as a TYPE MISMATCH rather than a notation error. That is materially harder to diagnose than a parse failure would be.

=== SCOPE ===

Low-risk, self-contained, orthogonal to falsum. Verify with `lake build` that the tree stays green; expect to fix any sites that relied on the old non-associative parse.

=== ORDERING CONSTRAINT (why this depends on the PR #648 rebase) ===

This task edits `Propositional/Defs.lean`, which is also in the #648 rebase's file scope. #648 carries a STANDING APPROVAL against a specific approved scope, and the decision report is explicit that widening that scope forfeits the approval. Landing a notation change into Defs.lean before the rebase risks polluting the approved diff. Sequence it after.

---

### 620. Rebase PR #648 onto current upstream and clear the stale blocking review
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Rebase the open PR #648 ("feat(Logics/Propositional): five-primitive formula type with primitive bot") onto current `upstream/main` and clear ctchou's stale blocking review.

SOURCE: `specs/400_reconcile_connectives_pr607/reports/03_falsum-representation-decision.md` §5, which recommends REWORK AND REBASE — explicitly not close, not leave pending.

=== WHY THE PR IS NOT ACTUALLY OPPOSED ===

Review record (verified read-only 2026-08-10):
  2026-06-15  ctchou         CHANGES_REQUESTED
  2026-07-06  thomaskwaring  APPROVED
  2026-07-13  benbrastmckie  COMMENTED x5 (answering all five inline comments)

thomaskwaring APPROVED after a Zulip compromise (2026-06-28: "if we are going to have bot as a primitive, we should also have efq") that was implemented 2026-06-29. His approval STANDS and should be cited, not re-litigated.

ctchou's is the only outstanding blocking review. Its FIRST bullet reads verbatim: "I like the idea of adding \bot as a primitive." Its four points are procedural: file organization (why both Semantics/Basic.lean and Semantics/Bool.lean), references (prefer Avigad's textbook over 1930s German sources), and "You should definitely coordinate this PR with #607 and #587. #536 is ready to merge, so you should wait for it." That coordination instruction is now ACTIONABLE — #607 merged 2026-08-03.

There is NO standing technical opposition to primitive bot on the record. A third participant (Matthew Doty) independently backed it on DPLL grounds.

=== SCOPE: KEEP EXACTLY AS APPROVED ===

Four files, ungated efq, IPL base, minimal logic deferred.

Do NOT widen to the fork's current `[IsIntuitionistic T]`-gated efq design. That is the deferred fragment work thomaskwaring explicitly agreed to postpone; widening it FORFEITS a standing approval. It belongs in a follow-up PR.

=== WHAT THE REBASE MUST ABSORB ===

1. Toolchain and Mathlib pin bump: fork pins `leanprover/lean4:v4.33.0-rc1` and Mathlib `169c26b5`; upstream is at `v4.33.0` for both. One release-candidate of drift.
2. PR #753's InferenceSystem/Congruence framework refactor (commit 3491c629).
3. IsIntuitionistic/IsClassical SHAPE RECONCILIATION. The fork's `Propositional/Defs.lean` does not import InferenceSystem and states these as theory-membership predicates (`(bot -> A) in T`, Defs.lean:166,175); upstream states them over an inference system (`S-down-arrow`, `[InferenceSystem S (Proposition Atom)]`). #648 had ALREADY reconciled this against #536; the fork's main has since drifted BACK. 80 files in the fork reference InferenceSystem — just not from Propositional/Defs.lean.

=== THEN ===

Re-request review from ctchou, itemising the four dispositions.

=== HARD CONSTRAINTS ===

- The GitHub text MUST be HUMAN-AUTHORED per the CSLib AI policy (Chris Henson formally challenged an LLM-drafted message on this exact Zulip topic, near/605827029). An agent may produce factual scaffolding — dispositions, diffs, tables — but never finished prose to paste.
- NO agent-initiated push, `gh pr` write, or Zulip post. Per `.claude/rules/pr-prohibition.md`, only user-invoked commands may push or post.

---

### 619. Reconcile Foundations/Logic/Connectives.lean against merged upstream Operators.lean
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Reconcile this fork's `Cslib/Foundations/Logic/Connectives.lean` against the `Cslib/Foundations/Logic/Operators.lean` that merged upstream in PR #607 (commit b8ad3923).

SOURCE: the falsum representation decision report, `specs/400_reconcile_connectives_pr607/reports/03_falsum-representation-decision.md`, which identified this as required under EVERY option considered there (adapt, re-argue, or diverge) and INDEPENDENT of the falsum question. It is not contingent on the Option B decision.

=== THE COLLISION ===

Four classes are duplicated in namespace `Cslib.Logic` between the fork's Connectives.lean and merged Operators.lean:
  HasAnd, HasOr, HasImp, HasBox

Upstream additionally defines: HasIff, HasNot, HasDiamond.
The fork names its own `HasDia` where upstream says `HasDiamond` — a naming divergence, not merely a duplicate.

=== WHY THIS MATTERS NOW ===

Prerequisite for PR #649 (LTL), which is stacked on #648 and whose changed files include `Foundations/Logic/Connectives.lean`. #649 cannot land cleanly while the duplication stands.

=== SCOPE ===

Decide, per class, whether to drop the fork's definition in favour of upstream's, keep the fork's under a distinct name, or upstream a delta. Resolve `HasDia` vs `HasDiamond` explicitly. Verify with `lake build` that the tree stays green.

Do NOT fold the falsum representation question into this task — it is settled (keep primitive bot) and orthogonal.

=== CONSTRAINT ===

No GitHub or Zulip post may be authored by an agent (CSLib AI policy; Chris Henson formally challenged an LLM-drafted message on the Propositional Logic topic, near/605827029). If outward communication is needed, produce a factual scaffolding file for a human to adapt.

---

### 618. Propositional coverage gaps and ordering overclaim
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Close the remaining coverage gaps in the propositional metatheory, and correct the one docstring that overclaims a result the tree does not prove.

SURFACED BY: the 2026-08-10 propositional review (specs/reviews/review-2026-08-10.md, findings H3 and M4), from a full coverage matrix over {CPL, IPL, MPL} x {Hilbert, ND, sequent, tableau, algebraic, fragments}. Every item below is a MISSING theorem, not a broken one -- the subsystem is sorry-free and axiom-clean (1827 declarations scanned, 0 tainted).

=== PART A (DO FIRST -- correctness of the record, not new mathematics) ===

A1. `Semantics/Algebra/ConservativeChain.lean:140` claims the five Hilbert systems are "**strictly ordered**" by derivability. FALSE AS STATED: `derivability_subsumption_chain` proves ONE-WAY SUBSUMPTION over three displayed nodes. Strictness is never proved, and an exhaustive search found NO properness or separation result anywhere in the tree -- nothing establishes MPL != IPL != CPL. Correct the docstring to say "ordered". Do this regardless of whether Part D is ever undertaken; do not leave the overclaim standing pending future work.

A2. `Tableau/Classical/DecisionProcedure.lean:23` lists `instDecidableDerivable` under "Main Results". NO SUCH INSTANCE EXISTS -- the same file explicitly declines it at :92-94. Remove the stale entry from the Main Results list.

A3. `Tableau/Intuitionistic/DecisionProcedure.lean:62` claims the instance "feeds the modal/temporal/bimodal extensions". It has ZERO consumers outside Cslib/Logics/Propositional/ (verified by grep; `IValid` hits under Modal/ are a DIFFERENT `IValid` from Birelational.lean). Correct or drop the claim.

A4. `CslibTests/TableauConformance.lean:34-35` states in the present tense that "the completeness theorems the driver would need do not exist yet for either calculus". They exist and are sorry-free (`intuitionisticTableau_complete`, `intuitionisticTableau_decides`). Re-tense.

A5. `Tableau/Minimal/DecisionProcedure.lean:119` says "`MValid φ` is decidable" where the statement is `MValid.{_, 0} φ`. Add the pin.

=== PART B (CHEAP WINS -- ingredients already exist) ===

B1. G10 -- LJ cut-free completeness. LK has `lkCutFreeCompleteness`/`lkCutFreeIffTautology` (LK/CutFreeCompleteness.lean:35,45); LJ has no counterpart. Both ingredients exist: `lj_iff_ivalid` (LJ/Completeness.lean:288) and `LJProof.cutElim` (LJ/CutElimination.lean:678). Essentially a composition. Target: `SequentCalculus/LJ/CutFreeCompleteness.lean`.

B2. G5 -- the GENERAL split-interpolation lemma over arbitrary cover partitions is already PROVED but `private`: `maeharaCore` (LK/Interpolation.lean:62) and `ljMaeharaCore` (LJ/Interpolation.lean:68). Only the empty-context implication form is public (`LKProof.interpolation` :863, `LJProof.interpolation` :560). Making the general form public requires NO NEW PROOF -- only a decision about the public API shape and a docstring.

B3. G4 -- LM decidability. Missing `Decidable (Nonempty (SeqProofMinimal (Γ ⊢ A)))` and `instDecidableDerivableInMPL`. LOW difficulty: `instDecidableMValid` already exists (Minimal/DecisionProcedure.lean:123), `listToImp`/`ctxToImp` are reusable (LJ/Decidability.lean:72,82), and `instDecidableLJDerivable` (:197) is a direct template. NOTE: coordinate with the computable-ctxToImp task -- if that lands first, build this on the computable route rather than inheriting the `noncomputable` taint.

=== PART C (LM PARITY -- the real remaining work) ===

STRUCTURAL FINDING: LM has only Basic/Soundness/Completeness (3 modules) against LJs 6 and LKs 8. `LM.lean` imports only those three. Note LMs soundness is strictly MORE general than LJs (arbitrary upward-closed `bot_forces`, LM/Soundness.lean:61), so this is a genuine gap in coverage, not a deliberate descoping.

C1. G1 -- LM cut elimination. Target `SequentCalculus/LM/CutElimination.lean`. PROMISING ROUTE: LJs proof (LJ/CutElimination.lean, 715 lines, `ljCutAdmissibility`:659) is already written over `SeqProof T` GENERICALLY, and `SeqProofMinimal = SeqProof MPL` is that same inductive at a different theory -- so much of it may generalize by abstracting `T` rather than being rewritten. Measure this before committing to a bespoke proof.
C2. G2 -- LM subformula property. Target `SequentCalculus/LM/SubformulaProperty.lean`. `SeqProof.formulas` (LJ/SubformulaProperty.lean:50) is ALREADY generic over `T`, so the collection function needs no work. Depends on C1.
C3. G3 -- LM Craig interpolation. Target `SequentCalculus/LM/Interpolation.lean`. Depends on C1.

=== PART D (DECIDE, DO NOT ASSUME) ===

D1. G7 -- the or-imp fragment IPL<or,imp,top> is the ONLY one of the eight fragment axiom systems without a completeness theorem. `OrImpAxiom` is declared (ProofSystem/FragmentAxioms.lean:257) and conservativity exists (`hilbertIplConservativeOverOrImp`, Algebra/OrImpConservative.lean:200), but no `orImp_*_completeness` exists anywhere. DIFFICULTY WARNING: its conservativity is proof-theoretic via cut-free LJ, NOT algebraic; the other four IPL fragments use Brouwerian/Hilbert-algebra Lindenbaum routes that do not obviously accommodate disjunction. Research the route before planning implementation.

D2. SEPARATION THEOREMS (the substance behind A1). Establishing MPL != IPL != CPL is REAL NEW MATHEMATICS, not cleanup. Report a recommendation on whether it belongs in scope; do not undertake it unilaterally under this task. INTERACTION TO ACCOUNT FOR: the natural route is exhibiting a separating formula via `decide` on the tableau -- which does not reduce in the kernel (see the instance-priority task and CslibTests/TableauConformance.lean:30, "`decide`, `native_decide`, and `rfl` stall on `WellFounded.fix`"). A separation proof will likely need `#eval`-level evidence promoted to a proof term, or a semantic argument instead.

=== ALSO RECORDED (no action unless you disagree) ===

G6 -- CPL Hilbert derivability is decidable only under `[Fintype Atom]` (Metalogic/StrongCompleteness.lean:566), while IPL and MPL are decidable for any `[DecidableEq Atom] [Hashable Atom]`. Tableau/Classical/DecisionProcedure.lean:79-80 notes the tableau route would lift the `Fintype` requirement. Whether to build that instance is a judgment call; A2 above only fixes the docstring that wrongly claims it already exists.
G9 -- no direct ND soundness/completeness for any system; both directions are reachable only by composing the `hilbert_iff_nd_*` bridges (NaturalDeduction/Equivalence.lean:448,456,464) with Hilbert-side results. Architectural and probably fine, but currently undocumented as a deliberate choice -- consider a module-docstring note.

=== DO NOT TOUCH ===

The intuitionistic engines internal "not proved"/"refuted" notes (Expansion.lean:151-155 saturation; Scheme.lean:596-597 isAccessible transitivity; Scheme.lean:4897-4899 intExpMeasure_step_lt) concern internal lemmas of a SUPERSEDED route. The headline theorems are sorry-free via a per-branch fuel-sufficiency argument, and the file records both "Gap 1" and "Gap 2" as closed at :804, :826, :5988. These are NOT live gaps. (Scheme.lean:4897-4899 is separately wrong on its own terms and is owned by the docstring-repair task -- do not also fix it here.)

---

### 617. Fix tautology decidable instance priority
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: CRITICAL. Library consumers importing `Cslib` receive a `Decidable (Tautology φ)` instance that cannot run in the kernel, shadowing the one that can. Seven existing tests pass only by accident of import order.

SURFACED AND REPRODUCED BY: the 2026-08-10 propositional review (specs/reviews/review-2026-08-10.md, finding C1). Both the defect and the fix were verified by direct experiment during that review -- this is not a hypothesis.

THE DEFECT: two instances target `Decidable (Tautology φ)`:
  - `instDecidableTautology` (Cslib/Logics/Propositional/Semantics/Bool.lean:185) -- Boolean enumeration over `BoolValuation`, requires `[Fintype Atom]`, REDUCES IN THE KERNEL.
  - `instDecidableTautologyTableau` (Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean:81) -- tableau-based, requires no `Fintype`, DOES NOT REDUCE IN THE KERNEL (stalls on `WellFounded.fix`).

Both carry default priority, so the later-declared tableau instance wins resolution wherever both are in scope. `Cslib.lean` imports both (`Semantics.Bool` at :597, `Tableau.Classical.DecisionProcedure` at :627), so every consumer of the barrel gets the inert one.

REPRODUCTION (verified): a file importing both `Cslib.Logics.Propositional.Semantics.Bool` and `Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure`, then:
  `#synth Decidable (Tautology (Atom := Bool) (.imp (.atom false) (.atom false)))`
resolves to `instDecidableTautologyTableau`, and
  `example : decide (Tautology (Atom := Bool) (.imp (.atom false) (.atom false))) = true := by decide`
fails with: "Tactic `decide` failed [...] After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, and `instDecidableTautologyTableau`, reduction got stuck at the `Decidable` instance".

BLAST RADIUS: `CslibTests/Propositional.lean:64-90` holds 7 `by decide` tautology tests that currently pass ONLY because that file does not transitively import the tableau module. Adding a single import breaks all 7. Downstream users importing `Cslib` cannot use `decide` on `Tautology` at all.

THE FIX (verified working): lower the tableau instances priority so the computable Boolean decider wins when both apply:
  `attribute [instance 100] instDecidableTautologyTableau`
With this in place, `#synth` resolves to `instDecidableTautology` and the `decide` examples compile clean. The tableau instance remains available for the `Fintype`-free case where it is the only candidate. Apply it at the declaration site in Tableau/Classical/DecisionProcedure.lean rather than in a consumer file.

VERIFY: (1) reproduce the failure first, so the fix is demonstrated against a known-red baseline -- do not skip this; (2) apply the priority change; (3) confirm `#synth` flips back; (4) add an import of the tableau module to `CslibTests/Propositional.lean` (or a new test file importing both) so the 7 `decide` tests actually EXERCISE the both-in-scope configuration and this regression cannot silently return; (5) full `lake build` + `lake test` green.

BACKGROUND (not a defect, do not "fix"): the `#eval`-vs-`decide` split is expected and documented at `CslibTests/TableauConformance.lean:30` -- "`decide`, `native_decide`, and `rfl` stall on `WellFounded.fix`". The tableau algorithms genuinely compute under `#eval` (20 `#guard_msgs` conformance rows green; `minimalTableau (⊥ → p)` correctly returns open, rejecting ex falso). This task is ONLY about instance priority, not about making the tableau kernel-reducible.

---

### 616. Repair stale contradictory tableau docstrings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Repair the stale and self-contradictory documentation layer in the propositional intuitionistic tableau tree. DOCUMENTATION ONLY -- no .lean proof term, statement, or definition may change. Verify with `lake build` that the tree stays green and that no declaration statement is touched.

SURFACED BY: the 2026-08-10 propositional review (specs/reviews/review-2026-08-10.md, findings H2 and M3), from a systematic check of every line-number reference under Cslib/Logics/Propositional/.

=== PART 1 (HIGH PRIORITY -- do this first, it is actively misleading) ===

`Tableau/Intuitionistic/Scheme.lean:9603-9608` (repeated verbatim at `:9733`) asserts in the PRESENT TENSE:
  "`rawEdges` was, and remains, REFUTED as a witness for `IFimpAccess` [...]:
   `CslibTests/WitnessProbe.lean:174-176` (`#eval check [(1,0),(2,1)]` reports
   `some (true, true)` -- upward-closed but FORCES `phiRef1` at world 0)"

Every factual element of that parenthetical is wrong (verified directly against the test file):
  - The `#eval` is at WitnessProbe.lean:177, not 174-176 (line 174 is blank).
  - The `#guard_msgs` at :175 asserts `some (true, FALSE)`, not `some (true, true)`.
  - WitnessProbe.lean:172-173 states the OPPOSITE of the docstring: "The raw tree edges:
    upward-closed, and (post-repair) DOES falsify `phiRef1` at world `0` -- this is now itself
    a witness (`upwardClosed = true`, `evalF ... = false`)."
  - `some (true, true)` is at WitnessProbe.lean:168 and belongs to `#eval check []` -- the EMPTY
    frame, a different probe entirely.

The two companion citations in the same paragraph are also off-target:
  - `BetaSplitRefutation.lean:304` is phiRef3s docstring; the raw-edge-list fact is at :318-320.
  - `:387` is inside `def fimpWitnesses`; `branchesAgree` is defined at :377, evaluated at :409.

CAUTION -- DO NOT SIMPLY FLIP THE WORDS. The frame-adequacy table immediately above
(Scheme.lean:9600-9601) still lists raw as "REFUTED" for IFimpAccess while listing augmented as
holding. Establish which verdict is actually authoritative post-repair BEFORE rewriting, and make
the table and the prose agree. If the table is the stale half, fix the table instead. Re-run or
read the CslibTests probes as ground truth; the #guard_msgs assertions are CI-protected and are
the most reliable evidence in the repository.

This is the same class of internal contradiction the earlier annotation close-out set out to
eliminate ("a docstring declared KNOWN IMPOSSIBLE a reconciliation a sorry-free proof performs
nearby"). That pass was incomplete; this instance survived it. Check for siblings it also missed.

=== PART 2: PRESENT-TENSE CLAIMS CONTRADICTED BY CURRENT CODE ===

  a. Scheme.lean:909-915 -- "that copy channel **was deliberately removed**", "confirmed
     structural blocker". Contradicted by Expansion.lean:121-127, which documents the channel as
     REINSTATED (V4, generalized to all positive-signed formulas). The section closing at :974
     scopes its retraction to items (i)-(ii) only, so it does NOT cover this paragraph.
  b. Scheme.lean:934, 939-940 -- present-tense "the `sorry` below". There is none; `truthLemma`
     (:997) is proved.
  c. Scheme.lean:4896-4899 -- "`intExpMeasure_step_lt`, not yet proved". Proved at :5097.
  d. Scheme.lean:7296-7299 -- "deferred to Phase 6". Landed: `IAugMembers_persist` (:7917).
  e. Expansion.lean:698-700 -- directive "do not attempt to prove [...] `hUniv` [...] they are
     refuted". The intUniverse/hnw half is STILL CORRECT and must be preserved. But `hUniv` now
     names `IAllUniv` (Scheme.lean:3298), which IS threaded and discharged (hypothesis at :8330,
     supplied at :9658-9664 via mem_intUniverseExt_of). Narrow the directive to the half that
     still holds.
  f. Minimal/DecisionProcedure.lean:22-24 vs :47 -- self-contradictory in one file: ":22-24 says
     "what still carries `sorryAx` one level down"; :47 says "This module is sorry-free, and so is
     everything it depends on." Nothing carries sorryAx. Drop the parenthetical at :22-24.
  g. IntDecidability.lean:71-72 and MinDecidability.lean:74-75 (identical text) -- "deferred
     (high risk, low payoff while 317 is open)". Dangling reference; both files assert the
     opposite in the same header (IntDecidability.lean:325, MinDecidability.lean:294). Per
     .claude/rules/no-task-references-in-deliverables.md, replace with a durable anchor, do not
     re-cite a task number.

=== PART 3: DOCSTRINGS CREDITING DEAD DECLARATIONS ===

  h. Minimal/Completeness.lean:58-61 attributes the live conjuncts to
     `openBranch_rawEdges_upward_closed` / `openBranch_rawEdges_both_upward_closed`. Both have
     ZERO non-docstring references in Cslib/ or CslibTests/. The live route is `hpersAug` over the
     AUGMENTED frame (Scheme.lean:9686-9705); Scheme.lean:9725-9727 says so explicitly.
  i. Minimal/Completeness.lean:137-138 and :164-166 imply `minOpenBranch_countermodel` feeds
     `minimalTableau_complete`. It does not -- the proof at :170-175 never mentions it, and that
     lemma has no code consumer at all. Compare Intuitionistic/Completeness.lean:120, which
     handles its twin correctly ("has no live consumer beyond docstrings") -- copy that framing.

=== PART 4: STALE LINE NUMBERS (lowest priority; ~38 sites) ===

  Scheme.lean self-refs pointing at the wrong declaration: :126 and :895 (sat_timp cited at
  105-108, actually 127); :834 (IExpandedConsistent_sat cited 897-967, actually 1303); :870
  (applyAllTImpRules_eq_self_of_length_eq cited 5335, actually 5942); :871 and :912
  (applyPersistenceFixpoint_genuine_of_count_le_fuel cited 5386/3444, actually 5993); :597 and
  :682 (cite 250-257, which is minSchemes docstring); :653 (cites 3272, a section header);
  :3587 (isAccessible_one_hop_ext cited 451, actually 657); :4087 and :9719 (IPosPersistRaw cited
  6701-6704, actually 7283); :4111 (cites 7058, induction boilerplate); :5702 (STOP-gate cited
  485-533, actually ~801-984); :7835 (IExpandedAccessConsistent cited 1078-1089, actually 1234).

  Rules.lean refs, all shifted: Scheme.lean:126 (arm cited 274-275, actually 279-280); :763,
  :827, :894 (cited 245-268, actually 279-280); :2341 (.neg/.imp arm cited 262-264, actually
  266-269); :2346 (posFormulasAt/propagatePersistence/intTImpRule cited 126/139-141/174-186,
  actually 131/144/179); :5148 (cited 254,260; actual .neg,.and at 257-258 and .pos,.or at
  261-262 -- AND the "F-or"/"T-and" labels are swapped relative to the signs given).

  Expansion.lean:514-516 cites :256-264 for an Option-B unsoundness note; those lines hold the
  tail of intStepBranch and the start of intStepBranchPrios docstring.

  Internal numbering contradiction: Scheme.lean:745 says "11th conjunct" where :9562 says "7th".
  7TH IS CORRECT against the statement at :8341-8344 (4 existential witnesses then 7 conjuncts;
  "11th" counts obtain-pattern slots, not conjuncts).

  Cross-module FmpMeasure.lean refs (~20 in Scheme.lean) drift 3-5 lines forward, e.g. modalUniverse
  cited 149-152 (actual 155), modalWork cited 190-193 (actual 197), modalSubfmls cited 73-80
  (actual 75-82). Lowest priority of all.

=== VERIFIED ACCURATE -- DO NOT TOUCH ===

Confirmed correct, listed so this pass does not churn them: the "PRE-REPAIR (historical)" blocks
at Scheme.lean:742-750, 755, 814-820, 841-845, 867-892, 898-904, 976-984, 1041-1052, 3284-3292,
9590-9601 and Expansion.lean:525-555 (all correctly re-tensed); the dead-code retention claims at
Scheme.lean:2385-2388 and 9725-9735; Intuitionistic/Completeness.lean:120; and the intUniverse/hnw
refutation at Scheme.lean:2372-2388 and 2887-2895 (still true of the retired engine).

=== CONSIDER (report, do not decide unilaterally) ===

~38 of these defects are line-number citations into files that have grown by thousands of lines
(Scheme.lean is ~9,900). Citing DECLARATION NAMES instead of line numbers would make this entire
defect class structurally impossible rather than recurrent. Report a recommendation on adopting
that as a convention; do not perform a repo-wide citation-style migration under this task.

---

### 615. Algebraic node proof system tfae
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Add algebraic semantic validity as a further equivalent node in the propositional proof-system TFAE families.

SURFACED BY: the 2026-08-10 propositional review (specs/reviews/review-2026-08-10.md, finding L1). Discoverability only — no mathematical content is missing; the required completeness results already exist.

CURRENT STATE: `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` ties together Hilbert, natural deduction, sequent calculus and tableau:
- 3-way, context-based: `cplProofSystemsTfae` (:76), `iplProofSystemsTfae` (:108), `mplProofSystemsTfae` (:141)
- 3-way, closed: `cplProofSystemsTfaeClosed` (:90), `iplProofSystemsTfaeClosed` (:122), `mplProofSystemsTfaeClosed` (:155)
- 4-way with tableau, closed only: `cplProofSystemsWithTableauTfae` (:203), `iplProofSystemsWithTableauTfae` (:229), `mplProofSystemsWithTableauTfae` (:252)

THE GAP: the substantial algebraic-semantics development under `Cslib/Logics/Propositional/Semantics/Algebra/` (Brouwerian algebras, Hilbert algebras, the Lindenbaum construction, algebraic completeness) is NOT wired in as a further node, even though `HilbertAlgCompleteness.lean` and `BrouwerianCompleteness.lean` prove what is needed. A reader cannot see from one place that algebraic validity is equivalent to the syntactic notions.

WORK: add the algebraic node to the appropriate TFAE families, composing the existing algebraic completeness/soundness results. Follow the pattern the tableau folds already established — including the `Iff.trans`-not-`rw` gotcha documented at :229-243 for any step that crosses a universe-invariance bridge.

SCOPE DISCIPLINE: mirror the existing typeclass hygiene. The tableau section deliberately scopes `[Hashable Atom]` to its own section (see the module docstring at :176-186) so the six pure proof-theoretic equivalences are not forced to carry it; do the same for whatever algebraic typeclass requirements the new node introduces, rather than widening the existing six.

DECIDE AND RECORD: whether the algebraic node belongs on the context-based families, the closed families, or both — and say why in the module docstring, so the shape reads as a decision rather than an omission.

VERIFY: `lake build` green; zero new sorries; zero new axioms beyond [propext, Classical.choice, Quot.sound]; no change to the statements of the nine existing TFAE theorems.

---

### 614. Computable ctxtoimp context decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None

**Description**: Give `ctxToImp` a computable definition so the four context-based `Decidable` instances for the propositional sequent calculi stop being `noncomputable`.

SURFACED BY: the 2026-08-10 propositional review (specs/reviews/review-2026-08-10.md, finding M2). User decision recorded in that review: computable context-based decision procedures ARE in scope for "propositional logic complete in full", so this is a genuine remaining gate, not an accepted limitation.

THE DEFECT: `ctxToImp` (Cslib/Logics/Propositional/SequentCalculus/LJ/Decidability.lean:82) is declared `noncomputable` solely because it uses `Finset.toList`. There is NO mathematical obstacle. That single incidental noncomputability propagates to all four context-based instances:
- `instDecidableLJDerivable` (LJ/Decidability.lean:197)
- `instDecidableDerivableInIPL` (LJ/Decidability.lean:218)
- `instDecidableLKDerivable` (LK/Decidability.lean:174)
- `instDecidableDerivableInCPL` (LK/Decidability.lean:190)

The docstring at LJ/Decidability.lean:190 states the cause outright: "The instance is `noncomputable` because `ctxToImp` uses `Finset.toList`."

IMPACT: the library can COMPUTE whether a closed formula is a theorem (the tableau procedures `intuitionisticTableau`/`minimalTableau`/`classicalTableau` are genuinely computational and sorry-free), but cannot compute whether a non-empty context proves a formula.

APPROACH (not prescriptive): give `ctxToImp` a deterministic computable fold — e.g. over a `List`/`Multiset` with a canonical order, or by requiring `[LinearOrder Atom]` for a canonical sort — then drop `noncomputable` from `ctxToImp` and all four instances. Preserve the existing universe-bridging via `ivalid_universe_invariant`/`mvalid_universe_invariant`; those are load-bearing and unrelated to this fix.

VERIFY: `lake build` green; the four instances build without `noncomputable`; add a `#guard_msgs`-protected computation in CslibTests/ demonstrating a non-empty-context decision actually evaluates. Watch for the two known `unusedDecidableInType` lint warnings (task 613) which are pre-existing in the same subtree and NOT this task's to fix.

FOLLOW-ON: if this lands, the closed-context restriction on the tableau TFAE folds (ProofSystemEquivalence.lean:176-186) becomes revisitable; that is explicitly out of scope here.

--- APPENDED 2026-08-10 (review finding M5: deeper root-cause analysis) ---

THE ROOT CAUSE IS DEEPER THAN "uses Finset.toList", AND THE FIX IS NOT FREE. `Multiset.toList` is itself `noncomputable def toList (s : Multiset a) := s.out` (.lake/packages/mathlib/Mathlib/Data/Multiset/Basic.lean:33, docstring: "Produces a list of the elements in the multiset using choice"). Picking a list order for a `Finset` is a GENUINE CHOICE -- distinct orders give distinct (though interderivable) formulas. `Finset.fold` does NOT apply: it requires commutativity and associativity, and `imp` is neither. `Hashable` supplies no total order.

TWO HONEST ROUTES, different costs -- pick deliberately and record the reasoning:
  (1) Add `[LinearOrder Atom]` and use `Finset.sort`. Computable, but imposes a NEW HYPOTHESIS on the four public instances. Weigh against the fact that `instDecidableIValid`/`instDecidableMValid` currently need only `[DecidableEq Atom] [Hashable Atom]`.
  (2) CHEAPEST REAL FIX: restate over `List` contexts. `listToImp` (LJ/Decidability.lean:72) and the list-level lemmas `ljListDeductionFwd`:91 / `ljListDeductionBwd`:130 (LK counterparts :65/:110) are ALREADY plain computable defs. Only the `ctxToImp`-wrapped :112/:170 and the four instances inherit the taint. This route adds no typeclass hypothesis.

SEPARATELY VERIFIED AS HARMLESS -- DO NOT "FIX": `decidableDerivableIntPropAxiomFMP` (Metalogic/IntDecidability.lean:489) and `decidableDerivableMinPropAxiomFMP` (MinDecidability.lean:445) are noncomputable for a DIFFERENT and deeper reason -- they depend on `instFintypeIntFinWorld`:153 / `instFintypeMinFinWorld`:155, built via `Fintype.ofInjective`, itself a `noncomputable def` (Mathlib/Data/Fintype/OfMap.lean:67; inverting an injection needs choice). Not a toList artifact and not removable by reordering. They are deliberately plain `def`s and NOT registered instances -- IntDecidability.lean:484-487 and MinDecidability.lean:441 both state the canonical registered instance is the computable tableau one. Leave them alone.

CONCLUSION: every REGISTERED `Decidable` instance in the subsystem is computable except the four LK/LJ context-based ones. That is exactly this task's scope and the only set worth acting on.

COORDINATE: the LM-decidability item (G4) in the coverage-gaps task will want to build on whatever route lands here. If this task lands first, that one should inherit the computable route rather than the taint.

---

### 613. Fix unuseddecidableintype lint warnings
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: None

**Description**: Fix the two unusedDecidableInType lint warnings in Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean:159 and Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean:173. Both are pre-existing and were surfaced while verifying the propositional tableau TFAE fold. Verify with lake lint after the fix.

---

### 612. Metadata and hygiene batch from the 2026-08-09 review
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: None

**Description**: Batch of small, independent corrections surfaced by the 2026-08-09 review. Each is self-contained; none requires research.

1. RE-TIGHTEN THE SORRY RATCHET. `bash scripts/check-sorry-suppressions.sh` reports `sorries: 26 (baseline ceiling 28)` and prints an ACTION REQUIRED block. The un-ratcheted file is `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (baseline `0 1`, actual `0 0`) -- the S4 redirect lemma deleted during the ancestor-redirect refutation. Run `bash scripts/check-sorry-suppressions.sh --update` and commit the updated baseline. One command.

2. REFRESH TASK 606's STALE SITE LIST. Its description enumerates "THE FOUR SITES" including `DP-5: truthLemma, Scheme.lean:693, sorry at :768`. DP-5 was discharged by task 604 and `truthLemma` is now sorry-free. All four cited line numbers are stale (the file has grown past 8,000 lines). Correct to the three live sites: `Intuitionistic/Scheme.lean:8034` (DP-6, the open existential), `Intuitionistic/Completeness.lean:170` (DP-3), `Minimal/Completeness.lean:166` (DP-4).

3. UNBLOCK TASK 554. It carries `status: blocked` with `dependencies: []` and nothing actually blocking it, while gating tasks 537 and 551 -- the entire constructive CS5 line, which the 2026-08-09 scope decision KEPT IN SCOPE. Either transition it to `not_started` or record what it is blocked on.

4. BACKFILL `file_scope` ON 497 AND 589. Both are absent. 497 is the `imp`->`impl` rename (~271 files); 589 is the repo-wide `unusedArguments` lint (33 files across five trees). Both are invisible to any clash check. 497 is now transitively serialized behind the propositional chain via 375, but remains unscoped against everything else.

5. RE-BASELINE THE ROADMAP COVERAGE COUNT. `specs/ROADMAP.md` instructs the next audit to "use the 46-task, fully-covered baseline". Thirteen tasks were archived on 2026-08-09, leaving 36 open. Coverage itself is intact -- all 36 open tasks are named in the roadmap, verified mechanically -- so only the number needs updating.

NOT IN SCOPE: the `file_scope` read/write distinction (that is task 595's charter, and it needs a schema decision first).

SOURCE: specs/reviews/review-2026-08-09.md findings H2, M1, M3, L1, L2.

--- APPENDED 2026-08-10 by the propositional review (specs/reviews/review-2026-08-10.md) ---

6. CORRECT THE STALE PROPOSITIONAL ROADMAP ROWS (finding H1). `specs/ROADMAP.md` states as verified fact, in four places, claims that are now false:
   - `:157-160` -- "**26** code-position sorries repo-wide -- Bimodal 23, Propositional 3, Modal 0 [...] the Propositional 3 are **bare**, and are the stated reason `lake build --wfail --iofail` is red on this tree." ACTUAL: Propositional is at **0** sorries (verified: 0 tactic-position occurrences, 0 `warn.sorry` suppressions, `lake build` of ProofSystemEquivalence + Tableau green at 990 jobs). Repo-wide is **23**, all in Bimodal, all suppressed. The `--wfail` red is now attributable to the two `unusedDecidableInType` lint warnings owned by task 613, NOT to sorries.
   - `:171` -- the propositional tableau completeness row still reads "**3 sorries**, as of 2026-08-09 [...] 601/602/603/604 completed, 605/606 not started". All of 605, 606, 609, 375 and 593 completed and were archived 2026-08-10. Move this row to **Completed**.
   - `:185` -- "task 375 `not_started`" for the TFAE fold. 375 is completed (the folds landed: cplProofSystemsWithTableauTfae, iplProofSystemsWithTableauTfae, mplProofSystemsWithTableauTfae in ProofSystemEquivalence.lean). Move to **Completed**.
   - `:313` -- the exclusion row for 591/592/593 refers to a superseding chain that is now fully terminal.
   NOTE ON DETECTION: `roadmap-integration.sh --annotate` ran against these tasks and made 0 annotations (scored the sole candidate `low_confidence`, `items_skipped: 1`), and the roadmap parsed cleanly with no warnings. This drift class is structurally invisible to the automation -- worth noting when task 595 designs its validation gate.

7. ITEM 2 ABOVE IS NOW SUPERSEDED. Task 606 completed and was archived on 2026-08-10; its description no longer needs refreshing. Verify and drop item 2 rather than acting on it.

8. ITEM 5 ABOVE NEEDS RE-COUNTING. Five more tasks (375, 593, 605, 606, 609) were archived and two created (614, 615) on 2026-08-10. Re-derive the open-task count from `specs/state.json` at execution time rather than trusting any number written here.

---

### 611. Correct the stale decidability-matrix documentation and record the 10-of-15 scope decision
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 610

**Description**: Correct the decidability-matrix documentation block in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (currently around lines 9110-9185), which is stale relative to what landed on 2026-08-09.

THREE STALE CLAIMS TO FIX:
1. The block names "serial-rule spec shape" as a live gate blocking D, DB, D4, D5 and D45. That gate is DISCHARGED -- its founding premise was machine-checked false, `DDriver.lean` was built with the full twelve-field witness, and the top-loop `...At` retype landed `modalExpandBranchesD_hintikka`.
2. It prices D at "~1,700 lines once ungated". The 1,327-line driver is already built; only the sound/complete/instance wiring remains.
3. The "Covered (8/15)" table must move D into the covered set once the wiring task lands, and the "Out of scope, with named gates" list must drop D and re-state DB's gate (its serial gate is discharged; only the SymmGen closure plus serial repair remain).

ALSO RECORD THE SCOPE DECISION (made 2026-08-09, see ROADMAP.md): the target is 10 of 15 corners. D and DB are IN scope. K45, D5 and D45 remain in scope but sequenced behind the Euclidean rule-combinator prototype. K4 and D4 are DELIBERATELY EXCLUDED at Tier C (~13,500 lines each, ~27,000 combined) -- the matrix stays intentionally incomplete there, and the block should say so as a decision rather than as an unmet gate.

CONSTRAINT: documentation-only in the Lean source -- do not change any proof, definition or instance. This task exists separately from the wiring task specifically so the two do not write `FrameCompleteness.lean` concurrently.

SOURCE: specs/reviews/review-2026-08-09.md finding C1.

---

### 610. Wire the D (serial) corner through to instDecidableDValid
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Wire the D (serial) corner through to a `Decidable` instance. The expensive machinery already exists and is green; only the final soundness/completeness/instance chain is missing.

WHAT EXISTS (landed 2026-08-09, verified): `Cslib/Logics/Modal/Tableau/DDriver.lean` (1,327 lines, registered in Cslib.lean) carrying `modalDualAugment`, the D driver triple, the complete twelve-field witness `modalApplyOneD_specAt`, `modalTableauD_eq`, and `modalExpandBranchesD_hintikka`. Build green at 3325 jobs, zero sorry in all touched files, `#print axioms modalApplyOneD_specAt = [propext, Classical.choice, Quot.sound]`.

WHAT IS MISSING (verified absent by grep): `dValid`, `modalTableauD_sound`, `modalTableauD_complete`, `instDecidableDValid`. Every covered corner (K, T, B, TB, K5, KB5, S4, S5) has all four; D has none.

SCOPE: follow the T corner end-to-end as the pattern -- `tValid` (FrameSoundness.lean), `modalTableauT_sound`/`modalTableauT_complete`, `instDecidableTValid` (FrameCompleteness.lean) -- and produce the D analogues. The serial-rule spec-shape gate that previously blocked this is DISCHARGED: research machine-checked that its founding premise was false (`modalApplyOneD` already satisfies `boxPosNotExpanding`; only `outputsSubsetUniverse` failed, for a universe reason, and that was narrowed via the additive `RuleApplicationSpecCoreAt`/`RuleApplicationSpecAt` siblings). The top-loop chain was retyped to the `...At` interface, landing `modalExpandBranchesD_hintikka` and explicitly unblocking D/DB/D4/D5/D45.

NOTE: do NOT re-litigate the per-regime driver split. That decision is settled -- each corner gets its own bespoke driver file rather than a generic traversal rung parameterised over frame conditions (see the "Settled decisions" block in FrameCompleteness.lean).

Zero new sorries, zero new axioms. Verify `lake build` green and `#print axioms instDecidableDValid` before completion.

SOURCE: specs/reviews/review-2026-08-09.md finding C1.

---

### 608. Fix lean-sorry-census.sh double-counting set_option warn.sorry false in as a sorry
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: None

**Description**: Discovered during task 596's ROADMAP realignment (2026-08-09; see specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md section 1 for the full evidence trail, independently re-verified by team-lead with a corrected-regex re-run). The deployed .claude/scripts/lean-sorry-census.sh strips comments/strings correctly, then matches `\bsorry\b` on the stripped text. It does NOT exclude `set_option warn.sorry false in` -- because `.` is a non-word character, `\bsorry\b` also matches the "sorry" substring inside "warn.sorry", so every suppression-annotation line is counted as an extra phantom sorry on top of the real sorry it annotates.

Verified for every Cslib/Logics/Bimodal file carrying sorries: script count 41 = 23 real sorry occurrences + 18 warn.sorry annotation lines double-counted (repo-wide: 45 = 27 + 18). The 27/23 figures independently match the pre-existing ROADMAP.md census and task 215's own hand-audited scope (12 + 1 = 13 for the BXCanonical files specifically). Team-lead independently reproduced repo-wide 45->27, Bimodal 41->23 using the corrected regex `(?<![.\w])sorry\b` substituted into the script's own strip_lean_comments pipeline, and confirmed a naive grep-style count that skips the block-comment/docstring stripper gives 152 repo-wide -- the stripper itself is correct and valuable; the `\bsorry\b` regex is the only broken piece.

CRITICAL -- fix target is the SOURCE STORE, NOT the deployed .claude/ copy: this repo's .claude/ tree is a gitignored deploy artifact regenerated from the source store (see .claude/rules/source-store-deploy-boundary.md). A hand-edit to .claude/scripts/lean-sorry-census.sh is silently wiped on the next regeneration. The actual fix target is the source-store copy at agent-system/extensions/lean/scripts/lean-sorry-census.sh (found on this machine at /home/benjamin/.config/nvim/agent-system/extensions/lean/scripts/lean-sorry-census.sh -- confirm the correct source-store root for whichever environment this task is executed in; it is a sibling extensions tree outside this repository, not a path under cslib/).

Fix: exclude lines that are exactly (or contain only) the `set_option warn.sorry false in` directive from the `\bsorry\b` match -- e.g. use the negative-lookbehind regex `(?<![.\w])sorry\b` in place of `\bsorry\b` (verified to work by both the task-596 implementer and team-lead independently), or line-level pre-filter any line whose stripped content is exactly the set_option directive. Preserve the comment/string stripper (`strip_lean_comments`) unchanged -- it is correct and is the script's valuable part; only the final regex match needs to change. Add a regression fixture (a file with N suppression annotations and M real sorries, asserting the census reports M, not M+N) so this cannot silently regress. Cross-check against `lake build`'s compiler-backed "declaration uses 'sorry'" warning count (the script's own --cross-check flag) as part of the fix's verification, since that count is comment/annotation-immune by construction.

---

### 607. Decide: complete BXCanonical/dense or abandon it for the algebraic pipeline
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Bimodal Metalogic
- **Dependencies**: None

**Description**: Tracked decision (created by task 596's ROADMAP realignment, per specs/ROADMAP.md Section B "Open decision"). The bimodal completeness layer has three constructions: `Algebraic` and `Bundle` form the wired, actively-used completeness pipeline; `BXCanonical` is a separate, incomplete leaf that nothing downstream imports.

Measured 2026-08-09 (bash .claude/scripts/lean-sorry-census.sh, hand-verified against the raw `sorry` occurrences to exclude the script's warn.sorry-substring double-counting bug -- see specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md section 1): BXCanonical carries 13 live sorries (ChronicleToCountermodel.lean: 12, Frame.lean: 1), all gated on the WeakCanonical discrete-completeness port. Task 215 already owns filling these specific sorries once that port lands.

This task is NOT about filling the sorries -- it is the prior architectural decision: (A) complete BXCanonical/dense once its blocking port lands (in which case task 215 delivers it), or (B) abandon BXCanonical/dense as dead weight and consolidate the bimodal completeness story onto the Algebraic+Bundle pipeline alone, retiring the file. Neither option should be taken autonomously by an implementer -- this task exists to hold the decision until a maintainer makes the call, at which point it should be re-scoped into either a completion task (if A) or a retirement/consolidation task (if B).

---

### 600. Unordered s4 stepper stack retirement
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Retire the unordered S4 stepper stack at Cslib/Logics/Modal/Tableau/LoopChecking.lean:192 (the 'Phase 15' marker). Research on the eight-corner decidability gap measured 152 live references still pointing at it, making this a real migration rather than a deletion. The keyed-ordered S4 path that supersedes it already landed (modalTableauS4KeyedOrdered_sound / _complete, instDecidableS4Valid in FrameCompleteness.lean). WORK: migrate the live references to the keyed-ordered path and remove the unordered stack. HARD PREREQUISITE for the K4 and D4 modal-cube corners per the tableau driver abstraction decision (section 9). Independent of the serial-rule spec decision and the Euclidean rule-combinator prototype. Zero sorry, zero new axioms; keep frozen deliverables from task 300 and task 506 untouched.

---

### 599. Euclidean rule combinator prototype
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Prototype the Euclidean rule combinator identified as an open, unowned gate by the tableau driver abstraction decision (section 7.2). WORK: build the combinator on Kb5''-from-Five and measure it -- derive the KB5 rule set from the existing Five (K5) rule set via the combinator rather than restating it, and report the measured cost against the bespoke alternative. Deliverable is a measured prototype plus decision report. GATES: K45, D5, D45 in the modal-cube decidability matrix. Independent of the serial-rule spec decision and the S4 stepper-stack retirement -- all three can run in parallel. Zero sorry, zero new axioms; keep frozen deliverables from task 300 and task 506 untouched.

---

### 595. Add a dependency-integrity validation gate so task-graph staleness cannot recur silently
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: Task 594

**Description**: Build the validation gate that would have caught the task-graph findings automatically. Created by the 2026-08-07 codebase review (specs/reviews/review-2026-08-07.md, finding H5 and recommendation 3).

WHY THIS EXISTS -- the loop is not closing: specs/ROADMAP-alignment-audit.md:15 ALREADY recorded "the dependency graph is materially broken" with "one circular edge, five edges pointing at archived tasks, and a recurring completed-but-doesn't-unblock pattern that makes several [blocked] labels stale". Its recommendations were never applied, and on 2026-08-07 the same findings recurred at roughly three times the scale: 37 stale edges, 6 stale-blocked tasks, 20 tasks absent from the roadmap. A one-time cleanup (the reconciliation metatask) will regress again without a gate. There is no dependency-integrity check anywhere in .claude/scripts/ today.

CHECKS TO IMPLEMENT (each must exit non-zero with an actionable message):
(A) STALE BLOCK -- any task with status `blocked` whose dependencies are all satisfied (completed/abandoned in either specs/state.json or specs/archive/state.json) AND which carries no `blocked_reason`. This is the check that would have caught all six.
(B) DANGLING EDGE -- any dependency naming a task number absent from both the active and archived sets.
(C) CYCLE -- any directed cycle in the dependency graph. The prior audit found a 512<->517 cycle; none exists today, so this check guards a real historical failure mode.
(D) PROSE/STATUS DISAGREEMENT -- any task whose description contains "BLOCKED" while its status is not `blocked`, or the converse. Currently fires on 497 and 548.
(E) HUSK -- any task whose entire remaining scope is delegated to a single dependent task, surfaced as a warning rather than a failure (this one needs human judgement; 506 is the worked example).

CRITICAL SCOPING CONSTRAINT -- READ BEFORE STARTING: this repository has NO `agent-system/` source store. Verified 2026-08-07: only two files under `.claude/` are git-tracked, and .claude/rules/source-store-deploy-boundary.md states that `.claude/**` is a disposable deploy artifact regenerated from `agent-system/extensions/**`. A script written into `.claude/scripts/` HERE will be silently wiped by the next deployment. The script must therefore be authored in the upstream source store repository that owns `agent-system/extensions/core/scripts/`, then deployed. FIRST STEP: locate that source store and confirm the correct write target. If it cannot be located, land the checker under this repository's own root-level `scripts/` directory (which IS tracked and IS the home of check-axiom-census.sh, check-sorry-suppressions.sh, check-shake-residue.sh and the other project gates) and record the deviation -- do NOT write into `.claude/scripts/` and call it done.

WIRING: follow the existing project-gate convention in scripts/ and add it to the same gate set the other check-*.sh scripts belong to. Include a self-test with fixture inputs, matching the pattern used by check-runtime-file-tracking.sh (which uses synthetic `000_probe` / `sess_0000000000_probe` fixtures).

SEQUENCING: the reconciliation metatask performs the one-time cleanup; this task prevents recurrence. Running this gate against the pre-cleanup state should reproduce all six stale-blocked findings -- use that as the acceptance test.

---

### 594. Metatask: reconcile all open task records against verified repository state
- **Status**: [NOT STARTED]
- **Task Type**: meta
- **Topic**: Agent System
- **Dependencies**: None

**Description**: METATASK. Bring all open task records in specs/state.json into agreement with verified repository state. Created by the 2026-08-07 codebase review (specs/reviews/review-2026-08-07.md, findings H1-H3, M4) at explicit user request for a metatask covering revisions to incomplete tasks.

EVERY ITEM BELOW WAS VERIFIED ON 2026-08-07. Re-verify before acting -- do not act on this list blind.

(1) SIX TASKS MARKED [BLOCKED] HAVE ZERO UNMET DEPENDENCIES. Resolving each edge against specs/state.json and specs/archive/state.json: 511, 554, 568, 583, 409, 37. specs/TODO.md's generated wave table places 511/554/568/583/409 in Wave 1 ("no active dependencies") while the tree entries immediately below render them [BLOCKED] -- the file contradicts itself within one section. Set 511, 554 and 568 to not_started (554's own description says its research is COMPLETE and the remaining work is "LAND NOW (mechanical, no research risk)"). Unblocking 511 and 554 cascades to release 506, 300, 537 and 551.

(2) CLOSE 583 AS SUPERSEDED. Its target `intExpandBranches_openBranch_sat` was restated per its own SCOPE and is now SORRY-FREE at Scheme.lean:6806. Its cited lines are stale: :2583/:2623/:2598-2622 today hold `intUniverseExt_length_le`, `mem_intUniverseExt_of` and neighbours, with no sorry in that region. Its own VERIFY BEFORE STARTING clause mandates this: "if the divergence repair has already restated the lemma, close this task as superseded rather than duplicating the work."

(3) CLOSE 506 AS EXPANDED/PARTIAL AND RE-POINT 300. 506 landed Phases 1-7 green (zero sorry/axiom) and its entire remaining scope IS 511. The graph currently reads 300 -> 506 -> 511, so the umbrella cannot close until an empty intermediate does. Record 506's landed phases in its completion summary, then set 300's dependencies to [511].

(4) THIRTY-SEVEN DEPENDENCY EDGES POINT AT ARCHIVED TASKS. generate-task-order.sh silently treats these as satisfied, which is exactly what makes the staleness invisible. Retarget or drop each. Known live retargets: 375's dependency on archived 317 should become [593] (its real gate is the propositional tableau sorries); 548's dependencies should add [597] (the driver-abstraction decision must precede its 8-corner expansion).

(5) ADD A `blocked_reason` FIELD. There is currently no way to distinguish a genuine external gate from stale graph state. Genuine external gates to record: 37 ("upstream BimodalLogic continuous frame development, not started upstream"), 497 ("external PR leanprover/cslib#607 not yet merged"), 409 ("parked behind an explicit trigger condition, not a dependency"). Note 497 and 548 currently say "BLOCKED" in their description prose while carrying status not_started -- the prose and the status disagree in both directions across the task set.

(6) REFRESH STALE DESCRIPTION TEXT. 375 names only the CPL and IPL TFAEs when `mplProofSystemsTfae` now also exists in ProofSystemEquivalence.lean; 571 qualifies its line numbers with "as of"; 548 says "BLOCKED on 511/535 landing" while 535 is archived.

(7) REWRITE `active_goal`. Handled directly by the review that created this task -- verify it still reads correctly and reflects any status changes made above.

CONSTRAINT: this task changes task METADATA only. No .lean file may be created, edited or deleted. All state.json writes go through .claude/scripts/state-write.sh (the single mutex-guarded writer); regenerate TODO.md via generate-todo.sh afterwards, never by hand.

---

### 590. Reestablish out of tree probe verdicts
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None

**Description**: Re-establish the six out-of-tree probe verdicts under a dedicated multi-hour budget: s4probe.lean, s4boxed.lean, s4ancestor.lean, s4subtractive.lean, s4subtractive2.lean, s4subtractive3.lean. These probes are expensive to run and their recorded verdicts have drifted from the current tree. Two specific record defects must be corrected as part of this work, folded in here rather than tracked separately because re-running the probes supersedes them: (a) the S4 loop-guard report 01 describes an s4probe.lean harness from a superseded revision -- eight identifiers it names (dfsR, classify, statsL, badL, hasCountermodel, notS4Valid, def sat, def isS4) have zero matches in the current on-disk file; (b) s4subtractive3.lean carries pre-split LoopChecking.lean:NNNN line citations that no longer resolve -- the declarations still exist under the same names in S4/Hintikka.lean, S4/HintikkaInvariant.lean and S4/Driver.lean, so these should be replaced with declaration names rather than re-numbered. If the multi-hour re-run budget never materialises, split (a) and (b) out as a standalone documentation-only task: they have independent value as a stopgap, because the stale records actively mislead every reader until corrected.

---

### 589. Repo wide unusedarguments lint hygiene
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Code Hygiene
- **Dependencies**: Task 534, Task 548, Task 593

**Description**: Fix repo-wide unusedArguments lint findings across the Lean sources: 145 sites in 27 modules, 10 of them in Cslib/Logics/Modal/Tableau/. The uniform pattern is an unused [Hashable Atom] (or analogous) section-level instance binder; the idiomatic fix is `omit [Hashable Atom] in` before the affected block. Distinct from the existing blanket file-scoped lint-suppression ratchet: these are live lint findings, not suppressions, so the ratchet baseline does not cover them.

---

### 588. Tableau import reachability duplicate families
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511, Task 534, Task 597

**Description**: Resolve the five import-reachability duplicate families in Cslib/Logics/Modal/Tableau/: accFreshInv_append, hasEdge_addEdge_mono, modalApplyOne_boxPos_acc_eq, modalApplyOne_diamondNeg_acc_eq, not_shape_of_not_or. These are privacy-caused duplicates that de-privatization alone cannot resolve: three consumer files cannot reach Soundness.lean where the largest family originates. This is a module-graph problem (new Support module or import restructure), not a statement-equivalence adjudication. The Support-module extraction audit supplies no verdict bearing on these, and the duplicate-family adjudication that followed it explicitly left this class untouched.

---

### 576. Resolve the Chronicle namespace/structure name coincidence and its 36 load-bearing suppressions
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal and Temporal Logic
- **Dependencies**: Task 530, Task 568

**Description**: Resolve the `namespace Chronicle` / `structure Chronicle` NAME COINCIDENCE, and delete the 36 suppressions it forces (33 @[nolint], 3 set_option) across the three ChronicleTypes/Types files, 9 declarations each.

ORIGIN: identified during the repo-wide lint-hygiene work as the genuine residual defect behind a group of dupNamespace suppressions. That work closed its doubled-namespace phase at 7 of 10 files and deliberately EXCLUDED the three Chronicle modules, because the original doubled-namespace diagnosis was WRONG there: `namespace ...Metalogic.Chronicle` contains `structure Chronicle`, so `def Chronicle.c0` correctly declares a structure-projection member that 81 dot-notation call sites (chi.c0, chi.c3, ...) depend on. A mechanical prefix strip fails with "Invalid field 'c0': the environment does not contain ...Chronicle.Chronicle.c0". The 36 suppressions are LOAD-BEARING until the coincidence itself is resolved -- do NOT delete them before the restructure lands.

THE DECISION: either (a) move `structure Chronicle` to the parent namespace, or (b) rename the namespace across the whole Chronicle/ subtree, or (c) a better option surfaced by the dependency below. This alters definitions, which is why it was barred from the hygiene-only lint task.

DEPENDENCY RATIONALE (task 568): 568 asks what the RIGHT Chronicle architecture is for Bimodal/Temporal dedup, evaluating type-alias, label-type parameterization, and typeclass-mediated indexing. Its file_scope is the three Chronicle DIRECTORIES and strictly contains this task's three files. If 568 recommends parameterizing the structure away, the naming question resolves differently -- or evaporates entirely. Renaming first would risk doing the work twice. Sequence after 568 reports.

DEFINITION OF DONE: the namespace/structure coincidence is resolved by an explicit, recorded decision; all 36 suppressions are deleted; dupNamespace is clean across the three files; the 81 dot-notation call sites still resolve; `lake build --wfail --iofail` shows no new warnings and `lake test` is unchanged.

CONSTRAINT: preserve every landed sorry-free result; do not discharge, add, or relocate any sorry.

---

### 571. Fill the strict-Until/Since-gated Bimodal sorries (SuccRelation, UntilSinceCoherence)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 37

**Description**: [Carved off the bimodal sorry task by the blocked-task review. Holding both halves as one task pinned the tractable discrete half behind this intractable one; they have different external gates and different prospects.] Fill the sorries gated on the strict Until/Since semantics gap in Cslib/Logics/Bimodal/Metalogic/:
- Bundle/SuccRelation.lean: 7 sorries (lines 257, 263, 270, 277, 284, 289, 294)
- Bundle/UntilSinceCoherence.lean: 2 sorries (lines 38, 43)

All 9 require axioms that were REMOVED AS UNSOUND (BX8/BX9 and the temporal-T axioms) under the strict Until/Since reading. They are therefore not merely unproved -- the statements may need restating before they are provable at all. Gated on the bimodal continuous port, which is itself gated on upstream BimodalLogic tasks 390/391 (Dedekind carrier construction and FrameClass scaffolding), both [NOT STARTED] upstream. Line numbers are as measured 2026-07-26. BEFORE PLANNING, establish whether the 9 obligations are stated soundly under the current semantics: if the removed axioms were genuinely unsound, some of these may need to be restated or retired rather than proved, and that determination should precede any port dependency.

---

## LINE NUMBERS ARE STALE (repo-wide lint/CI audit)

The line numbers in the body above are dated 2026-07-26 and have since moved -- the repo-wide lint-hygiene pass rewrapped long lines, deleted blank lines inside single-command blocks, and narrowed blanket linter suppressions to declaration scope across these files. RE-DERIVE EVERY LINE NUMBER LIVE (`grep -n sorry <file>`) before acting; do not trust the recorded positions.

The FILE-LEVEL scope and the sorry COUNTS per file are unchanged and remain accurate. The sorries in these files are currently hidden from `lake build --wfail --iofail` by `set_option warn.sorry false in` markers; filling them must also DELETE the corresponding marker, so the suppression count drops with the sorry count. A suppression ratchet is being added under a separate task to enforce exactly that.

---

### 569. Establish whether continuous time needs axioms beyond density (Burgess 1982)
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 530

**Description**: [Created by the blocked-task review to break a two-task deadlock.] RESEARCH ONLY. Both the temporal and bimodal continuous-completeness tasks are recorded as blocked on 'the continuous case has not been developed upstream' -- but their SHARED real blocker is a literature question that depends on neither, and can be answered today: DO CONTINUOUS (Dedekind-complete) FRAMES REQUIRE ANY AXIOM BEYOND DENSITY? The standard result attributed to Burgess 1982 is that the Until/Since temporal logic over the reals has exactly the same theorems as over the rationals, which would make density sufficient and collapse both continuous tasks to near-trivial transports of the already-landed dense completeness. That equivalence is precisely what has never been checked here. DETERMINE: (1) the exact statement and proof strategy of the Burgess result, from the source -- not from secondary recollection; (2) whether it applies to THIS repository's Until/Since temporal language and frame conditions, or only to a variant; (3) if it applies, the cheapest sound route to a Continuous frame class and its completeness theorem, and whether the bimodal continuous port is needed at all or can be bypassed; (4) if it does NOT apply, which additional axiom schema (Dedekind completeness or equivalent) is required, and what that costs. Run with --lit. A negative or 'genuinely open' verdict is a valid deliverable. CONSUMERS: the temporal continuous-completeness task (which may be re-scoped or unblocked outright on the verdict) and the bimodal continuous port (which may turn out to be unnecessary as a dependency).

---

### 568. Research the highest-quality Chronicle-structure refactor for Bimodal/Temporal dedup
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal and Temporal Logic
- **Dependencies**: Task 530

**Description**: [Follow-on created by the blocked-task review, at explicit user request, to run AFTER the Chronicle consolidation task closes as a descoped partial.] RESEARCH ONLY -- produce a recommendation, do not implement. THE QUESTION: the Bimodal and Temporal Chronicle trees remain ~89% duplicated. The consolidation task successfully lifted ChronicleInterface, generic Types, the RRelation shared core and the CEE Structures + BurgessHelpers, then hit a hard wall: C5ForwardWalkResult, C5BackwardWalkResult, EliminationResult and ChronicleConstruction are indexed by each tree's LOCAL Chronicle Atom structure, and two independent deep investigations confirmed that generically bridging that indexing breaks downstream rcases/simp proofs. Descoping was the right call for a task mandated as 'structural dedup, not a proof change'; it does not answer what the RIGHT architecture is. DETERMINE: whether a Chronicle-type-alias architecture, a parameterization over the label type, a typeclass-mediated indexing, or some fourth option lets the walk-result and construction layers be shared without perturbing the proof scripts that consume them -- and what each would cost. Establish this against the actual proof scripts that broke, not against the type signatures alone; the failure mode was rcases/simp behaviour, so a design that type-checks is not evidence. REPORTING CONTRACT: deliver either (a) a concrete architecture with a phase-sized implementation sketch and an honest cost, or (b) a reasoned finding that the duplication is the correct steady state for this subsystem, with the reason stated in terms a future reader can act on. (b) is a valid and useful deliverable -- do not manufacture a refactor to avoid it. CONSTRAINTS: preserve every landed sorry-free result; do not entangle the discrete-completeness sorries in the bimodal tree, which are gated on a separate external port.

---

### 554. Cs5 pair seed disjunction property cutfree research
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: None
- **Research**:
  - [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/02_cutfree-literature-grounded.md]
  - [554_cs5_pair_seed_disjunction_property_cutfree_research/reports/04_route-closure-reverification.md]
- **Plan**: [554_cs5_pair_seed_disjunction_property_cutfree_research/plans/03_ra-probe-product-model.md]
- **Summary**: [554_cs5_pair_seed_disjunction_property_cutfree_research/summaries/03_ra-probe-summary.md]

**Description**: [RESCOPED 2026-07-26 by explicit user decision, adopting report 02 section 8.] Research on the CS5 pair-seed disjunction property is COMPLETE; two rounds of probes and a literature-grounded assessment are landed. The adopted route is section 8.2's narrow probe plus section 8.1's zero-risk landings. NOTHING ELSE IS IN SCOPE.

LAND NOW (mechanical, no research risk, do these first and independently):
(1) Fix the refutable statement per section 1.1 -- the named Prop CS5PairSeedDisjunctionProperty (Cslib/Logics/Modal/Metalogic/Constructive/CS5Completeness.lean) is REFUTABLE AS STATED and needs the `A not-in cl_CS5 (boxInv H)` hypothesis. Land probe_refute_disjunctionProperty as a regression test so the unconditioned form can never be reintroduced.
(2) Land round 1 section 4.1's promotions under the corrected statement: the hOpen <-> hR equivalence, hR -> hL, single-hypothesis derivExcludes, the retraction bound.
(3) Land cs5Axiom_to_is5Axiom / cs5_deriv_to_is5 / cs5_closure_subset_is5_closure -- small, library-grade, load-bearing for the product-model route.
(4) Docstring corrections: [Marin2021] is for IK, not CK, so drop the 'a correct proof is expected to require a cut-free/nested-sequent argument ([Marin2021])' claim; the applicable cut-free system is [ADS15] but at prohibitive cost (section 5.4 cost table); drop 'No semantic witness exists' (the product model is a genuine candidate); correct Non-Goal 2's stated reason.

THEN THE SINGLE PROBE (section 8.2, de-risk R-a before any planning): does every IS5-consistent set have an is5FC model with TOTAL r? This one decidable-by-probe question determines the whole product-model route. If R-a holds, the product construction is ~200-400 lines of standard induction and the task reduces to R-b. If R-a fails, the route is dead and this task closes [BLOCKED] with the section 5.4 cost table as justification -- a negative result is a valid deliverable.

EXPLICITLY NOT ADOPTED, do not re-propose: (a) opening a nested-sequent or labelled-calculus formalisation task (section 8.3, prohibitive cost); (b) the fallback collapse route deriving idb then bridging CS5 -> IS5 -- still not adopted, and section 6 adds an independent reason for wariness, namely that its published basis (Pacheco's CS5 = IS5) rests on the same unsound Lemma 16; (c) the two recorded dead ends (the circular semantic route via pair-axiom soundness, and the signature-collapse retraction).

TWO CONSUMERS: the native-Hilbert pair-Lindenbaum completeness task needs to know whether the named open Prop can be discharged; the labelled CS5 general-soundness task needs to know whether a context-fold that splits compound context facts is derivable without the box-over-disjunction bridge. Report on both explicitly. Machine-checked durable assets from the labelled front live under that task's probes/theta_place_*.lean (all compile clean, no sorryAx).

---

### 551. Cs5 native hilbert pair lindenbaum completeness
- **Effort**: large
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 554
- **Research**:
  - [551_cs5_native_hilbert_pair_lindenbaum_completeness/reports/01_route-b-native-hilbert-cs5-research.md]
  - [551_cs5_native_hilbert_pair_lindenbaum_completeness/reports/03_remaining-obligations-and-path.md]
- **Probe**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/probes/cs5-pair-combined-atomsum.lean]
- **Summary**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/summaries/01_native-hilbert-cs5-completeness-summary.md]
- **Plan**: [551_cs5_native_hilbert_pair_lindenbaum_completeness/plans/02_incremental-assets-deferred-route.md]

**Description**: Deliver NATIVE Hilbert canonical-model completeness for constructive CS5 over the fallible-world CKValid semantics (cs5_completeness'' : CKValidFC cs5FC'' phi -> Derivable CS5ModalAxiom phi), uniform with the CK/CT/CS4 column -- NOT via IS5 transport (Route A) or the labelled adequacy bridge (Route C). The single open obstruction is the box-backward truth-lemma case: B's symmetry forces a two-sided canonical relation whose witness is a simultaneous maximal-theory PAIR <H',T> with cross-conditions boxInv H' subseteq T, boxInv T subseteq H' and designated-formula exclusions Box A notin H', A notin T. Landed sorry-free: soundness cs5_axiom_sound'' over cs5FC'' (CS5.lean:366), the symmetric tail with symmetry-by-construction (cs5Tail_symm), the collapse axioms cs5_dia_or (k3) + cs5_dia_bot_imp_bot (k5), and 3 of 4 pair-Lindenbaum ingredients (seed/chain-union/component-maximality, probes/cs5-pair-primeness.lean). Every one-set canonical relation is MECHANICALLY refuted (cs5Incest_cs5CanonMreach_false, cs5Incest_cs5PrimeMreach_false, cs5TwoSidedR_iff_cs5Tail, general monotonicity collapse). Pacheco Lemma 18->16 is UNSOUND here (uses phi notin Theta => neg phi in Theta). The gap is component PRIMENESS of the pair: the natural cross-condition predicate Cons_Y Z := boxInv Z subseteq Y is not cl-stable, so prime_maximal_is_prime (PrimeExclusion.lean:428) does not apply. SKETCHED SOUND REPAIR (not built): encode the pair as a SINGLE quasi-prime theory over the doubled atom space Atom (+) Atom under a combined axiom system that internalises the two cross-condition implications, making them cl-stable by construction, then project back via Sum.inl/Sum.inr. Main risk R1: are the combined cross-condition axioms simultaneously sound and closure-stable without breaking per-component primeness -- de-risk in a probe (cs5-pair-combined-atomsum.lean) before any library edit.

---

### 537. Labelled cs5 general soundness biconditional
- **Effort**: 15-40 hours
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 554
- **Summary**:
  - [537_labelled_cs5_general_soundness_biconditional/summaries/02_gate-c-blocked-handoff-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/03_phase1-box-dia-iff-base-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/04_phase2-box-dia-iff-tclosure-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/04_phase4-2-boxI-lift-star-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/05_phase3-f2-here-helpers-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/06_phase6-forest-invariant-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/07_phase7-boxI-lift-partial-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/08_phase7-boxI-lift-complete-summary.md]
  - [537_labelled_cs5_general_soundness_biconditional/summaries/09_phase8-blocked-crosslabel-efq-summary.md]
- **Research**: [537_labelled_cs5_general_soundness_biconditional/reports/05_efq-orE-motive-defect-and-path.md]
- **Plan**: [537_labelled_cs5_general_soundness_biconditional/plans/06_target-independent-theta-translation.md]

**Description**: Prove the general labelled SOUNDNESS direction nik_TS5_soundness : NIKTheorem TS5 phi -> CKValidFC cs5FCIncest phi, completing Simpson 1994 Thm 8.1.4's biconditional for CSLib constructive CS5/IS5. CONTEXT (from parent task 517, which delivered the completeness direction): cs5_completeness (Completeness.lean:132) and the anti-vacuity certificate nik_TS5_consistent + nik_soundness_onePoint (Soundness.lean) are LANDED sorry-free/axiom-clean. cs5FCIncest_lift (Soundness.lean:181) is a landed building block. THE OPEN OBSTRUCTION (established across 3 dispatches, no forced sorry): TS5={T,B,Four} makes TClosure TS5 G.R the TOTAL relation on the always-connected derivation graph, so the box edge-condition is an r-CLIQUE condition across all labels, not tree-adjacency; and cs5FCIncest's hfour/hsymbox/hincest conjuncts only ever produce EXISTENTIALLY-raised relational witnesses, whereas CKForces's box clause (and boxE) need EXACT edges/symmetry between independently-fixed points (persistence is only upward). No asymmetric countermodel refuted the obstruction; no closure proof completed it -- GENUINELY OPEN. THREE CANDIDATE STRATEGIES (ranked; none is a plain direct-implementation dispatch -- each needs research/re-plan): (1) prove cs5FCIncest forces symmetric/clique closure on finitely-generated substructures -- cheapest, possibly reuses the FLO closure machinery from parent Phases 1-7; (2) formalize Simpson's own modified sequent system L_m(TS5, empty), his stated fix for exactly this problem; (3) build the deferred Simpson Ch.6 Hilbert-labelled ADEQUACY bridge (NIKTheorem TS5 phi -> Derivable CS5ModalAxiom phi) and obtain labelled soundness as a corollary of the already-landed Hilbert soundness cs5_soundness_derivable_incest (CS5Canonical.lean:373) -- note this resurrects the bridge task 517 deliberately avoided (Track C, C5 'THE TRUE CRUX'). Full analysis: specs/517_labelled_bounded_context_cs5_completeness/handoffs/phase-11-general-soundness-blocked-20260719c.md and Soundness.lean's refined-analysis docstring. CONSTRAINTS: NO sorry, NO new axiom under Cslib/; do not weaken cs5FCIncest; do not regress parent's landed completeness/anti-vacuity. Research MUST use --lit (Simpson Ch 8 soundness, Lifting Lemma 8.1.3, L_m modified sequent system). BibKeys: Simpson1994, MarinMoralesStrassburger2021. HIGH uncertainty (the direct route may be genuinely open). Start with strategy (1) as a research/probe pass before committing. Depends on 517.

---

### 534. Pure K5/5 Euclidean tableau completeness without the equivalence route
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511, Task 531, Task 553, Task 563, Task 564, Task 566, Task 567, Task 586

**Description**: COMPLETENESS GAP. The 5/Euclidean decidability currently in-tree (instDecidableFiveValid/instDecidableKb5Valid, FrameCompleteness.lean) is delivered via the KB5/S5 equivalence route, which leans on a full-equivalence closure. This task delivers genuine pure-K5 / pure-5 (Euclidean without full equivalence, no Mathlib closure operator) tableau soundness + completeness + decidability - the one modal-cube corner explicitly deferred out of the completed KB5/Euclidean task. Mirror the existing Five/KB5 development but over the bare Euclidean frame condition. Zero sorry, zero new axioms; keep the frozen equivalence-route deliverables untouched.

---

### 497. Reconcile imp naming
- **Status**: [RESEARCHED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 400
- **Research**: [497_reconcile_imp_naming/reports/01_arrow-notation-precedence-reconciliation.md]

**Description**: [RETARGETED 2026-08-10 — this task is NO LONGER an identifier rename. The rename is already done. What remains is the `→` NOTATION gap. All claims below were verified directly against fork `main` and `upstream/main` @ `3951377e` (fetched 2026-08-10); re-verify before acting, the commands are cheap.]

Reconcile the fork's `→` notation for the implication connective with upstream. Originally raised in review of PR #648 by thomaskwaring as an `imp` vs `impl` naming question; that naming question has since resolved itself, and the notation divergence underneath it has not.

=== THE IDENTIFIER RENAME IS ALREADY COMPLETE — DO NOT RE-LITIGATE ===

Fork `main` already uses `imp` for every connective identifier. All five `→` notation declarations bind to a `.imp` field:

  Cslib/Logics/Bimodal/Syntax/Formula.lean:101   => Formula.imp
  Cslib/Logics/LTL/Syntax/Formula.lean:209       => Formula.imp
  Cslib/Logics/Modal/Basic.lean:234              => Proposition.imp
  Cslib/Logics/Propositional/Defs.lean:109       => Proposition.imp
  Cslib/Logics/Temporal/Syntax/Formula.lean:169  => Formula.imp

Only 4 `impl` tokens survive anywhere in `Cslib/` on `main`, all in
`Cslib/Foundations/Logic/Theorems/Propositional/Connectives.lean` lines 469, 471, 502, 504 — and
all four are a LOCAL TACTIC HYPOTHESIS NAME (`have impl := ModusPonens.mp bc dne_ψ`), not a
connective identifier. Renaming them is cosmetic and optional, not part of the reconciliation.

CORRECTION TO THE PRIOR (2026-08-10) REVISION: that revision claimed "MODAL'S `impl` IS THE
OUTLIER" and told a future reader to expect a rename in `Modal`. That claim is FALSE for `main`
— `Modal/Basic.lean:234` already reads `Proposition.imp`. It is corrected here rather than
deleted because it is the reason this task has looked far larger than it is.

The rename did NOT arrive from upstream. It landed independently in commit `c308d028`
("refactor modal formula, satisfies, and cube"), which IS an ancestor of `main`, well before
PR #607. `impl` appears ZERO times in any upstream `.lean` file. `impl` now survives only on
three unmerged feature branches (`feat/propositional-v2`, `feat/modal-formula-primitives`,
`feat/temporal-formula-propositional`); those are stale snapshots and whether they are rebased
or abandoned is OUT OF SCOPE here.

=== THE ACTUAL REMAINING GAP: NOTATION, IN THREE PARTS ===

Upstream, in `Cslib/Foundations/Logic/Operators.lean` (added by PR #607, commit `b8ad3923`,
merged 2026-08-03), declares:

  class HasImp (α : Type*) where
    imp (a b : α) : α

  @[inherit_doc] scoped infixr:25 " → " => HasImp.imp

Against that, the fork diverges in three ways:

(a) PRECEDENCE — fork `infix:30` vs upstream `infixr:25`.

(b) ASSOCIATIVITY — fork uses non-associative `infix`; upstream uses right-associative `infixr`.
    This is the higher-severity half: `a → b → c` parses upstream and FAILS in the fork. Worse,
    because the fork's notation is non-associative, Lean's own `Prop`-level arrow wins the
    overload, so a chained expression surfaces as a TYPE MISMATCH rather than a notation error —
    materially harder to diagnose.

(c) STRUCTURE — upstream binds `→` ONCE, at the typeclass. The fork binds it FIVE times, once per
    concrete formula type, at the five sites listed above.

REFINEMENT TO (c), NOT PREVIOUSLY RECORDED AND MATERIAL TO COST: the fork ALREADY HAS `HasImp`.
It is declared at `Cslib/Foundations/Logic/Connectives.lean:85`, in the SAME namespace
`Cslib.Logic` as upstream's, with the SAME field name `imp` (`imp : F → F → F`, definitionally
upstream's `imp (a b : α) : α`), and it has 1039 usage sites across the fork. What the fork lacks
is any NOTATION bound to it: `git grep -E '(infix|infixr|infixl|notation).*HasImp' main` returns
ZERO. So part (c) is "rebind the arrow to an existing class field", not "introduce a typeclass".
That is much cheaper than the earlier framing implied — but see the sequencing section, because it
is also the part most likely to be done by someone else first.

=== SEQUENCING — READ THIS BEFORE PLANNING; MOST OF THIS TASK MAY ALREADY BE SPOKEN FOR ===

The dependency graph does NOT gate this task: its sole dependency (400, the
`reconcile_connectives_pr607` falsum-representation decision) is `status=completed`. But that
task's completion carved out three follow-ups whose scopes OVERLAP this one, and the plan phase
MUST resolve the overlap explicitly rather than assume it away:

  - 621 `propositional_notation_infixr` — changes all five connective notations in
    `Cslib/Logics/Propositional/Defs.lean` from `infix` to `infixr` at upstream's precedences.
    Its `file_scope` is exactly `["Cslib/Logics/Propositional/Defs.lean"]`. It therefore ALREADY
    OWNS parts (a) and (b) for `Defs.lean:109`. Do not duplicate that edit here.
  - 619 `reconcile_connectives_operators` — reconciles the fork's `Connectives.lean` against
    upstream's `Operators.lean`, where `HasAnd`/`HasOr`/`HasImp`/`HasBox` are duplicated in
    namespace `Cslib.Logic`. Part (c) lives inside that reconciliation's blast radius: where `→`
    should bind is a consequence of which `HasImp` survives.
  - 620 `rebase_pr648_clear_review` — also touches `Propositional/Defs.lean` and carries a
    STANDING APPROVAL against a specific approved scope; widening that diff forfeits the approval.
    (621 already declares a dependency on 620 for exactly this reason.)

WHAT IS LEFT THAT IS UNIQUELY THIS TASK'S: the `→` notation in the FOUR files 621's scope does not
reach — `Bimodal/Syntax/Formula.lean:101`, `LTL/Syntax/Formula.lean:209`, `Modal/Basic.lean:234`,
`Temporal/Syntax/Formula.lean:169`. All four declare `@[inherit_doc] scoped infix:30 " → "`, and
all four carry the same non-associativity hazard, alongside equally non-associative sibling
connectives. None is covered elsewhere today. Planning should either (i) narrow this task to those
four files and defer (c) to 619, or (ii) argue for folding it into one of the siblings — but it
must CHOOSE, and record the choice.

Second sequencing axis: adopting `infixr:25` standalone and adopting `HasImp` as part of merging
#607 are DIFFERENT JOBS, and doing the first can make the second redundant. Fork `main` is 21
commits behind `upstream/main` and has NO `Cslib/Foundations/Logic/Operators.lean`; `b8ad3923` is
NOT an ancestor of `main`. So the upstream sync is genuinely still pending despite the falsum
decision having completed. Decide sequencing against that sync explicitly rather than assuming.

=== SCOPE — THE OLD ESTIMATE IS DEAD ===

The previous "~271 files" figure is WITHDRAWN. It was never verified, and it is meaningless now
that the rename it estimated is already done. Do NOT substitute a grep for `→` as a proxy: that
matches 547 files under `Cslib/` but overwhelmingly hits Lean's own function arrow rather than the
connective, so it is not a usable figure. True scope must be derived at planning time from the
five notation declaration sites plus the TRANSITIVE PARSE IMPACT of the associativity change —
i.e. the sites that currently rely on the non-associative parse and will need fixing once `→`
becomes right-associative. Verify with `lake build` that the tree stays green.

Note on relative precedence, so planning does not over-worry: the fork's ordering
(∧ 36 > ∨ 35 > → 30 > ↔ 20) and upstream's (∧ 36 > ∨ 30 > → 25 > ↔ 20) agree on ORDER, so moving
`→` from 30 to 25 alone does not invert any relationship. The sibling connectives' absolute levels
still differ from upstream (notably `∨` at 35 vs 30); that is a real remaining divergence but it
belongs to the notation-wide reconciliation, not to this arrow-scoped task, unless planning
deliberately widens.

RECORD DEFECT, STILL OPEN: `file_scope` is ABSENT from this task's record and must be backfilled.
Once planning narrows the scope per the sequencing section above, set it — the four
non-Propositional formula files are the likely value.

DEPENDENCY CLEANUP (applied 2026-08-10, still accurate): the previous dependency list was
[375, 393, 400, 425, 449, 535, 542]. Of those, 375, 393, 449, 535 and 542 are archived/completed.
The edge to 425 (temporal tableau decision procedure) was spurious — nothing about a temporal
tableau gates a propositional connective notation change. Dependencies are now [400] alone, and
400 is completed.

=== NARROW-VS-FOLD DECISION: RESOLVED 2026-08-10 — NARROW, WITH BUILD EVIDENCE ===

The sequencing section above asks planning to choose between (i) narrowing to the four
non-Propositional files and (ii) folding into a sibling. THAT CHOICE IS NOW MADE: NARROW.
`file_scope` is set accordingly and no longer needs backfilling.

It was decided empirically, not by argument. The hypothesis under test was that splitting PL
from the other four logics is unsafe: 19 files open two of the five scoped logic namespaces at
once (18 of them pair `PL` with another) — essentially the whole `ConservativeExtension` family,
because conservative-extension proofs are exactly where a propositional formula is related to
its modal/temporal embedding. The worry was that PL at `infixr:25` alongside Modal/Bimodal/
Temporal at `infix:30` would put the same `→` token in scope at two precedences AND two
associativities simultaneously.

THE HYPOTHESIS IS REFUTED. The PL-only change (all four `infix` declarations moved to `infixr`
at upstream precedences) was applied to `Cslib/Logics/Propositional/Defs.lean` and all 19
mixed-namespace modules were built against it — `lake build`, 928 jobs, exit 0, zero errors.
Verified by `.olean` mtimes postdating the source edit, so these are genuine rebuilds, not stale
cache. The `scoped` notations resolve by type (`Proposition` vs `Formula`), so the elaborator
disambiguates and the precedence difference never becomes a parse conflict. The experimental
edit was reverted; the tree is clean.

CONSEQUENCE: the four sites in this task's `file_scope` can move independently of
`Propositional/Defs.lean`. Task 621 may land before, after, or concurrently with this task
without a coordinated build.

SECOND REASON NARROW WON, INDEPENDENT OF THE BUILD: 621 depends on 620, which carries a standing
approval scoped to `Propositional/Defs.lean`. Folding these four files into 621 would couple
Bimodal/LTL/Modal/Temporal to that approval gate for no technical reason.

STILL TRUE AND UNCHANGED: part (c) — rebinding `→` to the existing `HasImp` (declared at
`Cslib/Foundations/Logic/Connectives.lean:85`, 1039 usage sites, currently with NO notation bound
to it) — remains 619's, not this task's.

PRE-EXISTING BLOCKER FOUND WHILE TESTING, NOT CAUSED BY IT: a full `lake build` on `main` does
not complete. It stalls indefinitely on `Cslib/Logics/Propositional/Tableau/Intuitionistic/
Scheme.lean` (9,884 lines) — 92 minutes of pegged CPU at 1.3 GB RSS with no completion, and no
cached `.olean` for that module at all, i.e. it has never built in this checkout. That is tracked
separately. It gates FINAL verification of this task (and of 619/620/621), though not the
targeted per-module builds used above.

---

### 450. Prove TM (Bimodal Base) conservative over BX+ and close the TemporalConservativity sorry
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 181, Task 449

**Description**: Core corrected conservativity result. PR-BLOCKING for task 180. Supersedes abandoned task 445 and inherits its research: specs/445_fix_temporal_conservativity_domain_mismatch_sorry/reports/01_domain-mismatch-transfer-feasibility.md and 02_literature-grounded-conservativity-obstruction.md. Depends on task 449 (BX+ definition).

TARGET: Bimodal.ThDerivable = DerivationTree Bimodal.FrameClass.Base (Cslib/Logics/Bimodal/ProofSystem/Derivation.lean:111,119), and Bimodal Base includes the 5 uniformity axioms. The honest theorem is therefore:
  bimodal_conservative_over_temporal : Bimodal.ThDerivable phi.toBimodal -> BXplus.ThDerivable phi
where BXplus = DerivationTree Temporal.FrameClass.Metric (from task 449).

RESEARCH PHASE MUST SETTLE THE PROOF ROUTE:
- Route (i) SYNTACTIC box-erasure (preferred; needs no completeness result). Define eraseBox : Bimodal.Formula -> Temporal.Formula, prove Bimodal.DerivationTree FrameClass.Base G phi -> Temporal.DerivationTree FrameClass.Metric (G.map eraseBox) (eraseBox phi) by induction on the derivation tree, then specialise via eraseBox (phi.toBimodal) = phi (Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean). CRUX to verify per-axiom with lean_multi_attempt: S5 axioms for box erase to tautologies; the pure-temporal and uniformity axioms erase to BX+ axioms; the MODAL-TEMPORAL INTERACTION axioms modal_future (box phi -> box(G phi)) and discrete_box_necessity (chi -> box chi) are the only load-bearing cases. The definition of eraseBox on box must be chosen so BOTH land as BX+ theorems: naive eraseBox(box psi) = eraseBox(psi) sends modal_future to phi -> G phi, which is FALSE, so a smarter erasure is required. Ground the correct construction in Thomason 1984 (Combinations of Tense and Modality).
- Route (ii) SEMANTIC transfer. Uses BX+ completeness over group flows (task 451) + trivial bimodal expansion + Bimodal soundness, via contrapositive. Only viable once task 451 has landed; if research selects this route, add a dependency on task 451.

IMPLEMENTATION: In Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean, REPLACE the false temporal_valid_of_bimodal_derivable (:269), restate bimodal_conservative_over_temporal over BX+, and REMOVE set_option warn.sorry false in (:248) and the sorry (:269). Rewrite the module docstring's "Domain Mismatch Resolution" section to the correct account: TM is conservative over METRIC tense logic BX+, not over plain BX (cite Burgess1984 sec 6.1 and Thomason1984). This task OWNS TemporalConservativity.lean; task 444's naming/lint sweep runs AFTER this task so it sees the settled file.

Zero-debt: lean_verify on the restated bimodal_conservative_over_temporal must report only [propext, Classical.choice, Quot.sound] with zero sorry; full CI green. If a genuine load-bearing obstruction is hit, escalate with the exact open goal and candidate lemmas; do NOT reintroduce a sorry or a vacuous (:= True / trivial) placeholder.

---

### 425. Temporal tableau ptl fmp decidability
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 552
- **Plan**:
  - [425_temporal_tableau_ptl_fmp_decidability/plans/03_validity-corrected-fmp-plan.md]
  - [425_temporal_tableau_ptl_fmp_decidability/plans/01_ptl-fmp-decidability-plan.md]
- **Summary**: [425_temporal_tableau_ptl_fmp_decidability/summaries/01_ptl-fmp-summary.md]
- **Research**: [425_temporal_tableau_ptl_fmp_decidability/reports/04_island-vs-periodic-strategic-decision.md]

**Description**: [Decomposed from the temporal tableau umbrella, blocker C.] BLOCKER CLEARED 2026-07-26: the shared conformance/rule-completeness repair this was gated on is COMPLETE. It landed the per-branch eventuality tracker (temporalStepBranch now returns one tracker per output branch, so untlPos's branch1/branch2 genuinely diverge in their pending sets), the temporal rule arms (seriality, G/H duality, transitive propagation), cap removal and fuel raise, and fixed two real directional defects in ancestorTimes / allPastPosAt. Cslib/Logics/Temporal/Tableau/Completeness.lean:127-140 now marks remaining-work items 1, 2 and 2a as Done. REMAINING SCOPE, restated: prove the fuel-sufficiency/pigeonhole theorem -- that temporalFuel guarantees isSubsetBlocked holds among a fuel-exhausted branch's own labels whenever pending eventualities remain. That is the sole prerequisite for wiring extractModelZPeriodic / periodicReducePast in as the real extractModelZ, and then discharging temporalTruthLemma_untl / _snce, openBranch_branchSat, eventualityDefect_unsat, temporalTableau_sound, temporalTableau_complete and the final instDecidableValid. NOTE THIS IS A DISTINCT OBLIGATION from the intuitionistic persistence-fixpoint fuel measure (that one is closed); do not conflate them. Mirror COMPLETED task 421 (min_fmp_decidability), which added a sorry-free Decidable instance via FMP -- reuse its pattern where possible. RESEARCH FIRST: Completeness.lean:138-140 explicitly recommends a dedicated research pass before further planning; run /research before /plan. Gates the temporal tableau umbrella.

---

### 409. Literal ⊥-rule-free base ND inductive (option B): split MinDerivation + Explosion; re-cut Curry-Howard & normalization
- **Status**: [ABANDONED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: Task 407
- **Research**: [409_bot_rule_free_nd_option_b/reports/01_bot-free-nd-option-b-research.md]

**Description**: SPAWNED from task 407 (MPL structure-first redesign), Wave 6 -- OPTIONAL / advanced. Task 407 adopts option C (re-frame the task-398 gated efq constructor as the explosion property module; the base relation is ⊥-rule-free UP TO the IsIntuitionistic gate). Option B is the LITERAL structure-first ND: split Theory.Derivation into a genuinely ⊥-rule-free base inductive MinDerivation (no efq constructor) plus an Explosion extension, prove all structural metatheory once on the base, and recover IPL-ND by adjoining efq. TRIGGER CONDITION: only pursue if a concrete downstream consumer needs a physically ⊥-free derivation object (e.g. a minimal-ND normalization theorem, or a lambda-calculus without an abort/efq combinator). COST/RISK: re-opens the single genuinely hard point from task 398 -- the subformula property under efq -- and forces re-cutting Curry-Howard (Theory.Term mirror) and Prawitz normalization (Basic/Reduction/Termination/SubformulaProperty) against the split. Reuse the task-398 decided strategy (atomic restriction + permutation conversions); treat any non-green proof as [BLOCKED], never sorry. HIGH effort -- use --hard. Depends on 407 (and ideally 408). Source: task 407 report 01 §5 option B / §7 W6, report 02 §5. ALIGNMENT NOTE: this two-inductive split is the Design-B-flavored route that the universal-algebra approach (task 407 option C) deliberately AVOIDS, because it duplicates derivation structure (exclude-then-add at the derivation level). Default remains task 407 option C: ONE derivation type with explosion as a property module. Pursue 409 ONLY if the trigger condition above fires.

---

### 400. Falsum representation decision: keep primitive bot; rebase PR #648
- **Status**: [COMPLETED]
- **Task Type**: cslib
- **Topic**: Propositional Logic
- **Dependencies**: None
- **Research**:
  - [400_reconcile_connectives_pr607/reports/01_pr607-engagement.md]
  - [400_reconcile_connectives_pr607/reports/02_engagement-strategy.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/01_comparison-tables.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/02_falsum-bridge-sketch.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/03_grind-direction-finding.md]
  - [400_reconcile_connectives_pr607/review-scaffolding/04_review-packet.md]
  - [400_reconcile_connectives_pr607/reports/03_falsum-representation-decision.md]
- **Plan**: [400_reconcile_connectives_pr607/plans/02_pr607-engagement.md]

**Description**: [REVISED 2026-08-10 — SECOND revision. The first revision's load-bearing premises were verified FALSE against the live record; corrected below. Decision landed: OPTION B.]

DECISION MADE. Research deliverable complete: reports/03_falsum-representation-decision.md (section 9 is a standalone action checklist). Recommendation: OPTION B — keep the fork's primitive `bot`.

=== WHAT THE FIRST REVISION GOT WRONG (verified 2026-08-10 against freshly fetched refs; upstream/main = 3951377e) ===

CORRECTION 1 — "PR #607 settled the falsum question AGAINST the fork's design" is FALSE.
  - `instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩` was introduced in commit 61785643, "feat(Logics/Propositional): definitions (#89)" — the ORIGINAL definitions commit, four PRs before #607.
  - #607 is commit b8ad3923, "feat(Logic): logical operators", touching 9 files. Its ONLY constructor-level change to `Proposition` was the rename `impl` -> `imp`. It did not add, remove, or alter any constructor, and did not touch the `Bot` instance. The bot-as-atom lines appear in its diff as UNCHANGED CONTEXT.
  - #607 is therefore ORTHOGONAL to the falsum representation question. No falsum decision was made there, so there is nothing to have "settled against". The premise that motivated Option A does not exist.

CORRECTION 2 — "PR #648 carries CHANGES_REQUESTED [read as standing opposition]" is MISLEADING.
  Review record (`gh pr view 648`, read-only):
    2026-06-15  ctchou         CHANGES_REQUESTED
    2026-07-06  thomaskwaring  APPROVED
    2026-07-13  benbrastmckie  COMMENTED x5 (answering all five inline comments)
  - thomaskwaring APPROVED after negotiating a compromise on Zulip (2026-06-28: "if we are going to have bot as a primitive, we should also have efq"), which was implemented 2026-06-29. His 2026-06-16 objection — the one the first revision quoted — was SUPERSEDED by his own later approval.
  - ctchou's is the only outstanding blocking review, and its FIRST bullet reads verbatim: "I like the idea of adding \bot as a primitive." Its four points are procedural: file organization (why both Semantics/Basic.lean and Semantics/Bool.lean), references (prefer Avigad's textbook over 1930s German sources), and "You should definitely coordinate this PR with #607 and #587. #536 is ready to merge, so you should wait for it."
  - That coordination instruction is now ACTIONABLE: #607 has merged.
  - There is NO standing technical opposition to primitive bot on the record. A third participant (Matthew Doty) independently backed it on DPLL grounds.

CORRECTION 3 — "the HasBot prediction held" OVERSTATES.
  The fork's own review-scaffolding/02_falsum-bridge-sketch.md had ALREADY retracted the HasBot recommendation: Mathlib's `Bot`/`Top` supply the notation and the fork already uses them, so a five-primitive `Proposition` registers against merged #607 with ZERO new typeclasses. No `HasBot` was needed, so its absence is not a gap.
  The real finding is a DOCUMENTATION BUG in merged upstream code: upstream `Cslib/Logics/Propositional/Defs.lean:36-37` promises `HasBot (Proposition Atom)` and `HasTop (Proposition Atom)` instances for classes that exist NOWHERE upstream. #607's own diff added that text.

CORRECTION 4 — the notation divergence is WORSE than described, and not confined to the arrow.
  ALL FIVE fork connectives are non-associative `infix`, vs upstream `infixr`:
    fork:     and infix:36,  or infix:35,  imp infix:30,  iff infix:20,  not prefix:40
    upstream: and infixr:36, or infixr:30, imp infixr:25, iff infixr:20, not notation:max
  Empirically verified: `a → b` parses, `a → (b → c)` parses, but `a → b → c`, `a ∧ b ∧ c`, and `a ∨ b ∨ c` ALL FAIL — and they fail as Prop-level TYPE MISMATCHES (Lean's own `And`/`Or`/`→` win the overload), not as notation errors, which makes them materially harder to diagnose. Relative precedence ORDERING is preserved between fork and upstream.

=== THE DECISION ===

OPTION B — keep the fork's primitive `bot`. Note that "re-argue" overstates the work required: the argument was already won on the record before #607 merged, and there is no standing opposition to overcome.

Measured basis for REJECTING OPTION A (migrate to four constructors with `.atom ⊥`):
  - 512 of 1,614 declarations in Propositional/ (31.7%) would acquire a `[Bot Atom]` gate.
  - 165 `.bot` token lines across 39 files; 120 match-arm lines; 50 fully-qualified `Proposition.bot`; 790 bare `⊥` glyph occurrences. (Repo-wide `.bot` is 2,287 lines across 228 files, but that figure includes Modal/Temporal/Bimodal/LTL formula types carrying their own primitive bot — not all PL.Proposition.)
  - Three central semantic definitions (Tautology, IValid, and substitution closure) change MEANING, not merely signature.
  - All three tableau DecisionProcedure files currently carry only `[DecidableEq Atom] [Hashable Atom]`; MValid/IValid carry only `{Atom : Type u}`. The `[Bot Atom]` gate propagates into all of them.
  - Risk is borne by a 42,166-line, zero-sorry development (0 sorries in Propositional/; 1 repo-wide).
  - The one genuine benefit — MValid loses its `bot_forces` quantifier (thomaskwaring's argument, correct for minimal logic taken alone) — is outweighed within the same development, because the IPL and CPL layers pay a side-condition tax to buy it.

Basis for REJECTING OPTION C (accept divergence): forfeits a 42k-line sorry-free development that two upstream reviewers signalled they want; blocks #649; and does not even avoid the Connectives/Operators reconciliation work, which is required under every option.

=== PR #648 DISPOSITION ===

REWORK AND REBASE. Do not close. Do not leave pending.
  - Keep scope EXACTLY as approved: four files, ungated efq, IPL base, minimal logic deferred.
  - Do NOT widen to the fork's current `[IsIntuitionistic T]`-gated efq design. That is the deferred fragment work thomaskwaring explicitly agreed to postpone; widening it forfeits a standing approval.
  - Rebase onto upstream/main @ 3951377e, absorbing: the v4.33.0-rc1 -> v4.33.0 toolchain and Mathlib pin bump; #753's InferenceSystem/Congruence refactor; and the IsIntuitionistic/IsClassical shape reconciliation below.
  - Re-request review from ctchou, itemising the four dispositions. Note that thomaskwaring's approval stands — it should be cited, not re-litigated.
  - The GitHub text must be HUMAN-AUTHORED per the CSLib AI policy. Chris Henson formally challenged an LLM-drafted message on this exact Zulip topic (near/605827029). No agent-drafted GitHub or Zulip prose exists for this task, deliberately.

=== NEWLY SURFACED — NOT NAMED IN THE FIRST REVISION ===

IsIntuitionistic/IsClassical SHAPE DRIFT. The fork's Propositional/Defs.lean does not import InferenceSystem and states these as theory-membership predicates (`(bot → A) ∈ T`, Defs.lean:166,175), while upstream states them over an inference system (`S⇓`, `[InferenceSystem S (Proposition Atom)]`). PR #648 had ALREADY reconciled this against #536; the fork's main has since drifted BACK. 80 files in the fork reference InferenceSystem — just not from Propositional/Defs.lean. This is a reconciliation obligation under EVERY option and must be folded into the #648 rebase.

CONNECTIVES/OPERATORS COLLISION. Four classes are duplicated in namespace `Cslib.Logic` between the fork's Foundations/Logic/Connectives.lean and merged Operators.lean: HasAnd, HasOr, HasImp, HasBox. Upstream additionally has HasIff, HasNot, HasDiamond; the fork names its own `HasDia` where upstream says `HasDiamond`. Must be resolved under EVERY option; prerequisite for #649; independent of falsum.

TOOLCHAIN DRIFT IS NOT A DIFFERENTIATOR. The 21 unmerged upstream commits include a bump to v4.33.0 (fork pins v4.33.0-rc1; Mathlib pin 169c26b5 vs upstream v4.33.0). One release-candidate of drift, identical work under A, B, and C — a prerequisite for the #648 rebase only, not an input to the option choice.

=== DOWNSTREAM PRs ===

#649 (LTL) DEPENDS on the propositional base — its changed files include Propositional/{Defs.lean, NaturalDeduction/Basic.lean, NaturalDeduction/Theory.lean} plus Foundations/Logic/Connectives.lean; it is stacked on #648.
#662 (Modal semantics) DOES NOT depend on it — its changed files are Modal/{Basic,Cube,Denotation,LogicalEquivalence}.lean plus references.bib, and upstream Modal/Basic.lean imports only Operators/InferenceSystem/Relation.Euclidean/Mathlib, with no Logics.Propositional import.

=== SCOPE AND STATE ===

Research deliverable COMPLETE. Orchestration deliberately halted at [RESEARCHED] by user direction — no plan or implement phase was run, and none should be inferred as pending. No .lean file was created, moved, or edited under this task. Nothing was posted to GitHub or Zulip; all gh and Zulip access was read-only.

Three follow-ups, NONE started here: (1) rebase and clear review on #648 per the disposition above (needs human-authored GitHub text); (2) reconcile Foundations/Logic/Connectives.lean against merged Operators.lean; (3) switch the fork's five Propositional notation declarations from `infix` to `infixr` at upstream precedences (low-risk, self-contained, orthogonal to falsum).

The imp/impl naming reconciliation task is UNBLOCKED and its direction is determined: upstream landed `HasImp.imp` and the fork already uses `imp`.

---

### 301. Temporal tableau
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Temporal Logic
- **Dependencies**: Task 425
- **Research**: [301_temporal_tableau/reports/01_temporal-tableau-decision-procedure.md]
- **Plan**: [301_temporal_tableau/plans/01_temporal-tableau-decision-procedure.md]

**Description**: Implement tableau decision procedure for temporal logic (Cslib.Logic.Temporal.Formula) with until/since decomposition rules, time labels, and temporal ordering tracking. Most complex new tableau: until/since rules have no modal analogue, requiring branching decomposition with event-witness and guard-continue alternatives. Adapt patterns from bimodal decidability system (TimeOrdering, temporal rule structure, frame-class rules) but build fresh implementations on shared Foundations infrastructure. Include density and discreteness frame-class rules. Formula type has atom, bot, imp, untl, snce primitives using Lukasiewicz encoding. Files under Cslib/Logics/Temporal/Tableau/: Defs.lean, Rules.lean, TimeOrdering.lean, Branch.lean, Closure.lean, Saturation.lean, Soundness.lean, Completeness.lean. Estimated: 2,000-2,500 lines.

---

### 300. Modal extensions t s4 s5
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Modal Logic
- **Dependencies**: Task 511
- **Research**:
  - [300_modal_extensions_t_s4_s5/reports/01_frame-specific-tableau-extensions.md]
  - [300_modal_extensions_t_s4_s5/reports/02_spawn-analysis.md]
- **Plan**: [300_modal_extensions_t_s4_s5/plans/01_frame-extensions-implementation.md]

**Description**: Umbrella task for modal frame extensions T/S4/S5 (and the derived B/D/5/Euclidean cube corners). RECONCILED: T (instDecidableTValid), B (instDecidableBValid), S5 (instDecidableS5Valid), and 5/Euclidean (instDecidableFiveValid/instDecidableKb5Valid) are all delivered sorry-free in Cslib/Logics/Modal/Tableau/FrameCompleteness.lean via the generic tableau driver. The SOLE remaining phase is S4 (reflexive-transitive) loop-checking termination bound and decidability, tracked by task 506 (gated on the S4 termination task). This umbrella closes when S4 decidability (instDecidableS4Valid) lands.

---

### 215. Fill the discrete-gated Bimodal sorries (BXCanonical Chronicle and Frame)
- **Status**: [BLOCKED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 36
- **Research**: [215_fill_bimodal_sorries/reports/01_sorry-analysis.md]

**Description**: Fill the discrete-gated sorry declarations in Cslib/Logics/Bimodal/Metalogic/:
- BXCanonical/Chronicle/ChronicleToCountermodel.lean: 12 sorries (lines 75, 145, 146, 152, 157, 162, 172, 173, 174, 175, 176, 187)
- BXCanonical/Frame.lean: 1 sorry (line 161)

All are gated on the discrete completeness pipeline (discrete_embed_strictMono, gap_contradicts_prior, the discrete FMCS construction), which the discrete port task delivers. Counts above are as measured 2026-07-26, superseding the earlier asserted figures. The strict-Until/Since sorries are tracked separately. Note: countermodel_dense (ChronicleToCountermodelBasic.lean:825) and completeness_dense (Dense.lean:122) were carved off previously and remain out of scope.

---

## LINE NUMBERS ARE STALE (repo-wide lint/CI audit)

The line numbers in the body above are dated 2026-07-26 and have since moved -- the repo-wide lint-hygiene pass rewrapped long lines, deleted blank lines inside single-command blocks, and narrowed blanket linter suppressions to declaration scope across these files. RE-DERIVE EVERY LINE NUMBER LIVE (`grep -n sorry <file>`) before acting; do not trust the recorded positions.

The FILE-LEVEL scope and the sorry COUNTS per file are unchanged and remain accurate. The sorries in these files are currently hidden from `lake build --wfail --iofail` by `set_option warn.sorry false in` markers; filling them must also DELETE the corresponding marker, so the suppression count drops with the sorry count. A suppression ratchet is being added under a separate task to enforce exactly that.

---

### 181. Bimodal primitive dia always historically
- **Status**: [NOT STARTED]
- **Task Type**: cslib
- **Topic**: Bimodal Logic
- **Dependencies**: Task 180, Task 393
- **Research**: [181_bimodal_primitive_dia_always_historically/reports/01_bimodal-primitive-expansion-research.md]

**Description**: Propagate primitive diamond, allFuture, and allPast constructors to the Bimodal layer, giving {atom, bot, imp, and, or, box, dia, untl, snce, allFuture, allPast} (11 primitives). This is the union of Modal (task 179) and Temporal (task 180) primitive sets. Scope: (1) Syntax/Formula.lean: add .dia/.allFuture/.allPast constructors, update all match cases. (2) Semantics/Truth.lean: structural truthAt clauses. (3) ProofSystem: axiom constructors for diamond duality and G/H axioms. (4) Embedding: extend ModalEmbedding (.dia), TemporalEmbedding (.allFuture/.allPast). (5) Metalogic: propagate through ~50 files (Core, Soundness, Completeness, BXCanonical, ConservativeExtension, Separation, Decidability, Algebraic). Follow task 177 playbook. (6) Classical equivalences become theorems. Verify full CI. Estimated ~50 files, ~2000 lines, similar scope to task 177.

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
- **Topic**: Bimodal Logic
- **Dependencies**: None

**Description**: Port continuous extension completeness once developed upstream. The continuous case (FrameClass for continuous/real-valued time) has not been started in BimodalLogic. This task is blocked pending upstream development of continuous frame completeness.

**Source**: Not yet developed in BimodalLogic
**Target**: Cslib/Logics/Bimodal/Metalogic/
**Blocker**: Upstream BimodalLogic continuous extension development
**Parent task**: 8 (expanded)

---

### 36. Port discrete completeness bimodal
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: Bimodal Logic
- **Dependencies**: None

**Description**: Port discrete completeness (completeness_discrete) from upstream BimodalLogic. EXTERNAL BLOCKER CLEARED 2026-07-26 (verified directly against the upstream working tree, not against prior notes): upstream Theories/Bimodal/Metalogic/BXCanonical/Completeness.lean:302 now documents completeness_discrete as sorryAx-free, with #print axioms giving exactly [propext, Classical.choice, Quot.sound]. The chain this task was blocked on (chronicle_gap_contradiction -> succ_cofinal -> limitDomSubtype_isSuccArchimedean -> succ_embed_surjective) was DEAD CODE on no live call path and has been archived upstream to Boneyard/DeadChronicleGapElimination/. succ_cofinal itself remains provably unfixable (Z+Z counterexample) and is correctly bypassed. SCOPE HAS CHANGED -- DO NOT PORT FROM THE OLD DESCRIPTION. The live discrete path is countermodel_discrete_reynolds_v2 (WeakCanonical/IntegerModel/ReynoldsBridge.lean:739) -> limitdom_is_good -> no_gaps_discrete_model_surgery -> US_expressively_complete_over_prior -> kamp_prior_expressive_completeness -> nf_characterizable_temporal_prior -> nf_nvar_exist_all_depths, with the formerly-sorry |_k+2 arm retired by the zeta wire kampArm_zeta (ZetaUniformExtract.lean, the unary E[Sigma]-atom re-architecture of Rabinovich Def 4.1 / Prop 4.3 / Thm 4.4). The port surface is therefore ReynoldsBridge + the Kamp/KampPrior/ZetaUniformExtract cluster, NOT the '~6 IntegerModel files' originally scoped. Note that IntegerModel/GoodStructuresModelSurgery.lean still carries two sorries (gap_prior_UZ_contradiction / gap_prior_SZ_contradiction, Reynolds Lemmas 6-13) -- confirm at port time whether the live path depends on them or whether they sit on the alternative route. RUN /research AND /revise BEFORE /implement: the port map must be re-derived against the current upstream tree before any plan is written. Target: Cslib/Logics/Bimodal/Metalogic/. Unblocks 12 of the bimodal sorries and the temporal discrete completeness task.
