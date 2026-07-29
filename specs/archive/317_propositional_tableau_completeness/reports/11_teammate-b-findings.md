# Teammate B Findings: Alternative Approaches / Prior Art (Task 317)

## Key Findings

1. **The "discharge parametrically" mandate is already satisfied — it is not new work.**
   `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` already defines
   `IntMinScheme` (a structure bundling `closurePred`/`modelBot`/`bot_truth`/`no_contradiction`,
   lines 118-146), with two data instances `intScheme` (line 159) and `minScheme` (line 208).
   The parametric `truthLemma` (line 555), `openBranch_countermodel`, and `tableau_complete` are
   all stated and proved ONCE against `S : IntMinScheme Atom`. `Intuitionistic/Completeness.lean`
   and `Minimal/Completeness.lean` are thin corollaries (`intTruthLemma`/`minTruthLemma`,
   `intuitionisticTableau_complete`/`minimalTableau_complete`) that each call `truthLemma
   intScheme`/`truthLemma minScheme` directly (`Completeness.lean:84`, `Minimal/Completeness.lean:88`).
   The same holds for `DecisionProcedure.lean` in both directories — each is a single ~120-line
   file dominated by docstrings, delegating to the shared `tableau_sound`/`tableau_complete`
   machinery. **There is no copy-paste duplication to refactor.** The description's phrase
   "rather than duplicating" should be read as "keep it this way," not as a call for new
   infrastructure — a plan that budgets time for building a parametric abstraction would be
   budgeting for work that is already done.

2. **The stale docstring block is not just imprecise, it appears to assert a false blocker.**
   `Scheme.lean:3001-3022` ("GAP 2 investigation... determinacy remains BLOCKED, confirmed by
   source-level investigation, not merely re-asserted") directly contradicts the resolution
   already recorded at `Scheme.lean:485-500` (the `sat_timp` discharge note, which says Gap 2 is
   RESOLVED by the `.pos, .imp` branching arm) and at the inline comment on `truthLemma`'s T-imp
   case itself (`Scheme.lean:580-590`, "The determinacy obstruction... is RESOLVED"). Worse: the
   3001-3022 block's own argument does not hold up. It claims the T-imp case needs "the CONVERSE
   of `ih_φ'`" (`IForces val w' φ' → T(φ')@w' ∈ b`) to use the disjunction, and that no such
   converse exists. That is not correct — see Alternative Proof Strategies below, where a
   standard classical disjunction-elimination closes the goal using only the F-direction and
   T-direction of the *existing* IH, exactly mirroring the pattern already used for the
   classical-tableau `T(a→c)` branching case and the modal `box` case in this same repository.
   This is exactly the docstring the task description flags for MANDATORY repair; my
   independent read agrees it is wrong, not merely outdated.

3. **What Gap 1's resolution (`applyPersistenceFixpoint_genuine_of_count_le_fuel`,
   `Scheme.lean:2912`) actually buys you, and what it does not yet buy you.** The landed lemma
   states a fixpoint-equality: `applyAllTImpRules (applyPersistenceFixpoint b edges fuel) edges =
   applyPersistenceFixpoint b edges fuel` once `fuel ≥` the not-yet-claimed `intUniverse φ0` cell
   count. This is a genuine, useful, sorry-free fact, but it is **not itself** the membership
   statement `sat_timp` needs (`∀ w' accessible from w, T(φ'→ψ')@w' ∈ b`). A short bridging
   lemma is still needed: at a genuine fixpoint, if `T(φ→ψ)@l ∈ b` and `w'` is accessible from
   `l`, then `T(φ→ψ)@w' ∈ b` — proved by contradiction against the fixpoint equality using the
   same `if b.any (...) then none else some copy` guard pattern already used in
   `applyAllTImpRules_copy_notMem` (`Scheme.lean:2777-2801`) and `intTImpRule_output_notMem`
   (`Scheme.lean:2806-2824`): if the copy were absent, one more `applyAllTImpRules` round would
   add it, contradicting fixpoint-equality. This bridging lemma looks mechanical (same proof
   style as its neighbors, ~20-40 lines), not a new calculus rule. This contradicts the stale
   block's claim that a "calculus-level change to `Rules.lean`/`Expansion.lean`" is required.

## Recommended Approach

Do **not** budget time for a parametric refactor (finding 1) or for a new tableau rule (finding
2/3). The remaining path to close `sat_timp`/`truthLemma`'s T-imp case is:

1. Prove the bridging lemma described in Finding 3 (genuine-fixpoint → membership-at-every-
   accessible-world), stated against `applyPersistenceFixpoint_genuine_of_count_le_fuel`.
2. Add `sat_timp : ∀ φ' ψ' w, T(φ'→ψ')@w ∈ b → ∀ w' accessible from w, F(φ')@w' ∈ b ∨ T(ψ')@w'
   ∈ b` as a new `IBranchSaturation` field (mirrors `sat_fimp`'s shape but existential →
   universal-over-accessible).
3. Discharge it at `IExpandedConsistent_sat` (`Scheme.lean:904`) the same mechanical way as
   `sat_tand`/`sat_fand`/`sat_tor`/`sat_for_`/`sat_fimp` are discharged there — via
   `compound_sat` on the `.pos, .imp` branch of `sfSatisfied` (`Scheme.lean:765-771`), now
   consuming the Finding-3 bridging lemma to get `T(φ'→ψ')@w' ∈ b` at the target world before
   invoking `compound_sat`.
4. Close `truthLemma`'s T-imp T-direction (`Scheme.lean:591-592`) via case split on `sat_timp`'s
   disjunction: in the `F(φ')@w'` branch, derive a contradiction between `ih_φ'.2` and the
   hypothesis `IForces val w' φ'`; in the `T(ψ')@w'` branch, close directly with `ih_ψ'.1`. No
   converse of any IH direction is needed.
5. Rewrite `Scheme.lean:3001-3022` to describe steps 1-4 above instead of asserting a blocked
   determinacy gap — or delete it if step 1-4 lands in the same dispatch (per the task's
   MANDATORY DOCSTRING REPAIR instruction).

This differs from a plan that treats "sat_timp discharge" as requiring either (a) a new
determinacy/completion tableau rule, or (b) a parametric refactor of Int/Min — both would be
solving problems that do not exist given the current, verified state of the code.

## Evidence/Examples

- `IntMinScheme` structure and both instances: `Scheme.lean:118-221`.
- Parametric `truthLemma`, `tableau_sound`: `Scheme.lean:247-255` (soundness),
  `Scheme.lean:555-630` (truth lemma, all six connective cases).
- Thin-corollary pattern confirmed in both consumer files:
  `Intuitionistic/Completeness.lean:74-133`, `Minimal/Completeness.lean:78-125` — both files
  are ~130 lines, each with exactly one `sorry` (the `IValid`/`MValid` bridge in the final
  theorem), both delegating truth-lemma/countermodel work to `Scheme.lean`.
- Branching rule for `T(φ→ψ)` (Gap 2 fix): `Rules.lean:274-275`,
  `.pos, .imp φ ψ => .branchingResult [[⟨.neg, φ, l⟩], [⟨.pos, ψ, l⟩]] nextWorld`.
- Stale/contradictory docstring pair: `Scheme.lean:485-500` (says RESOLVED) vs.
  `Scheme.lean:3001-3022` (says BLOCKED) vs. `Scheme.lean:580-590` (inline note on
  `truthLemma` itself, says RESOLVED, matches 485-500).
- Fuel-sufficiency lemma actually landed: `Scheme.lean:2912-2999`
  (`applyPersistenceFixpoint_genuine_of_count_le_fuel`), with its supporting lemmas
  `applyAllTImpRules_copy_notMem` (2777), `intTImpRule_output_notMem` (2806),
  `applyAllTImpRules_count_drop` (2831).
- `IExpandedConsistent_sat`'s construction-site pattern (what a new `sat_timp` field would
  reuse): `Scheme.lean:904-969`, `compound_sat` helper at 910.
- `sfSatisfied`'s `.pos, .imp` clause (the loop-invariant analogue of `sat_timp`, already
  correctly stated): `Scheme.lean:765-771`.

### Prior-art parallels (why the disjunction-elimination route is standard, not novel)

- **Classical tableau**, `T(a → c)` branching case,
  `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean:202-222`: branches into
  `[F(a)]` / `[T(c)]`, case-splits, closes each branch with the corresponding IH direction. No
  converse of any IH is used.
- **Modal tableau**, `box` case,
  `Cslib/Logics/Modal/Tableau/Completeness.lean:566-573`: `T(□ψ)@w ∈ b → ∀ w' accessible,
  Satisfies w' ψ` closes via `hintikka_box_pos` supplying `T(ψ)@w' ∈ b` directly (unconditional
  propagation, no disjunction needed — see Disanalogy note below) then `IH.1`.
- Neither prior-art case needed an IH converse; the intuitionistic case needs one extra step
  (disjunction elimination via contradiction in the false branch) precisely because the
  intuitionistic `T(φ→ψ)` rule is a genuine two-way branching rule, whereas modal `box` is a
  one-way unconditional propagation rule. That extra step is still elementary — it does not
  require a converse IH.

## Reusable Prior Art

| Source location | What transfers | What does not transfer |
|---|---|---|
| `Classical/Completeness.lean` `classicalHintikkaSet` (raw `∀ sf ∈ b, match applyOne with ...` predicate, no dedicated structure) | The idea of stating saturation as "every rule's output is on the branch," case-split on the rule shape at proof time | The Int/Min case already improved on this by using a named `IBranchSaturation` structure per connective — better than reinventing the raw-predicate style; do not regress to the classical file's un-named style |
| `Classical/Completeness.lean` `T(a→c)` branching-case proof shape (lines 202-222) | The exact disjunction-elimination pattern needed for `truthLemma`'s T-imp case (branch, contradiction in the false arm via the IH's F-direction, direct closure in the true arm via IH's T-direction) | The classical case closes by *substitution* into a Boolean function (`BoolEvaluate`), not by contradiction against a semantic hypothesis — the int case needs the contradiction step because `IForces` is a `Prop`, not decidable — same-shape proof, different closing tactic |
| `Modal/Tableau/Completeness.lean` `modalTruthLemma`'s `box`/`diamond` cases (439-586) | The overall induction-on-formula-complexity shape via `IH`, and the "helper lemma extracts the accessible-world witness from the Hintikka structure, then invoke IH" idiom (`hintikka_box_pos`, `hintikka_diamond_pos`) | Box propagation is unconditional (no disjunction, no branching rule); nothing to port for the disjunction-elimination step itself, but the file confirms "quantify over accessible worlds via a dedicated per-connective Hintikka-field lemma" is the established local idiom |
| `Modal/Tableau/CompletenessLoop.lean` `ModalLoopInvGen`/`RuleApply`, `AuxBounds`/`AuxStepPreserved`, `ModalLoopAuxK`/`ModalLoopAuxS5w` (74-1430) | Confirms "one parametric development (`RuleApply`-generic loop invariant), multiple instantiations (K/S5/...)" is an *established, repo-wide* convention, not something task 317 needs to invent for Int/Min — `IntMinScheme` is the propositional-tableau analogue of this same idiom | The modal generic driver is far more elaborate (handles loop-checking, multiple frame conditions); porting its machinery wholesale would be over-engineering for a 2-value (`closurePred`, `modelBot`) parameterization |
| `applyAllTImpRules_copy_notMem` / `intTImpRule_output_notMem` (`Scheme.lean:2777-2824`) | The exact proof idiom needed for the Finding-3 bridging lemma: unfold the `if b.any (...) then none else some copy` guard and derive non-membership/membership by contradiction | N/A — this is already Int-local code, directly reusable in-place, no adaptation needed |

## External Prior Art (brief)

A brief check: Fitting-style intuitionistic tableau completeness (the paper this development
cites, *Proof Methods for Modal and Intuitionistic Logics*, Ch. 4) proves the analogous
Hintikka-set lemma by the same case-split-on-the-branching-rule technique used above; mechanized
treatments in Coq/Isabelle for intuitionistic Kripke completeness (e.g. via canonical-model or
tableau routes) uniformly close the `→`-case by cases on whether the antecedent is forced,
deriving a contradiction in the "antecedent forced but branch says F(antecedent)" arm — i.e. the
same disjunction-elimination shape recommended above. This is standard, not a novel technique;
it does not change the recommendation, only confirms it. No CSLib-specific mechanized reference
was found beyond what already exists in this repository (Mathlib has no intuitionistic-Kripke or
tableau formalization to draw from — see below).

## Mathlib Leverage

- `HeytingAlgebra`, `HeytingHom` (`Mathlib.Order.Heyting.Basic`/`Hom`): algebraic Heyting
  structures exist, but nothing connects them to a Kripke/possible-worlds semantics or to
  tableau proof search — **not usable** for this task's forcing-relation or persistence
  arguments.
- Generic `Monotone`/`MonotoneOn` lemmas (`Mathlib.Order.Monotone.*`) exist but are too generic
  to shortcut the branch-membership-specific persistence argument; `intAccessPreorder` already
  builds its own `Preorder Nat` from `Relation.ReflTransGen`, which is the right Mathlib-backed
  piece already in use (`Relation.ReflTransGen` itself is Mathlib, not reinvented).
- No Mathlib formalization of intuitionistic Kripke semantics, tableau calculi, or
  fuel/fixpoint-sufficiency measures was found (`lean_local_search "Heyting"`,
  `lean_leansearch "intuitionistic Kripke semantics persistence monotonicity forcing"`,
  `lean_loogle "Nat.rec fuel well-founded fixpoint idempotent"` all returned nothing relevant
  beyond the generic order-theory lemmas above). **State plainly: do not budget research time
  looking for a Mathlib shortcut for the persistence/fixpoint or Kripke-forcing machinery — it
  does not exist.** The right reusable pieces are already in-repo (`Relation.ReflTransGen`, the
  `intAccessPreorder`/`IFimpAccess` machinery from phase 1).

## Confidence Level

**High** on Findings 1 and the "no Mathlib leverage" claim (directly verified against file
contents and exhaustive rate-limited search). **Medium-high** on Finding 2/3's specific claim
that the stale block is substantively wrong (not just outdated) and that the bridging lemma is
mechanical — this is a proof-strategy argument sketched on paper, not verified by actually
running the tactic block in Lean (out of scope for this read-only research dispatch, and another
session is actively building in this repo). Teammate A/the plan author should have the
implementer attempt steps 1-4 above directly rather than accept the stale block's "new calculus
rule" recommendation at face value.
