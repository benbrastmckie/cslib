# Research Report: Task 317 — Tableau Completeness Approach (Int/Min)

- **Task**: 317 — Discharge the open completeness obligations for the intuitionistic and
  minimal propositional tableaux (post task-369 parametric refactor)
- **Date**: 2026-06-28
- **Type**: cslib research (study/recommendation; no implementation)
- **Session**: orchestrate batch (team research)
- **Build constraint**: produced build-free (no `lake`, no compiling lean-lsp calls);
  grounded in source reads + web/literature.

## Scope: the 6 open sorries after task 369

The 369 refactor consolidated the int/min completeness story into one parametric module,
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (`IntMinScheme` bundling
the two divergence points `closurePred` and `modelBot`). The architecture is sound:
`tableau_complete` (Scheme.lean:322) is already **sorry-free given** `openBranch_countermodel`,
and `openBranch_countermodel` (Scheme.lean:269) is sorry-free **given** `truthLemma` plus three
structural facts. The remaining 6 sorries are:

| # | Location | Obligation |
|---|----------|------------|
| 1 | Scheme.lean:242 `truthLemma S` | Parametric Kripke truth lemma (the mathematics) |
| 2 | Scheme.lean:280 `…openBranch_closed` | open branch ⟹ `S.closurePred b = false` |
| 3 | Scheme.lean:288 `…openBranch_sat` | open branch ⟹ `intStepBranch b [] 0 = none` |
| 4 | Scheme.lean:296 `…openBranch_initial_mem` | F(φ)@0 ∈ b (branch monotonicity) |
| 5 | `Intuitionistic/Completeness.lean:~112` | per-logic validity bridge (`intScheme`) |
| 6 | `Minimal/Completeness.lean:~110` | per-logic validity bridge (`minScheme`) |

Sorries 2–4 are the three structural obligations of `openBranch_countermodel`; they are the
induction-on-`intExpandBranches` work that has resisted prior attempts. Sorries 5–6 are
thin instantiations (`IValid φ` / `MValid φ` ⟹ `hvalid b`) and are not the bottleneck.

---

## A. The mathematics: standard routes to tableau completeness

There are two textbook strategies.

**(i) Direct model-existence / Hintikka route (Smullyan, Fitting).**
Run the tableau to exhaustion; a non-closed branch becomes *saturated* (downward-closed under
the rules). A saturated open branch is a **Hintikka set**. From it one reads off a model and
proves a **truth lemma** by induction on formula structure: every T-signed formula on the branch
is true/forced and every F-signed formula is false/not-forced. Since the root carries F(φ), φ is
refuted, so φ is not valid — the contrapositive of completeness. The key technical step is the
*Downward Saturation Lemma* feeding the truth lemma (OpenLogic, *Intuitionistic Tableaux*;
Fitting 1983 Ch. 4; Smullyan block tableaux).

**(ii) Reduction / consistency route.**
Show: open tableau ⟹ the branch formula set is *consistent* in an axiomatic/sequent calculus ⟹
(by an **already-established semantic completeness** for that calculus) the set is satisfiable ⟹
φ not valid. This route only saves work if (a) a semantic (Kripke) completeness theorem for the
target calculus already exists and (b) a cheap "open tableau ⟹ consistency" bridge exists.

**Intuitionistic specifics (vs classical).** Classical completeness extracts a single Boolean
valuation from the atoms on the branch — the truth lemma is a flat structural induction. The
intuitionistic case must build a **Kripke frame**:
- worlds = branch labels / prefixes; accessibility = label order (initial-segment order on
  prefixes), i.e. `worldOf`/`isAccessible` in this repo;
- the valuation must be **persistent/monotone** (atoms true at w stay true at w′ ≥ w);
- `T(φ→ψ)` is a **persistent** signed formula (transferred to every accessible world), and
  `F(φ→ψ)` is **world-creating** (spawns a fresh w′ ≥ w with T(φ), F(ψ)).
The hard truth-lemma case is implication: `IForces … w (φ→ψ)` quantifies over **all** w′ ≥ w, so
the proof needs saturation (T(imp) persistence has populated every accessible world) for the
T-direction and the freshly-created witness world for the F-direction. The cleanest standard
completeness for the *axiomatic* IPL system is instead the **Henkin / Troelstra–van Dalen
canonical model** over prime theories (a recent Lean formalization of exactly this:
[arXiv:2310.01916](https://arxiv.org/abs/2310.01916)) — important because it is *not*
tableau-based and is a substantial standalone development.

Sources: [OpenLogic, Intuitionistic Tableaux](https://builds.openlogicproject.org/content/intuitionistic-logic/tableaux/tableaux.pdf),
[Fitting, Handbook of Tableau Methods](https://id144254.securedata.net/melvinfitting/bookspapers/pdf/papers/tableauchapter.pdf),
[Verified Henkin-style IPL completeness in Lean (arXiv:2310.01916)](https://arxiv.org/abs/2310.01916),
[SEP: Intuitionistic Logic](https://plato.stanford.edu/entries/logic-intuitionistic/).

---

## B. Repo asset — the classical direct-route template (working, sorry-free)

The classical case proves completeness by the **direct** route and is the in-repo template.

- **One bundled Hintikka lemma.** `classicalExpandBranches_hintikka`
  (`Classical/Completeness.lean:924`) yields a single `classicalHintikkaSet` record bundling
  *openness + saturation + rule-closure* for the returned open branch — rather than three
  separate facts. The truth lemma and countermodel then consume that one bundle.
- **Driven by a termination measure.** The induction is powered by `classicalExpMeasure`
  (a Σ 3^complexity sum over pending formulas) together with `classicalExpMeasure_step_lt`,
  proving each expansion step strictly decreases the measure. This is what makes the
  double recursion (fuel + pending) tractable: the measure bound is carried as a hypothesis.
- **Monotonicity / initial membership.** `classicalExpandBranches_openBranch_initial_mem`
  proves the root formula persists into the returned branch (expansion only adds formulas,
  `extendMany` prepends).
- **Truth lemma + countermodel + main theorem** then follow the standard chain:
  Hintikka set ⟹ truth lemma (induction on φ) ⟹ `classicalOpenBranch_countermodel` ⟹
  `classicalTableau_complete` (contrapositive against `Tautology`).

**How closely can int/min mirror it, and what genuinely differs.**
The *shape* transfers directly, but the INT module currently **mis-mirrors** the template:

1. INT has **no measure apparatus** at all — there is no `intExpMeasure`/`…_step_lt`. The
   classical proof's central engine is missing on the INT side.
2. INT splits the bundle into **three separate sorries** (Scheme.lean:280/288/296) feeding a
   `truthLemma` that takes `hopen`/`hsat` as *separate* hypotheses — instead of one
   `intHintikkaSet` bundle as classical does.
3. The INT recursion is **structurally harder**: a **persistence fixpoint**
   (`applyPersistenceFixpoint`, producing a mutated branch `bPers`) runs inside the loop, there
   are **4 parallel state lists** (branches, expanded-sets, next-world counters, persistence
   edges) vs classical's 2, and world creation (`F(imp)`) inflates the state. A correct INT
   measure must dominate **both** world-creation and persistence blow-up.
4. The **saturation sorry is mis-stated.** `truthLemma` asks for
   `hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none` — i.e. saturation w.r.t. the **empty**
   expanded-set and world 0. But the loop saturates w.r.t. an **accumulated** expanded-set `e`
   and current next-world `nw`; classical never resets these. Connecting the loop's
   `intStepBranch b e nw = none` to the reset `intStepBranch b [] 0 = none` is not obviously
   true and is precisely where sorry #3 is stuck.

Transferability of the three structural obligations:
- **#4 initial membership (`hFmem`)** — *highly transferable* from
  `classicalExpandBranches_openBranch_initial_mem` (plus a persistence-fixpoint monotonicity
  lemma `b ⊆ applyPersistenceFixpoint b edges fuel`).
- **#2 openness (`hopen`)** — *moderate*; the loop checks `closurePred b = false` before
  returning `.openBranch b`, but the proof must thread it through fuel=0 and the inner loop.
- **#3 saturation (`hsat`)** — *hardest*, and currently **mis-formulated** (see point 4).

---

## C. Repo asset — the Hilbert/IPL completeness bridge (rejected as a shortcut)

The bridge hypothesis was: "no closed tableau ⟹ branch set IPL-consistent ⟹ (existing IPL
completeness) satisfiable ⟹ φ not valid."

**What exists (sorry-free).** IPL *Kripke* completeness is already in the repo, on the
semantic/axiomatic side: `Metalogic/IntStrongCompleteness.lean` provides
`int_completeness : IValid φ → Derivable IntPropAxiom φ`, `int_soundness_completeness`, and an
`int_truth_lemma`, built via a canonical-model / Lindenbaum construction. Proof-system
inter-translation also exists: `ProofSystemEquivalence.lean` proves Hilbert ↔ ND ↔ LJ
(intuitionistic) and Hilbert ↔ ND ↔ LK (classical).

**Why it is NOT a shortcut.** The existing completeness lives entirely on the unsigned,
inductive Hilbert/semantic side. The stuck obligation is the gap between the **executable,
signed, world-labelled tableau** (`intExpandBranches`: a `List ISF` fuel loop with
persistence) and that semantic/axiomatic world. To use the bridge you would have to build a
**brand-new** theorem "no closed `intExpandBranches` ⟹ ¬`Derivable`/consistent", which:
- still requires the **same `intExpandBranches` structural induction** we are trying to avoid
  (you must reason about what an open tableau gives you), **plus**
- a **signed→unsigned translation layer** bridging world-labelled `ISF` branches and fuel-loop
  state to the unsigned inductive Hilbert calculus (an impedance mismatch with no existing
  connector).

Net: the bridge is **at least as much work, not less** — it adds a translation layer on top of
the very induction it was meant to sidestep. Reject it as the primary route. (The existing
`int_truth_lemma`/canonical-model code remains useful as a *reference* for the truth-lemma shape,
but not as a reduction target.)

---

## D. Reference — BimodalLogic canonical-model patterns (reference-only)

From `BimodalLogic/.../BXCanonical/TruthLemma.lean` and `.../Quasimodel/HintikkaPoint.lean`
(different logic/project; transferable *ideas* only):

- **Witness-via-contrapositive** for the modal/implication case: to show a formula is *not*
  forced, exhibit an accessible world witnessing failure — mirrors the F(φ→ψ) world-creating
  case of the INT truth lemma.
- **Persistence as a separate lemma**, applied at the accessibility step rather than inlined —
  matches `iforces_persistence` usage and keeps the implication case clean.
- **Negation-completeness via case split** on membership of a formula vs its negation in a
  maximal/saturated set — analogous to reading the F-direction off an open branch.
- **Finite projection from a maximal consistent set / enumeration of worlds** — analogous to
  worlds = branch labels with `worldOf`/`isAccessible`.

These confirm the standard truth-lemma skeleton but do not reduce the INT-specific structural
induction.

---

## E. Recommendation

**Route: the DIRECT branch-saturation route, RESTRUCTURED to mirror the classical template.**

Rationale: (1) the math is the standard, correct Hintikka/model-existence argument for IPL;
(2) a working, sorry-free in-repo template exists for the analogous classical induction,
including the measure and the initial-membership lemma; (3) the parametric `IntMinScheme`
architecture is already in place, so success collapses the int *and* minimal cases at once via
`intScheme`/`minScheme`; (4) the Hilbert bridge is strictly more work (Section C). The reason
prior attempts stalled is not that the route is wrong — it is that INT was attempted **without**
the classical template's two enabling devices (a termination measure and a bundled Hintikka
predicate) and with a **mis-stated saturation hypothesis**.

### Phased plan (feeds a revised plan v3, replacing the current 3-sorry decomposition)

**Phase 1 — INT termination measure.** Define `intExpMeasure` analogous to `classicalExpMeasure`
(Σ 3^complexity over pending signed formulas) but **accounting for world creation and the
persistence fixpoint**, and prove `intExpMeasure_step_lt` (each `intStepBranch`/persistence step
strictly decreases it). Key risk lives here: the measure must dominate both `F(imp)` world
spawning and `applyPersistenceFixpoint` growth.

**Phase 2 — persistence-fixpoint monotonicity.** Prove `b ⊆ applyPersistenceFixpoint b edges fuel`
(formulas only added). Unblocks initial-membership and supports saturation.

**Phase 3 — single bundled Hintikka lemma.** Define an `intHintikkaSet` predicate bundling
openness + saturation (w.r.t. the **accumulated** expanded-set `e` and `nw`, *not* the reset
`[] / 0` form) + rule-closure. Prove one `intExpandBranches_hintikka` by the **same double
induction (fuel + pending)** as classical, carrying the `intExpMeasure` bound as a hypothesis.
This single lemma replaces sorries #2, #3, #4.

**Phase 4 — reformulate `truthLemma S`.** Change its hypothesis from
`hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none` to consume `intHintikkaSet` (the accumulated-`e`
saturation/rule-closure conditions). Prove by induction on φ, using `S.modelBot`, persistence
(`iforces_persistence`), and the world-creation witness for the F(imp) case; `bot_truth` from
the scheme handles ⊥. The F-atom case requires no atomic-contradiction worry for `minScheme`
(its `closurePred = isMinimallyClosed` closes complementary pairs) and is discharged for
`intScheme` via the Hintikka rule-closure conditions.

**Phase 5 — rewire `openBranch_countermodel` and the validity bridges.** Replace the three
sorries with the `intExpandBranches_hintikka` projections; close sorries #5/#6
(`Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`) by instantiating
`tableau_complete` at `intScheme`/`minScheme` — these are the thin `IValid`/`MValid` ⟹ `hvalid b`
wrappers (build the upward-closure witnesses for `intExtractValuation b` and, for minimal,
`minBranchBotForces b`).

### Key new lemmas
- `intExpMeasure`, `intExpMeasure_step_lt` (Phase 1) — the central enabler.
- `applyPersistenceFixpoint_subset` / branch-monotonicity (Phase 2).
- `intHintikkaSet` predicate + `intExpandBranches_hintikka` (Phase 3) — replaces sorries #2–#4.
- reformulated `truthLemma S` over `intHintikkaSet` (Phase 4).

### Reuse from the repo
- Template & proof skeleton: `classicalExpandBranches_hintikka` (924),
  `classicalExpMeasure`/`classicalExpMeasure_step_lt`,
  `classicalExpandBranches_openBranch_initial_mem`, `classicalTableau_complete`
  (`Classical/Completeness.lean`).
- Already-built parametric scaffolding: `IntMinScheme`, `tableau_sound`, `tableau_complete`,
  `intScheme`, `minScheme`, `bot_truth` (Scheme.lean) — all sorry-free.
- Semantics & extraction: `IForces`/`IValid`/`MValid`, `iforces_persistence`
  (`Semantics/Kripke.lean`); `intExtractValuation`, `intBotForces`/`minBranchBotForces`,
  `intBranchSatisfied` (Int/Min `Completeness.lean`/`Soundness.lean`).
- Reference only (do **not** reduce to it): `int_truth_lemma`/canonical model in
  `Metalogic/IntStrongCompleteness.lean`; BimodalLogic truth-lemma patterns (Section D).

### Main risks
1. **The INT measure (Phase 1)** — proving `intExpMeasure_step_lt` through the persistence
   fixpoint and world creation is the genuine novelty with no exact classical analog. Highest
   risk; do it first as a spike.
2. **Saturation reformulation** — must abandon the reset `intStepBranch b [] 0 = none` form;
   the Hintikka bundle must be expressed against the accumulated `e`/`nw` the loop actually
   produces, or sorry #3 stays unprovable.
3. **Zero-debt** — no new axioms, no sorry deferral; if the measure spike fails, mark
   `[BLOCKED]` for user review rather than introducing placeholders.

This recommendation should drive a **revised 317 plan (v3)** replacing the current three-sorry
decomposition with the five-phase, measure-first, single-`intHintikkaSet` structure above.
