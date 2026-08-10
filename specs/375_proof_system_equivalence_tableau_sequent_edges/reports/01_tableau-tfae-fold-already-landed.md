# Research Report: Tableau Folds in the Propositional Proof-System TFAE

**Task**: 375 — proof_system_equivalence_tableau_sequent_edges
**Session**: sess_1786378622_28837b
**Date**: 2026-08-10
**Agent**: cslib-research-agent

## Headline Finding

**The work this task describes is already complete in the repository.** All three tableau
folds (CPL, IPL, MPL) exist in
`Cslib/Logics/Propositional/ProofSystemEquivalence.lean`, build green, and are sorry-free
and axiom-clean. The task was superseded by task 606
(`discharge_propositional_tableau_completeness_and_verify_tfae`, status `completed`), whose
commit `8bfebc43 task 606 phase 1: land the TFAE fold in ProofSystemEquivalence.lean` landed
exactly the deliverable described here.

Recommended disposition: mark task 375 **[COMPLETED]** (superseded, no code change required),
or **[ABANDONED]** as a duplicate. No implementation phase is warranted.

## Q1: What the TFAEs currently state

File: `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` (269 lines).
Namespace: `Cslib.Logic.PL`, with `open InferenceSystem Cslib.Logic.Tableau`
(`ProofSystemEquivalence.lean:61-63`).
Section variables: `{Atom : Type*} [DecidableEq Atom]` (`:65`).

There are **nine** theorems, not two. The task description's premise ("has
cplProofSystemsTfae and iplProofSystemsTfae") is accurate but stale — it omits the MPL row
and all three tableau folds.

### Three-way, context-based (`:76`, `:108`, `:141`)

| Theorem | Line | Node 1 (Hilbert) | Node 2 (ND) | Node 3 (Sequent) |
|---|---|---|---|---|
| `cplProofSystemsTfae` | 76 | `Deriv PropositionalAxiom Γ.toList φ` | `DerivableIn (AxiomTheory (@PropositionalAxiom Atom)) (Γ ⊢ φ)` | `Nonempty (LKProof (Γ ⊢ₛ ({φ} : Finset _)))` |
| `iplProofSystemsTfae` | 108 | `Deriv IntPropAxiom Γ.toList φ` | `DerivableIn (AxiomTheory (@IntPropAxiom Atom)) (Γ ⊢ φ)` | `Nonempty (LJProof (Γ ⊢ φ))` |
| `mplProofSystemsTfae` | 141 | `Deriv MinPropAxiom Γ.toList φ` | `DerivableIn (AxiomTheory (@MinPropAxiom Atom)) (Γ ⊢ φ)` | `Nonempty (SeqProofMinimal (Γ ⊢ φ))` |

Each is proved by `tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_{cl,int,min}`,
`tfae_have 2 ↔ 3 := nd_iff_{lk,lj,lm}`, `tfae_finish` (`:80-82`, `:112-114`, `:145-147`).

### Three-way, closed (`:90`, `:122`, `:155`)

`cplProofSystemsTfaeClosed`, `iplProofSystemsTfaeClosed`, `mplProofSystemsTfaeClosed` — each
specialises the context-based version at `Γ = ∅` via `simp only [Finset.toList_empty]`
(`:95-97`, `:127-129`, `:160-162`). Node 1 becomes `Derivable {Prop,Int,Min}PropAxiom φ`.

### Legacy re-export (`:170`)

`mplHilbertIffNd` — two-way `Deriv MinPropAxiom ↔ DerivableIn`, retained for backward
compatibility, body is `hilbert_iff_nd_ctx_min` (`:173`).

## Q2 & Q4: The tableau folds and their statement shape

The folds live in `section WithTableau` (`:185-265`) with `variable [Hashable Atom]` (`:187`).
The section docstring (`:175-183`) records the design rationale: the tableau decision
procedures take a single closed formula and no context, so each fold extends the `...Closed`
three-way TFAE rather than the context-based one; `[Hashable Atom]` is scoped to this section
so the six pure proof-theoretic equivalences are not forced to carry it.

**Answer to Q4** — the node shape actually used is `{classical,intuitionistic,minimal}Tableau φ = .closed`,
i.e. *the tableau on `φ` itself closes*, not "the tableau for `¬φ` closes". Negation is
internal to the decision procedure. Side conditions: `[DecidableEq Atom]` throughout;
`[Hashable Atom]` additionally for IPL and MPL only. CPL does **not** need `[Hashable Atom]`
and explicitly opts out via `omit [Hashable Atom] in` (`:189`) — documented at `:200-202`.

| Theorem | Line | 4th node | Bridge proof |
|---|---|---|---|
| `cplProofSystemsWithTableauTfae` | 203 | `classicalTableau φ = .closed` (`:208`) | `rw [← prop_completeness_iff_tautology, ← classicalTableau_decides]` (`:212-213`) |
| `iplProofSystemsWithTableauTfae` | 229 | `intuitionisticTableau φ = .closed` (`:233`) | `int_soundness_completeness.symm.trans ((ivalid_universe_invariant φ).trans (intuitionisticTableau_decides φ).symm)` (`:237-239`) |
| `mplProofSystemsWithTableauTfae` | 252 | `minimalTableau φ = .closed` (`:256`) | `min_soundness_completeness.symm.trans ((mvalid_universe_invariant φ).trans (minimalTableau_decides φ).symm)` (`:260-262`) |

All three reuse nodes 1-3 by `have h := ...TfaeClosed` then `h.out 0 1` / `h.out 1 2`
(`:209-211`, `:234-236`, `:257-259`).

**Universe gotcha, documented in-repo**: the IPL/MPL bridges cannot be discharged by `rw` —
it leaves an unsolvable universe metavariable — so they are built in term mode via `Iff.trans`
(`:226-228`, `:251`). The `ivalid_universe_invariant` / `mvalid_universe_invariant` step is
what reconciles the universe-pinned completeness theorem with an unpinned public statement.

The imports wiring the tableau side in are already present:
`Tableau.Intuitionistic.DecisionProcedure`, `Tableau.Minimal.DecisionProcedure`,
`Tableau.Classical.DecisionProcedure`, `Metalogic.StrongCompleteness`
(`ProofSystemEquivalence.lean:13-16`).

## Q3: Is Minimal in scope?

**Yes, and it is already done.** The task description's assumption that there is "no minimal
TFAE yet" is stale. `mplProofSystemsTfae` (`:141`), `mplProofSystemsTfaeClosed` (`:155`), and
`mplProofSystemsWithTableauTfae` (`:252`) all exist. Git history shows the MPL three-way row
landed in `5d20118d task 547 phase 4: barrel + TFAE + docstring fixes` and the tableau folds
in `8bfebc43 task 606 phase 1`. The module docstring (`:23-27`) states the intent explicitly:
"All three logic strengths have a three-way equivalence at both the context-based and
closed-formula levels, and the closed-formula equivalences additionally fold in the tableau
decision procedure as a fourth node, making the proof-system × logic matrix structurally
symmetric."

## Q5: Dependency state — is task 317 still blocking?

**No. The claimed blocker is resolved.** Task 317 (`propositional_tableau_completeness`) is
archived at `specs/archive/317_propositional_tableau_completeness`. Its CHANGE_LOG entry
(`specs/CHANGE_LOG.md:55`) records its terminal state as "4 bare sorries in subtree (DP-2 ->
task 585, DP-3/DP-4/DP-5 -> task 430), all strategic and tracked". Those four were
subsequently discharged by tasks 430, 585, and 606.

### Machine-verified evidence (not docstring prose)

`lake build Cslib.Logics.Propositional.ProofSystemEquivalence` — **Build completed
successfully (986 jobs)**. Only two warnings, both pre-existing and unrelated to this task
(`unusedDecidableInType` on `ivalid_universe_invariant` at
`Tableau/Intuitionistic/DecisionProcedure.lean:159` and `mvalid_universe_invariant` at
`Tableau/Minimal/DecisionProcedure.lean:173`).

`#print axioms` run against a scratch file importing the module — every one of the following
reports exactly `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**:

- `cplProofSystemsTfae`, `iplProofSystemsTfae`, `mplProofSystemsTfae`
- `cplProofSystemsTfaeClosed`, `iplProofSystemsTfaeClosed`, `mplProofSystemsTfaeClosed`
- `cplProofSystemsWithTableauTfae`, `iplProofSystemsWithTableauTfae`, `mplProofSystemsWithTableauTfae`
- `classicalTableau_complete`, `intuitionisticTableau_complete`, `minimalTableau_complete`
- `classicalTableau_decides`, `intuitionisticTableau_decides`, `minimalTableau_decides`

Completeness theorem locations (all in namespace `Cslib.Logic.PL`, not
`Cslib.Logic.Tableau` — an early probe assuming the latter failed with
`Unknown constant`):

- `Tableau/Classical/Completeness.lean:1310` — `classicalTableau_complete`
  (namespace opened at `:46`)
- `Tableau/Intuitionistic/Completeness.lean:184` — `intuitionisticTableau_complete (φ) (h : IValid.{_, 0} φ) : intuitionisticTableau φ = .closed`
- `Tableau/Minimal/Completeness.lean:170` — `minimalTableau_complete` (namespace at `:88`)

`decides` bridges: `Tableau/Classical/DecisionProcedure.lean:68`,
`Tableau/Intuitionistic/DecisionProcedure.lean:97`,
`Tableau/Minimal/DecisionProcedure.lean:113`.

### Note on the 79 grep hits for "sorry"

A raw `grep -rn sorry Cslib/Logics/Propositional/Tableau/` returns 79 lines. Every one is
**docstring prose**, overwhelmingly of the form "this module is now sorry-free" or historical
narration of gaps that were since closed (e.g.
`Tableau/Intuitionistic/Scheme.lean:743`: "The two `sorry`s this note used to cite ... "). No
code-level `sorry` tactic remains anywhere in the propositional tableau subtree. The
`#print axioms` results above are the authoritative check; the grep count is misleading and
should not be read as a blocker signal.

## Reuse Check Protocol (CSLib reuse-first)

No new definitions or abstractions are recommended, so the reuse question is moot — but for
completeness: every abstraction this task would have needed already exists and is already
wired. `List.TFAE` comes from `Mathlib.Data.List.TFAE` (`:12`) with the `tfae_have` /
`tfae_finish` tactics from `Mathlib.Tactic.TFAE` (`:17`). The bridge lemmas
(`hilbert_iff_nd_ctx_*`, `nd_iff_*`, `*_soundness_completeness`, `*valid_universe_invariant`,
`*Tableau_decides`) are all enumerated in the module's own Dependencies docstring (`:46-56`)
and were each verified present above.

## Zero-Debt Compliance

Nothing to implement, therefore no sorry-deferral, no new axioms, no plan decomposition
needed. The existing code already satisfies the zero-debt gate: build green, axiom profile
clean, no `sorryAx` in any of the fifteen checked declarations.

## Recommendation

1. **Do not dispatch an implementation phase.** There is no remaining code delta.
2. Transition task 375 to `[COMPLETED]` with a completion summary noting supersession by
   task 606, or `[ABANDONED]` as a duplicate — the orchestrator/user should pick, since the
   distinction is bookkeeping preference, not technical.
3. If any residual work is wanted, the only candidates found are the two pre-existing
   `unusedDecidableInType` lint warnings on `ivalid_universe_invariant`
   (`Tableau/Intuitionistic/DecisionProcedure.lean:159`) and `mvalid_universe_invariant`
   (`Tableau/Minimal/DecisionProcedure.lean:173`). These are out of scope for this task and
   would warrant their own small lint task if desired.
