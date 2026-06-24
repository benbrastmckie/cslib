# Research Report: Intuitionistic Tableau Soundness — Inner Induction Crux

- **Task**: 316 - propositional_tableau_soundness
- **Started**: 2026-06-24T21:44:49Z
- **Completed**: 2026-06-24T22:10:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: Reports 01–04 (this task); concurrent implementation on the same file
- **Sources/Inputs**:
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (full read)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (full read)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` (full read)
  - `specs/316_propositional_tableau_soundness/reports/03_blocker-solutions.md`, `04_b4-hard-research.md`
  - `specs/316_propositional_tableau_soundness/.orchestrator-handoff.json` (implementation agent state)
  - lean-lsp `lean_goal` at line 950 (exact goal state of linearResult bp=bh case)
  - Web/literature search on Fitting-style intuitionistic/prefixed tableau soundness
- **Artifacts**: `specs/316_propositional_tableau_soundness/reports/05_intuitionistic-soundness-induction.md`
- **Standards**: report-format.md, lean4.md, cslib.md

## Executive Summary

- **The file has moved on from the 8-sorry state in the task brief.** As of this read the file
  compiles with **3 live `sorry`s**: line **945** (`hfresh`, linearResult), line **950**
  (linearResult `bp=bh` case), line **961** (`hfresh`, branchingResult). The other 5 obligations
  (819 outer gap, 922 sf-witness, both `bp∈bt` cases, and branchingResult `bp=bh`) are already
  discharged in the working tree.
- **The single conceptual blocker is freshness.** `hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH` is
  *not provable from the hypotheses currently in scope* because the induction (`hcore` over `fuel'`,
  `key` over `pending`) carries **no invariant relating `nwH` to the labels on the branch**. This
  matches the canonical literature requirement (Fitting): the new prefix/world must be *fresh to the
  branch*. The fix is to thread a **branch-freshness invariant** `∀ sf ∈ b, sf.label < nw` (per
  branch, paired through `nextWorlds`) — exactly the invariant proposed in reports 03/04 but **never
  actually added to the implemented induction**.
- **Most of the hard machinery is already built and sorry-free.** `intRule_preserves_sat`
  (existential `worldOf'`), `monotoneEdges_update` (monotonicity preserved across a world-creating
  step given freshness of `nw` in the edges), `applyPersistenceFixpoint_sat`, and
  `monotoneEdges_go` all exist. The linearResult `bp=bh` sorry is a *mechanical assembly* of these,
  blocked only by the missing freshness facts.
- **Verdict: the plan needs a targeted revision, not a rewrite.** Add one invariant
  (`BranchFresh`/label-bound) to the `key` suffices and to the outer `intExpandBranches_closed_unsat`
  statement, prove it is preserved by closure/persistence/linear/branching steps, and the three
  remaining sorries close. Estimated 2 focused phases (~150–250 lines).
- **Canonical technique confirmed (Fitting 1969/1983).** Soundness = per-rule
  satisfiability-preservation under a prefix→world assignment respecting accessibility; the F-→
  ("false implication") case is discharged by the Kripke truth condition for `→` yielding an
  accessible witness world, mapped onto the *fresh* prefix via `Function.update`. This is precisely
  what the existing `intRule_preserves_sat` implements.

## Context & Scope

Goal: unblock the inner induction of `intExpandBranches_closed_unsat` in
`Intuitionistic/Soundness.lean`. The lemma asserts (contrapositive form): if the fuelled expansion
returns `.closed`, then every input branch is unsatisfiable in every Kripke model whose
prefix→world map is monotone w.r.t. that branch's edge set. The proof is a triple nested induction:

1. **Outer** induction on `fuel'` (`hcore`).
2. **Middle** `suffices key` over the `go`-loop's `pending` list.
3. **Inner** structural induction on `pending` (`cons bh bt`).

Inside the `cons` case, after persistence (`bPers`) and a non-closing step
(`intStepBranch bPers eH nwH = some (result, newExp)`), the proof case-splits on `result`. The
world-creating / linear and branching cases recurse via `intExpandBranches ... fuel''`, so they must
use the **fuel IH `ih`**, not the pending IH `ih_inner` (confirmed against the live goal state).

Constraint: an implementation agent may be editing this file concurrently. This report is
read-only research; do not edit the file.

## Findings

### F1 — Canonical soundness technique (literature)

The standard soundness argument for signed/prefixed intuitionistic tableaux (Fitting's "prefixed
tableaux" for intuitionistic logic) is a **satisfiability-preservation** (a.k.a. *Hintikka /
model-existence dual*) argument:

- **Branch satisfiability.** A branch `b` is *satisfiable* iff there is a Kripke model
  `(W, ≤, ⊩)` (monotone/persistent forcing on a reflexive-transitive frame) and a map `ρ` from the
  prefixes/labels occurring on `b` to worlds in `W` such that (i) `ρ` respects the accessibility
  constraints recorded on the branch — if the branch records `σ` accessible from `τ` then
  `ρ(τ) ≤ ρ(σ)`; (ii) every `T(A)@σ` has `ρ(σ) ⊩ A`; (iii) every `F(A)@σ` has `ρ(σ) ⊮ A`. This is
  exactly `intBranchSatisfied val botForces worldOf b` together with `MonotoneEdges worldOf edges`
  in the Lean code.
- **Per-rule preservation lemma.** *If a branch is satisfiable and a tableau rule is applied to it,
  then at least one resulting branch is satisfiable.* For a **linear (α) rule** this is "the unique
  child is satisfiable"; for a **branching (β) rule** it is "some child is satisfiable." Iterating
  the contrapositive over the whole tableau gives: a closed tableau (every branch closed, hence
  unsatisfiable) cannot have a satisfiable root — i.e. soundness. This is the `closed_unsat` +
  `intRule_preserves_sat` decomposition already present.
- **The F-→ (world-creating) case** is the only non-trivial one. Given `F(A→B)@σ` satisfiable, the
  Kripke truth condition for intuitionistic implication,
  `ρ(σ) ⊮ (A→B) ⟺ ∃ w ≥ ρ(σ), w ⊩ A ∧ w ⊮ B`, supplies a witness world `w`. The rule introduces a
  **fresh prefix** `σ.n` (here: the fresh label `nw`, a fresh `Nat`) and records `σ.n` accessible
  from `σ`. We extend `ρ` by `ρ(σ.n) := w`. Because the prefix is **fresh** (occurs nowhere else on
  the branch), the extension does not disturb the existing assignment, and monotonicity is preserved
  because `ρ(σ) ≤ w` is exactly the witness condition. Persistence of T-formulas from `σ` to `σ.n`
  is justified by monotonicity of forcing (`w ≥ ρ(σ)` and `ρ(σ) ⊩ α ⟹ w ⊩ α`).

**Why freshness is essential.** If `σ.n` already carried constraints on the branch (or already had a
world assigned by `ρ`), the `Function.update worldOf nw w` re-assignment would silently overwrite a
constraint that other formulas depend on, breaking conditions (ii)/(iii). Freshness is what makes
"extend the model at the new prefix" a *conservative* extension. In Fitting's prose this is the
side-condition "`σ.n` is new to the branch/tableau" attached to the `F→`/`Tν`-style rules.

The exact soundness statement the literature gives (verified via dedicated literature search): *a set
`S` of prefixed signed formulas is satisfiable iff there is a Kripke model `(W,≤,⊩)` and a map
`m : Pfx(S) → W` with `m(σ) ≤ m(σ.n)` whenever both prefixes occur, `m(σ) ⊩ A` for every `T(A)@σ`, and
`m(σ) ⊮ A` for every `F(A)@σ`; every rule application preserves satisfiability to at least one child
branch.* (Fitting 2014, §5–6; Open Logic Project, *Intuitionistic Tableaux*.) The persistence step
("any formula forced at a state is forced at all accessible states") is factored out in Fitting's
presentation as the **Lift lemma** — the literature name for what CSLib calls `iforces_persistence`
(used inside `intRule_preserves_sat`).

**Citations** (grounded; see Appendix for full entries):
- M. Fitting, *Intuitionistic Logic, Model Theory and Forcing*, North-Holland, 1969 — original
  forcing/Beth model theory for IPL underpinning the prefix→world assignment; persistence lemma.
- M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*, Reidel, 1983 — cited in the CSLib
  module docstrings as **Ch. 4**; the *prefixed intuitionistic propositional tableau* soundness
  proper is in **Ch. 9, §9.5**, where the satisfiable-branch definition and per-rule
  satisfiability-preservation (incl. the F-→ fresh-prefix case) are given.
- A. Waaler & L. Wallen, "Tableaux for Intuitionistic Logics," **Ch. 5, pp. 255–296** in *Handbook of
  Tableau Methods* (D'Agostino, Gabbay, Hähnle, Posegga, eds.), Kluwer, 1999 — labelled/prefixed
  presentation; the *eigenvariable/fresh-label* condition on the F-→ rule and its soundness role.
- M. Fitting, "Nested Sequents for Intuitionistic Logics," *Notre Dame J. Formal Logic* 55(1):41–61,
  2014 — most accessible modern source stating the satisfiable-set definition (§5), the per-rule
  soundness proof (§6), and the Lift lemma explicitly.
- A. Chagrov & M. Zakharyaschev, *Modal Logic*, OUP, 1997, **§2.2** — Kripke semantics for IPL via
  the modal embedding; co-cited in the module docstring.

### F2 — The freshness invariant is the missing link (local grounding)

Mapping the literature side-condition to the Lean obligation `hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH`:

- `nwH` is the head of the per-branch `nextWorlds` list. World creation uses
  `intFImpRule … nextWorld …` which sets the fresh label to `nextWorld` and returns
  `nextWorld' = nextWorld + 1` and edge `(nextWorld, parentLabel)` (see `Rules.lean` lines 153–158,
  244–267). So `nwH` is *intended* to be a value strictly greater than every label currently on the
  branch.
- **But nothing in the current proof state records this.** The `key` suffices (Soundness.lean lines
  839–857) carries length invariants only; there is no hypothesis bounding labels by `nwH`.
  Therefore `hfresh` cannot be discharged — it is true *operationally* but unprovable *as stated*
  without strengthening the induction.
- The required invariant (per branch, threaded through `nextWorlds`/`pending`):

  `BranchLabelBound b nw : Prop := ∀ sf ∈ b, sf.label < nw`

  From `sf.label < nwH` we get `sf.label ≠ nwH` immediately (`Nat.ne_of_lt`), discharging both
  `hfresh` sorries (945, 961). The strict-`<` form (rather than `≠`) is the right choice because it
  is *preserved* across world creation: new labels are exactly `nwH < nwH+1 = nw'`, and persistence
  copies only old labels (all `< nwH < nw'`).

**Preservation obligations for `BranchLabelBound`** (these become small helper lemmas):
- *Closure step* (`bPers` closed): `done ++ [bPers]` — `bPers = applyPersistenceFixpoint bh edges _`.
  Need `BranchLabelBound bPers nwH`. Persistence (`applyAllTImpRules`) only adds T(ψ) at labels `w'`
  already on the branch (`intTImpRule` filters over `b.map (·.label)`), so it introduces **no new
  labels** ⇒ bound preserved from `BranchLabelBound bh nwH`.
- *Linear non-world-creating* (`newEdge = none`: T∧, F∨): `nw' = nwH`, new forms reuse `label`
  already on branch ⇒ bound preserved at `nw' = nwH`.
- *Linear world-creating* (`newEdge = some (nwH, label)`: F→): new forms have label `nwH` (the
  fresh world) plus persistence copies (labels already on branch, all `< nwH`). New bound is
  `nw' = nwH + 1`; every new label is `nwH < nwH+1` and every old label `< nwH < nwH+1` ⇒ preserved.
- *Branching* (F∧, T∨): `nw' = nwH`, children reuse existing `label` ⇒ preserved at `nwH`.

All four are arithmetic/membership facts (`omega` + `List.mem` reasoning), no semantics involved.

### F3 — The world-creating monotonicity machinery already exists

The hardest part of the F-→ case — proving the *updated* `worldOf'` stays monotone for the
*extended* edge set — is already fully proved as `monotoneEdges_update` (Soundness.lean lines
688–762). It requires:
- `hnw_not_child : ∀ parent, (nw, parent) ∉ edges`
- `hnw_not_parent : ∀ child, (child, nw) ∉ edges`
- `hnw_ne_parent : parentLabel ≠ nw`
- `hmono : MonotoneEdges worldOf edges`
- `hle : worldOf parentLabel ≤ w'`

The first three are **edge-freshness** facts. They follow from the same `BranchLabelBound` invariant
**extended to edges**: if every label appearing in `edges` is `< nw`, then `nw` is neither a child
nor a parent in `edges`, and `parentLabel < nw ⇒ parentLabel ≠ nw`. So the cleanest design is a
single combined invariant covering both branch labels and edge endpoints:

`FreshAbove b edges nw : Prop := (∀ sf ∈ b, sf.label < nw) ∧ (∀ (c p : Nat), (c,p) ∈ edges → c < nw ∧ p < nw)`

- `hle : worldOf parentLabel ≤ w'` comes for free: `intRule_preserves_sat`'s F-→ branch builds
  `w'` from `hw'_ge : worldOf label ≤ w'` (Soundness.lean lines 184–190), and `parentLabel = label`.
  In fact the existential `worldOf'` returned by `intRule_preserves_sat` *is* `Function.update worldOf nwH w'`.

### F4 — Anatomy of the linearResult `bp=bh` sorry (line 950)

From the live `lean_goal` at line 950, the goal is `⊢ False` with (relevant hypotheses):
- `hsat_p : intBranchSatisfied val botForces wo bh`
- `hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH` (currently itself a sorry'd `have`)
- `hsf_mem : sf ∈ bPers`, `hresult_sf : intApplyRuleFull sf nwH bPers = .linearResult newForms nw' newEdge`
- `hgo` : reducible to `intExpandBranches (done ++ [extendMany bPers newForms] ++ bt) … fuel'' closurePred = .closed`
- `ih` : the fuel IH (over arbitrary `branches/edgeSets`, fuel `fuel''`)
- `edges' := match newEdge with | none => edgesP | some e => edgesP ++ [e]`

Proof assembly (no new semantics, only wiring):

1. `have hsat_pers := applyPersistenceFixpoint_sat … wo bh edgesP (fuel''+1) hsat_p hmono_p`
   ⇒ `intBranchSatisfied val botForces wo bPers`.
2. `have hpres := intRule_preserves_sat … wo bPers sf hsf_mem hsat_pers nwH hfresh`.
   Then `rw [hresult_sf] at hpres` (the prior session's "rewrite the result equation first" note —
   needed because the lemma's conclusion is a `match` on `intApplyRuleFull …`, so it must be reduced
   to the `linearResult` arm before destructuring). Now
   `hpres : ∃ worldOf', (∀ k, k ≠ nwH → worldOf' k = wo k) ∧ intBranchSatisfied … worldOf' (extendMany bPers newForms)`.
3. `obtain ⟨wo', hwo'_eq, hsat'⟩ := hpres`.
4. Establish `MonotoneEdges wo' edges'`:
   - If `newEdge = none` (T∧/F∨): `edges' = edgesP` and `wo'` agrees with `wo` on all labels
     `< nwH` (which is all labels of `edgesP` by the edge-freshness invariant), so
     `MonotoneEdges wo' edgesP` reduces to `hmono_p`. (Because accessibility only ever consults
     labels present in `edgesP`, all `< nwH`, where `wo' = wo`.)
   - If `newEdge = some (nwH, label)` (F→): apply `monotoneEdges_update wo edgesP nwH label w' …`
     with the edge-freshness facts from `FreshAbove` and `hle` from step 2's witness. Note
     `wo' = Function.update wo nwH w'` definitionally in this arm, matching `monotoneEdges_update`'s
     conclusion `MonotoneEdges (Function.update wo nwH w') (edgesP ++ [(nwH, label)])`.
5. Apply `ih` to the new branch list with the new branch `(extendMany bPers newForms, edges')` at the
   `done`-tail position. Membership `(extendMany bPers newForms, edges') ∈ (done ++ [..] ++ bt).zip (doneEdges ++ [edges'] ++ edgesT)` is proved exactly as in the already-completed branchingResult
   `bp=bh` case (Soundness.lean lines 972–984): `List.zip_append` twice + `List.mem_append`,
   landing in the middle singleton. Length side-goals via `hdlength_*`/`hlength_*` as elsewhere.
   Supplying `hgo` (after `simp only [] at hgo` to collapse the `match`), `hsat'`, and the
   monotonicity from step 4 yields the `¬ intBranchSatisfied … wo' (extendMany bPers newForms)`,
   contradicting `hsat'` ⇒ `False`.

This is structurally the linear analogue of the branchingResult `bp=bh` proof already in the file;
the only extra is the `worldOf'` swap (steps 3–4), which the branching case avoids because its
`intRule_preserves_sat` arm keeps `worldOf` unchanged.

### F5 — Why the prior `bp=bh` linear attempts stalled

The handoff notes three real traps, all confirmed:
1. `intRule_preserves_sat`'s conclusion is a `match`, not a product — `.1`/`.2` fail; must
   `rw [hresult_sf]` first (handled in step 2 above).
2. `hgo` in linear/branching arms has the **`intExpandBranches … fuel''`** shape (not `…go…`), so
   the **fuel IH `ih`** is the right tool, not `ih_inner` (confirmed in the live goal: `ih` quantifies
   over `branches/edgeSets`).
3. The `worldOf'` from the F-→ case differs from `wo` at `nwH`, so the IH must be fed `wo'`, and the
   monotonicity obligation is for `edges'`, not `edgesP`. This is the step that genuinely needs
   `monotoneEdges_update` + freshness — and without the freshness invariant in scope, the attempt
   could not even *state* the hypotheses `monotoneEdges_update` demands. **This is the root cause of
   the stall: the missing freshness invariant blocks both `hfresh` and the monotonicity wiring.**

### F6 — Comparison with Classical/Soundness.lean

The classical case (`Tableau/Classical/`) has the same fuel+`go` induction but **two** parallel
lists (no `nextWorlds`, no edges, no world creation), so it never needs a freshness invariant or
`worldOf` update — its `intRule_preserves_sat` analogue keeps the (trivial) world map fixed. That is
why the classical proof closed without this machinery and the intuitionistic one did not: the
world-creating F-→ rule is the sole source of the difficulty, exactly as the literature predicts.

## Decisions

- **D1.** Introduce a freshness invariant `FreshAbove b edges nw` (branch labels `< nw` ∧ edge
  endpoints `< nw`) and thread it through the outer statement, the `key` suffices, and per-branch via
  `nextWorlds`/`pendingEdges`.
- **D2.** Discharge `hfresh` (945, 961) from the branch-label half via `Nat.ne_of_lt`.
- **D3.** Complete linearResult `bp=bh` (950) by the F4 assembly, reusing `monotoneEdges_update` and
  `applyPersistenceFixpoint_sat`; mirror the branchingResult `bp=bh` membership plumbing.
- **D4.** Do **not** refactor the algorithm (`intExpandBranches`) — reports 04 and this read agree the
  computational code is correct; only the proof needs strengthening. (Reuse-first: all needed
  helpers already exist in `Foundations`-adjacent local scope.)

## Recommendations (prioritized)

### Per-sorry recommendation table

| Line | Obligation | Strategy | New helper needed? |
|------|-----------|----------|--------------------|
| 945 | `hfresh` (linearResult): `∀ sf'∈bPers, sf'.label ≠ nwH` | From threaded `FreshAbove bPers _ nwH` branch-label half: `intro sf' h; exact Nat.ne_of_lt (hbound sf' h)`. Requires `FreshAbove` in scope (invariant strengthening). | Yes: `FreshAbove` def + threading; preservation lemmas (closure/persistence/linear/branch). |
| 950 | linearResult `bp=bh`: derive `False` | F4 assembly: `applyPersistenceFixpoint_sat` → `intRule_preserves_sat` (`rw [hresult_sf]` first) → `obtain ⟨wo',…⟩` → `MonotoneEdges wo' edges'` (via `monotoneEdges_update` when world-creating, else `hmono_p`) → apply fuel `ih` with middle-singleton membership (mirror lines 972–984) on `hsat'`. | No new lemma beyond `FreshAbove` (needed to supply `monotoneEdges_update`'s three edge-freshness args + `hfresh`). |
| 961 | `hfresh` (branchingResult): same as 945 | Identical to 945. | Same as 945. |

### Implementation phasing (revised)

- **Phase A — Freshness invariant (closes 945, 961; unblocks 950).**
  1. Define `FreshAbove (b : IBranch Atom) (edges : IEdges) (nw : Nat) : Prop`.
  2. Prove preservation lemmas:
     - `freshAbove_persistence`: `FreshAbove b edges nw → FreshAbove (applyPersistenceFixpoint b edges f) edges nw` (persistence adds no new labels; `intTImpRule` ranges over existing labels).
     - `freshAbove_linear_nonworld` (T∧, F∨): label reused ⇒ `FreshAbove (extendMany b nf) edges nw`.
     - `freshAbove_world_create` (F→): `FreshAbove (extendMany b nf) (edges++[(nw,l)]) (nw+1)` given `l < nw`.
     - `freshAbove_branch`: each child `extendMany b br` keeps `FreshAbove … edges nw`.
  3. Add `FreshAbove b edges nw` (paired with each branch via `nextWorlds`/`edgeSets`) to the
     `key` suffices hypotheses and to `intExpandBranches_closed_unsat`'s statement; thread it
     through every recursive call (initial branch `[F(φ)@0]` with `nw=1`, `edges=[]` satisfies
     `FreshAbove` trivially — see `intuitionisticTableau`).
  4. Discharge 945 and 961 with `Nat.ne_of_lt`.
- **Phase B — linearResult bp=bh (closes 950).** Execute the F4 assembly. With `FreshAbove` in
  scope from Phase A, all of `monotoneEdges_update`'s arguments are available.
- **Verification.** `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`;
  `grep -c sorry`; `lean_verify Cslib.Logic.PL.intuitionisticTableau_sound` to confirm no `sorryAx`.

**Granularity check.** The existing lemma decomposition is *adequate* — `intRule_preserves_sat`,
`monotoneEdges_update`, `applyPersistenceFixpoint_sat` are at the right level. The **only** missing
abstraction is the `FreshAbove` invariant and its four preservation lemmas. This is a strengthening,
not a redesign.

## Risks & Mitigations

- **R1 — Concurrent edits.** An implementation agent owns `.orchestrator-handoff.json` and may be
  editing the file; line numbers (945/950/961) may drift. *Mitigation*: recommendations key off
  semantic anchors (`hfresh have`, `linearResult bp=bh` case, `intRule_preserves_sat` application),
  not line numbers.
- **R2 — Threading `FreshAbove` through three nested inductions is verbose.** The length invariants
  already thread similarly; *mitigation*: bundle `FreshAbove` as a per-branch predicate quantified
  the same way as `MonotoneEdges` (i.e. universally over `(b, edges) ∈ branches.zip edgeSets`
  together with the corresponding `nw` — may require a 4-way zip or a parallel `∀ i` index form). The
  cleanest encoding pairs it with `nextWorlds`; consider a single
  `∀ b edges nw, (b,edges,nw) ∈ … → FreshAbove b edges nw` over a `List.zip₃`-style relation, or an
  indexed `∀ i (hi : i < branches.length), FreshAbove branches[i] edgeSets[i] nextWorlds[i]`.
- **R3 — `none` vs `some` edge arm in step 4.** The `edges'` definition is a `match newEdge`; the
  proof must `cases newEdge` (or `cases hresult`'s edge component). *Mitigation*: `intApplyRuleFull`
  only ever returns `newEdge = none` for non-world-creating linear rules and `some (nw, label)` for
  F→ (Rules.lean 244–267), so a two-way `cases` is exhaustive and each arm is short.
- **R4 — Zero-debt compliance.** No sorry deferral, no new axioms. The plan closes all three sorries
  structurally. If Phase A's threading proves intractable in one pass, mark the phase `[BLOCKED]`
  with the goal state — do **not** leave a placeholder.

## Verdict on plan revision

**`plan_revision_recommended = true`.** The existing plan (`plans/05_soundness-plan.md`) and reports
03/04 correctly anticipated the `∀ sf ∈ b, sf.label < nw` invariant, but the **implemented proof
never added it to the induction**, which is precisely why `hfresh` and the linear `bp=bh`
monotonicity wiring are stuck. The revised plan is narrow and additive:

1. **Phase A**: define and thread `FreshAbove`; prove 4 preservation lemmas; close 945 + 961.
2. **Phase B**: assemble linearResult `bp=bh` (F4) using the now-available freshness facts; close 950.

No algorithmic change, no new axioms, full reuse of existing `monotoneEdges_update` /
`intRule_preserves_sat` / `applyPersistenceFixpoint_sat`. Estimated ~150–250 lines across the two
phases.

## Appendix — References

- **[Fitting1969]** M. Fitting, *Intuitionistic Logic, Model Theory and Forcing*, Studies in Logic
  and the Foundations of Mathematics, North-Holland, Amsterdam, 1969. Prefixed/forcing tableaux for
  intuitionistic propositional and predicate logic; soundness via model-respecting prefix assignment.
- **[Fitting1983]** M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*, Synthese
  Library vol. 169, D. Reidel, Dordrecht, 1983. CSLib module docstrings cite **Ch. 4**; the
  *prefixed intuitionistic propositional tableau* soundness/completeness proper is in **Ch. 9, §9.5**
  (satisfiable-branch definition; per-rule satisfiability-preservation incl. the F-→ fresh-prefix
  case). (Cited in `Rules.lean`/`Expansion.lean` module docstrings.)
- **[WaalerWallen1999]** A. Waaler & L. Wallen, "Tableaux for Intuitionistic Logics," **Ch. 5,
  pp. 255–296** in M. D'Agostino, D. Gabbay, R. Hähnle, J. Posegga (eds.), *Handbook of Tableau
  Methods*, Kluwer, Dordrecht, 1999. Labelled/prefixed systems; eigenvariable (fresh-label) condition
  on the F-→ rule.
- **[Fitting2014]** M. Fitting, "Nested Sequents for Intuitionistic Logics," *Notre Dame Journal of
  Formal Logic* 55(1):41–61, 2014, DOI:10.1215/00294527-2377869. §5 prefixed IPL tableau rules; §6
  soundness/completeness with the satisfiable-set definition and the explicit **Lift lemma**
  (persistence). Most accessible modern exposition; the per-rule preservation argument matches the
  CSLib `intRule_preserves_sat` structure one-to-one.
- **[OpenLogic]** Open Logic Project, *Intuitionistic Tableaux* chapter
  (builds.openlogicproject.org). Freely available textbook presentation of prefixed signed tableaux
  for IPL with the satisfiable-branch definition and per-rule soundness (F-→ freshness) case.
- **[Handbook1999]** M. D'Agostino, D. M. Gabbay, R. Hähnle, J. Posegga (eds.), *Handbook of Tableau
  Methods*, Kluwer Academic Publishers, 1999, DOI:10.1007/978-94-017-1754-0. General signed-tableau
  soundness/completeness framework (Smullyan-style α/β analysis adapted to non-classical logics);
  Fitting's introductory chapter (pp. 1–98) states the prefixed-tableau soundness lemma in full
  generality (the modal ⟨a⟩ fresh-world case is the exact analogue of intuitionistic F-→).
- **[ChagrovZakharyaschev1997]** A. Chagrov & M. Zakharyaschev, *Modal Logic*, Oxford Logic Guides
  35, OUP, 1997, **§2.2**. Kripke semantics for IPL via the Gödel–McKinsey–Tarski embedding;
  co-cited in module docstrings.
- **Local file anchors**: `Soundness.lean` — `intRule_preserves_sat` (L83–266), `monotoneEdges_update`
  (L688–762), `applyPersistenceFixpoint_sat` (L404–420), inner induction `key`/`go` (L839–994);
  `Rules.lean` — `intFImpRule` (L153–158), `intApplyRuleFull` (L244–267); `Expansion.lean` —
  `intExpandBranches` / `.go` (L153–218).
