# Implementation Plan: Task #316 (Revised — Round 6)

- **Task**: 316 - Propositional Tableau Soundness
- **Status**: [IN PROGRESS] — FreshAbove machinery built then accidentally reverted; now RECOVERED (see "Recovery Status" below). Working tree at green 4-sorry baseline.
- **Effort**: 5 hours (≈3h remaining: re-apply recovered machinery + close the F→ monotonicity gap)
- **Dependencies**: None (all upstream machinery is proved and sorry-free)
- **Research Inputs**: specs/316_propositional_tableau_soundness/reports/05_intuitionistic-soundness-induction.md, specs/316_propositional_tableau_soundness/reports/06_research-verification.md, specs/316_propositional_tableau_soundness/reports/07_freshabove-recovery.md, specs/316_propositional_tableau_soundness/reports/04_b4-hard-research.md
- **Artifacts**: plans/06_soundness-plan-revised.md (this file); recovered/freshabove-machinery.lean (recovered code)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, lean4.md, cslib.md
- **Type**: cslib
- **Lean Intent**: true

## Recovery Status (updated 2026-06-24)

The `FreshAbove` approach below was **implemented across two sessions and then accidentally reverted to
baseline before being committed** (an agent, finding the in-progress file build-red, ran `git checkout`
instead of fixing forward — losing the uncommitted work). The code was **recovered from the agent
transcripts** and is preserved in:
- `specs/316_propositional_tableau_soundness/recovered/freshabove-machinery.lean` — paste-ready, 8
  declarations (6 proved sorry-free, 2 threading blocks had sorry), UNVERIFIED pending a build check.
- `specs/316_propositional_tableau_soundness/reports/07_freshabove-recovery.md` — per-declaration
  status, insertion points, threading plan, and a re-application recipe.

**Current working-tree state**: `Intuitionistic/Soundness.lean` is at the **committed green baseline**
— 4 sorries (live: 945, 950, 961; comment: 919) and it **builds** (the `978:46`/`.symm` issue described
below does NOT exist at the baseline; it was an artifact of a since-reverted edit). The next session
should re-apply the recovered machinery onto this baseline, NOT restart from scratch.

**Corrected gap (supersedes F3 below)**: recovery confirmed that `worldOf parentLabel ≤ w'` does NOT
"come for free" from `intRule_preserves_sat` — the F(→) arm of the `linearResult bp=bh` case needs that
inequality exposed, which requires **extending `intRule_preserves_sat`'s return from a 3-tuple to a
4-tuple** (adding the `hle : worldOf parentLabel ≤ w'` witness). This is the one genuine remaining
obstacle and contradicts the original Non-Goal "Changing `intRule_preserves_sat`'s signature" — that
Non-Goal is now RETRACTED (see Phase B).

## Overview

This is a **targeted, additive revision** of plan `05_soundness-plan.md`, not a rewrite. The
implementation reached the final wall: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
was driven from 8 sorries down to **4** (live sorries at lines 945, 950, 961, plus a non-blocking
comment at 919). Two of those (the `hfresh` obligations at 945 and 961) are **unprovable as stated**.
(A transient `978:46` build error existed only in a since-reverted intermediate edit; the committed
baseline builds green.)

The conceptual blocker, confirmed by research report 05 against the canonical Fitting-style argument
(Fitting 1983 Ch. 9 §9.5; Fitting 2014 §6; Waaler–Wallen Ch. 5), is **freshness**: the obligation
`hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH` cannot be discharged because the nested induction
(`hcore` over `fuel'`, `key` over `pending`) carries **no invariant relating the new world label `nwH`
(`nextWorld`) to the branch's existing labels.** The literature side-condition "the new prefix is fresh
to the branch" is exactly the missing invariant. The fix is to define and thread a `FreshAbove`
invariant (branch labels `< nw` ∧ edge endpoints `< nw`), prove ~4 small preservation lemmas, and
close both `hfresh` sorries via `Nat.ne_of_lt`. With `FreshAbove` in scope, the remaining
`linearResult bp=bh` sorry (950) becomes a mechanical assembly mirroring the already-completed
`branchingResult bp=bh` case.

**Definition of done**: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`
succeeds with **zero sorries**; `lean_verify` confirms `intuitionisticTableau_sound` and
`minimalTableau_sound` are free of `sorryAx`.

### Research Integration

Newly integrated report: **05_intuitionistic-soundness-induction.md**. Key findings encoded into this plan:

- **F1/F2 (the missing link)**: The single conceptual blocker is freshness. `hfresh` is true
  *operationally* (world creation uses `nextWorld`, strictly greater than every existing label) but
  unprovable *as stated* because no induction hypothesis records `sf.label < nwH`. The literature
  (Fitting) requires the new prefix to be fresh to the branch; the strict-`<` form is the right
  choice because it is *preserved* across world creation (`nwH < nwH+1`).
- **F3 (machinery already exists)**: `monotoneEdges_update` (Soundness.lean L688–762) is already
  proved and consumes exactly the three edge-freshness facts (`nw` not a child, `nw` not a parent,
  `parentLabel ≠ nw`) plus `worldOf parentLabel ≤ w'`. All three edge-freshness facts follow from
  the **edge half** of `FreshAbove`; `worldOf parentLabel ≤ w'` comes for free from
  `intRule_preserves_sat`'s F-→ witness.
- **F4 (linearResult assembly recipe)**: `applyPersistenceFixpoint_sat` → `intRule_preserves_sat`
  (`rw [hresult_sf]` **first** — the conclusion is a `match`, not a product, so `.1`/`.2` are
  invalid) → `obtain ⟨wo', hwo'_eq, hsat'⟩` → establish `MonotoneEdges wo' edges'` (via
  `monotoneEdges_update` when world-creating, else `hmono_p`) → apply the **fuel IH `ih`** (NOT the
  pending IH `ih_inner`) with middle-singleton membership, mirroring the branchingResult `bp=bh`
  membership plumbing at L972–985.
- **F5 (why prior linear attempts stalled)**: Three confirmed traps — (1) `intRule_preserves_sat`
  conclusion is a `match` requiring `rw [hresult_sf]` first; (2) `hgo` has the `intExpandBranches …
  fuel''` shape so the fuel IH `ih` is correct, not `ih_inner`; (3) the `worldOf'` from F-→ differs
  from `wo` at `nwH`, so the IH must be fed `wo'` and monotonicity must be re-established for
  `edges'` — which is impossible to even *state* without the freshness invariant.
- **D4 (no redesign)**: No algorithmic change to `intExpandBranches`/`intStepBranch`. The
  computational code is correct; only the proof needs strengthening. This is additive.
- **Verdict**: `plan_revision_recommended = true`; narrow and additive; ~150–250 lines.

### Preserved Assets (committed baseline + recovered code — do NOT restart)

The working tree is at the **committed green baseline** (4 sorries). The following are already proved
and sorry-free in that baseline and **must NOT be re-derived**:

| Asset | Location | Status |
|-------|----------|--------|
| `intRule_preserves_sat` (existential `worldOf'`) | Soundness.lean L83–266 | sorry-free; reuse (but see Phase B — needs 4-tuple extension) |
| `monotoneEdges_update` | Soundness.lean L688–762 | sorry-free; reuse |
| `applyPersistenceFixpoint_sat` | Soundness.lean L404–420 | sorry-free; reuse |
| `monotoneEdges_go` | Soundness.lean | sorry-free; reuse |
| `iforces_persistence` (literature "Lift"/persistence lemma) | Soundness.lean | sorry-free; reuse |
| outer 819 gap, 922 sf-witness, both `bp∈bt` cases | Soundness.lean | already discharged in baseline |
| **branchingResult `bp=bh` case** | Soundness.lean L962–989 | proved; the linear case mirrors it |

Additionally, the following `FreshAbove` machinery was built and is **RECOVERED** (in
`recovered/freshabove-machinery.lean`) — re-apply rather than re-derive (status from report 07):

| Recovered declaration | Status |
|-----------------------|--------|
| `def FreshAbove` | sorry-free |
| `freshAbove_applyAllTImpRules` (persistence preservation) | sorry-free |
| `freshAbove_applyPersistenceFixpoint` (fixpoint preservation) | sorry-free |
| `freshAbove_extendMany` (+ `_none`, `_some`; linear non-world-creating) | sorry-free |
| `freshAbove_world_create` (F→ world-creating) | sorry-free |
| `monotoneEdges_of_agree` (monotonicity transfer, `newEdge = none` arm) | sorry-free |
| `hfresh` closure (L945 + L961) via `Nat.ne_of_lt` | sorry-free (re-applies once threaded) |
| linearResult `bp=bh` threading + branchingResult FreshAbove recursion | **had sorry** — blocked on the F→ monotonicity gap (Phase B) |

Live sorries remaining in the baseline: **L945** (`hfresh`, linearResult), **L950** (linearResult
`bp=bh`), **L961** (`hfresh`, branchingResult). The L919 line is a comment, not a live `sorry`.

### Prior Plan Reference

Plan 05 anticipated the `∀ sf ∈ b, sf.label < nw` invariant in its Phase 3 notes ("Add `nextWorld`
freshness invariant"), and reports 03/04 named it, but **the implemented proof never actually added
it to the induction** — which is precisely the root cause of the stall (report 05, F2/F5). Plan 05's
Phases 1, 2, and the bulk of Phase 3 are effectively done in the working tree (8→4 sorries). This
revision supersedes plan 05's remaining open work with the concrete `FreshAbove` mechanism.

### Roadmap Alignment

No specific ROADMAP.md items reference tableau soundness directly. This task advances the
propositional logic foundations underpinning the decidability instances.

## Goals & Non-Goals

**Goals**:
- Restore a green build by fixing the `978:46` error (a `List.zip_append` orientation mismatch
  needing `.symm` on `hdlength_edges`).
- Define `FreshAbove b edges nw` (branch labels `< nw` ∧ edge endpoints `< nw`) and thread it through
  the `key` suffices and `intExpandBranches_closed_unsat`'s statement.
- Prove ~4 small preservation lemmas (closure/persistence, linear non-world-creating, linear
  world-creating, branching) establishing `FreshAbove` is preserved by each step.
- Close both `hfresh` sorries (945, 961) via `Nat.ne_of_lt` from the branch-label half of `FreshAbove`.
- Assemble the `linearResult bp=bh` case (950) via the report's F4 recipe, reusing
  `monotoneEdges_update` / `intRule_preserves_sat` / `applyPersistenceFixpoint_sat`.
- Achieve **zero sorry** in `intuitionisticTableau_sound` and `minimalTableau_sound`.

**Non-Goals**:
- Refactoring algorithmic code (`intExpandBranches`, `intStepBranch`, `applyAllTImpRules`,
  `intApplyRuleFull`). Report 05 D4 confirms the computation is correct.
- Re-deriving any of the Preserved Assets above.
- New axioms or sorry deferral. Zero-debt: every sorry is closed structurally.
- Adding `Fitting1983` to `references.bib` (separate task); proving completeness (separate module).
- ~~Changing `intRule_preserves_sat`'s signature~~ — **RETRACTED** (2026-06-24): recovery (report 07)
  found the `linearResult bp=bh` F→ arm DOES require exposing `worldOf parentLabel ≤ w'`, which means
  `intRule_preserves_sat` must be extended from a 3-tuple to a 4-tuple return. This is now in-scope for
  Phase B.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Threading `FreshAbove` through three nested inductions is verbose | M | H | Pair it per-branch the same way `MonotoneEdges` is already paired (universally over `(b, edges) ∈ branches.zip edgeSets` with the corresponding `nextWorlds` entry). Consider an indexed `∀ i (hi : i < branches.length), FreshAbove branches[i] edgeSets[i] nextWorlds[i]` form, or pair with `nextWorlds`. (Report 05 R2.) |
| `none` vs `some` edge arm in the F4 monotonicity step | M | M | `edges'` is `match newEdge`; do `cases newEdge`. `intApplyRuleFull` returns `none` for non-world-creating linear (T∧, F∨) and `some (nw, label)` for F→ only (Rules.lean L244–267), so a two-way `cases` is exhaustive and each arm is short. (Report 05 R3.) |
| `intRule_preserves_sat` conclusion is a `match`, not a product | H | H (known trap) | `rw [hresult_sf] at hpres` **before** `obtain`. Do not use `.1`/`.2`. (Report 05 F4 step 2, F5 trap 1.) |
| Wrong IH chosen (`ih_inner` vs `ih`) | H | M | The world-creating/linear arms recurse via `intExpandBranches … fuel''`, so use the **fuel IH `ih`**, not the pending IH `ih_inner`. Confirmed against the live goal: `ih` quantifies over `branches/edgeSets`. (Report 05 F4 step 5, F5 trap 2.) |
| HeartBeat timeout on the nested induction | M | M | The induction already carries length invariants without timing out; `FreshAbove` adds one more parallel predicate. Use `set_option maxHeartbeats` only if a build times out. |
| Phase A threading proves intractable in one pass | M | L | Per report 05 R4: mark the phase `[BLOCKED]` with the exact goal state — do **not** leave a placeholder or vacuous `def := True`. Zero-debt enforced. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | A | 0 |
| 3 | B | A |
| 4 | C | B |

Phase 0 must restore a green build before any proof work. Phases A→B→C are strictly sequential
(B needs `FreshAbove` from A; C is verification of A+B). No parallelism across these phases.

---

### Phase 0: Restore green build (fix the `978:46` error) [COMPLETED]

**STATUS NOTE (2026-06-24)**: This phase is **moot at the current baseline**. The committed baseline
builds green with the original `by exact hdlength_edges` orientation (NO `.symm`). The `978:46` error
only ever appeared in a since-reverted intermediate edit; the verification report 06 explicitly warned
*against* adding `.symm`. Do NOT re-introduce a `.symm` here. If a re-application of the recovered
`FreshAbove` machinery shifts this code and the orientation breaks, resolve it against the live
`lean_goal` at that position — do not assume `.symm`.

**Goal (historical)**: restore a green `lake build`. Line ~978 passes `hdlength_edges` to
`List.zip_append`; resolve any orientation mismatch against the live goal, not by assuming `.symm`.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` and capture the
      exact error at `978:46`.
- [ ] At line ~978, change `rw [List.zip_append (by exact hdlength_edges)]` so the length proof has
      the orientation `List.zip_append` expects — use `hdlength_edges.symm` (or `(by exact
      hdlength_edges.symm)` / `(by simp [hdlength_edges])` as appropriate to the goal direction at
      that nested `zip_append`). Confirm with `lean_goal` at the `by` position which orientation the
      side-goal demands before editing.
- [ ] Re-run the scoped build; it must compile with exactly the **3 expected sorry warnings** (945,
      950, 961) and **no errors**.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` — line ~978 only.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` succeeds (warnings for
  the 3 sorries only; zero errors).
- `grep -c sorry` on the file returns 4 (3 live + 1 comment), unchanged from start.

---

### Phase A: Define and thread `FreshAbove`; prove preservation lemmas; close both `hfresh` sorries (945, 961) [PARTIAL]

**STATUS NOTE (2026-06-24)**: This phase was COMPLETED once in the working tree (all of `FreshAbove` +
preservation lemmas proved sorry-free, both `hfresh` sorries closed) but the work was reverted before
commit. The code is **recovered** in `recovered/freshabove-machinery.lean` (declarations marked
sorry-free per report 07). Re-application steps: (1) paste the recovered declarations at the insertion
points in report 07, (2) thread `FreshAbove` through the `key`/`intExpandBranches_closed_unsat`
induction, (3) close `hfresh` via `Nat.ne_of_lt`, (4) scoped build, (5) **COMMIT immediately** so this
progress cannot be lost again. The declarations below are the design spec the recovered code implements.

**Goal**: Introduce the freshness invariant the induction is missing, prove it is preserved by every
step, and discharge both `hfresh` obligations.

**Tasks**:
- [ ] **Define the invariant** (report 05 D1, F3):
      ```
      def FreshAbove (b : IBranch Atom) (edges : IEdges) (nw : Nat) : Prop :=
        (∀ sf ∈ b, sf.label < nw) ∧ (∀ c p : Nat, (c, p) ∈ edges → c < nw ∧ p < nw)
      ```
      (Use the exact `IBranch`/`IEdges` types and `sf.label` accessor as they appear in the file.)
- [ ] **Prove the ~4 preservation lemmas** (all arithmetic/membership, no semantics — report 05 F2):
  - `freshAbove_persistence`: `FreshAbove b edges nw → FreshAbove (applyPersistenceFixpoint b edges f) edges nw`.
    Persistence (`applyAllTImpRules`/`intTImpRule`) only adds `T(ψ)` at labels `w'` already on the
    branch (it filters over `b.map (·.label)`), so it introduces **no new labels** ⇒ bound preserved.
  - `freshAbove_linear_nonworld` (T∧, F∨; `newEdge = none`, `nw' = nwH`): new forms reuse a `label`
    already on the branch ⇒ `FreshAbove (Branch.extendMany b newForms) edges nwH`.
  - `freshAbove_world_create` (F→; `newEdge = some (nwH, label)`, `nw' = nwH + 1`, given `label < nwH`):
    new forms have label `nwH` (the fresh world) plus persistence copies (all old labels `< nwH`);
    every new label is `nwH < nwH+1` and every old `< nwH < nwH+1`; the new edge endpoints are
    `nwH < nwH+1` and `label < nwH < nwH+1` ⇒ `FreshAbove (Branch.extendMany b newForms)
    (edges ++ [(nwH, label)]) (nwH + 1)`.
  - `freshAbove_branch` (F∧, T∨; `nw' = nwH`): each child `Branch.extendMany b br` reuses existing
    labels ⇒ `FreshAbove … edges nwH`.
  - Discharge each with `omega` + `List.mem` reasoning. Use `lean_multi_attempt` before editing.
- [ ] **Thread `FreshAbove` through the induction** (report 05 D1, R2): add `FreshAbove b edges nw`
      (paired per-branch with the corresponding `nextWorlds`/`edgeSets` entry) to the hypotheses of
      the `key` suffices and to `intExpandBranches_closed_unsat`'s statement; re-establish it at every
      recursive call using the preservation lemmas above. The **initial** branch `[F(φ)@0]` with
      `nw = 1`, `edges = []` satisfies `FreshAbove` trivially (`0 < 1`, no edges) — supply this at the
      call site in `intuitionisticTableau`. Pair the invariant the same way `MonotoneEdges` is
      already paired (e.g. an indexed `∀ i (hi : i < branches.length), FreshAbove branches[i]
      edgeSets[i] nextWorlds[i]`, or a parallel `∀ (b,edges,nw) ∈ zip₃ …` form).
- [ ] **Close `hfresh` at 945 and 961**: with `FreshAbove bPers _ nwH` in scope, replace each
      `sorry` with `intro sf' h; exact Nat.ne_of_lt (hbound sf' h)` (where `hbound` is the branch-label
      half of the threaded `FreshAbove`). (Report 05 D2.)
- [ ] Verify at each sorry site with `lean_goal`, then build.

**Timing**: 2.5 hours

**Depends on**: 0

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` — add `FreshAbove` def + 4
  preservation lemmas; strengthen the `key` suffices and `intExpandBranches_closed_unsat` statement;
  thread through recursive calls; replace sorries at 945 and 961.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` compiles; sorry count
  drops from 3 to 1 (only the linearResult `bp=bh` at the former line 950 remains).
- `lean_verify` on the 4 preservation lemmas shows no axioms/sorry.
- **Phase must end at a green build** (one remaining expected sorry warning; zero errors).

---

### Phase B: Assemble `linearResult bp=bh` case (close 950) [NOT STARTED]

**STATUS NOTE (2026-06-24)**: This is the **one genuine remaining obstacle** for task 316. The recovered
threading for this case still had a `sorry` (per report 07) because the F→ arm needs
`hle : worldOf parentLabel ≤ w'` to feed `monotoneEdges_update`, and that inequality is NOT currently
returned by `intRule_preserves_sat`. **Prerequisite step for Phase B**: extend `intRule_preserves_sat`'s
F→ witness from a 3-tuple `⟨wo', hwo'_eq, hsat'⟩` to a 4-tuple `⟨wo', hwo'_eq, hsat', hle⟩` exposing
`worldOf parentLabel ≤ w'` (the value `w'` is the accessible witness world from the Kripke truth
condition; the inequality holds because `w'` is reachable from `worldOf parentLabel`). Then the F4
assembly proceeds as written below. The `none` arm (T∧/F∨) is already handled by the recovered
`monotoneEdges_of_agree` lemma.

**Goal**: Execute the report's F4 assembly to discharge the final sorry. With `FreshAbove` in scope
from Phase A and the 4-tuple `intRule_preserves_sat`, all of `monotoneEdges_update`'s arguments are
available.

**Tasks** (report 05 F4, D3 — mechanical, mirrors branchingResult `bp=bh` at L962–989):
- [ ] `simp only [] at hgo` to collapse the `match` in `hgo` (it has the `intExpandBranches … fuel''`
      shape).
- [ ] `have hsat_pers := applyPersistenceFixpoint_sat … wo bh edgesP (fuel''+1) hsat_p hmono_p`
      ⇒ `intBranchSatisfied val botForces wo bPers`.
- [ ] `have hpres := intRule_preserves_sat … wo bPers sf hsf_mem hsat_pers nwH hfresh`, then
      **`rw [hresult_sf] at hpres` FIRST** (conclusion is a `match`, not a product — `.1`/`.2` invalid).
      Now `hpres : ∃ worldOf', (∀ k, k ≠ nwH → worldOf' k = wo k) ∧ intBranchSatisfied … worldOf'
      (Branch.extendMany bPers newForms)`.
- [ ] `obtain ⟨wo', hwo'_eq, hsat'⟩ := hpres`.
- [ ] **Establish `MonotoneEdges wo' edges'`** where `edges' := match newEdge with | none => edgesP |
      some e => edgesP ++ [e]`. `cases newEdge`:
  - `none` (T∧/F∨): `edges' = edgesP`; `wo'` agrees with `wo` on all labels `< nwH` (all of
    `edgesP`'s labels, by the edge half of `FreshAbove`), so `MonotoneEdges wo' edgesP` reduces to
    `hmono_p`.
  - `some (nwH, label)` (F→): apply `monotoneEdges_update wo edgesP nwH label w' …` with the three
    edge-freshness facts from `FreshAbove`'s edge half (`nw` not a child, `nw` not a parent,
    `parentLabel ≠ nw`) and `hle : worldOf parentLabel ≤ w'` from the `intRule_preserves_sat`
    witness. Note `wo' = Function.update wo nwH w'` definitionally in this arm, matching
    `monotoneEdges_update`'s conclusion.
- [ ] **Apply the fuel IH `ih`** (NOT `ih_inner`) to the new branch list, placing
      `(Branch.extendMany bPers newForms, edges')` at the `done`-tail (middle-singleton) position.
      Prove membership exactly as the branchingResult `bp=bh` case at L972–985: `List.zip_append`
      twice + `List.mem_append`, landing in the middle singleton; length side-goals via
      `hdlength_*`/`hlength_*` (mind the `.symm` orientation lesson from Phase 0). Feed `hgo`,
      `hsat'`, and the monotonicity from the previous step. The IH yields
      `¬ intBranchSatisfied … wo' (Branch.extendMany bPers newForms)`, contradicting `hsat'` ⇒ `False`.
- [ ] Use `lean_goal` at each step and `lean_multi_attempt` before committing edits.

**Timing**: 1.5 hours

**Depends on**: A

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` — replace the linearResult
  `bp=bh` sorry (former line 950).

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` compiles with **zero
  sorry warnings**.
- `grep -c sorry` on the file returns 1 (the L919 comment only) or 0 if the comment is also removed.
- **Phase must end at a green, sorry-free build.**

---

### Phase C: Build verification and CI [NOT STARTED]

**Goal**: Confirm the complete build is sorry-free and passes CI.

**Tasks**:
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` — zero sorry warnings.
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.Soundness` — zero sorry warnings.
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` — zero sorry warnings.
- [ ] `lean_verify` on `intuitionisticTableau_sound`, `minimalTableau_sound`, and
      `intExpandBranches_closed_unsat` — no `sorryAx`; axioms limited to `propext`, `Quot.sound`,
      `Classical.choice`.
- [ ] `lake exe checkInitImports`; `lake exe lint-style`; `lake test` — all pass (fix minor style
      issues if reported).
- [ ] `grep -rn "sorry" Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` returns
      only comments (or nothing).

**Timing**: 0.5 hours

**Depends on**: B

**Files to modify**:
- None expected (verification only); minor style fixes if `lint-style` reports issues.

**Verification**:
- All CI commands pass; the file is sorry-free.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` compiles with zero sorry.
- [ ] `lean_verify Cslib.Logic.PL.intuitionisticTableau_sound` shows no sorry; expected axioms only.
- [ ] `lean_verify Cslib.Logic.PL.minimalTableau_sound` shows no sorry.
- [ ] `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` shows no sorry.
- [ ] `lake test` passes with no regressions.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.

## Artifacts & Outputs

- `specs/316_propositional_tableau_soundness/plans/06_soundness-plan-revised.md` (this file)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (modified: `FreshAbove` + 4
  preservation lemmas added; build error fixed; all 3 live sorries removed)
- `specs/316_propositional_tableau_soundness/summaries/06_soundness-summary.md` (post-implementation)

## Rollback/Contingency

If a sorry cannot be removed (report 05 R4 — zero-debt, no placeholders):
1. Mark the specific phase **[BLOCKED]** with the exact `lean_goal` state that could not be closed.
2. Preserve all completed work (each phase's removals are independently useful progress).
3. **Do NOT** leave a placeholder, vacuous `def := True`, or deferred sorry.
4. If Phase A's threading proves intractable in one pass, capture the goal state at the failing
   recursive call and the precise `FreshAbove` shape that did not unify, then escalate.
5. `git stash`/`git checkout` to revert only if a change breaks the previously-green build — but note
   the working tree (8→4 sorries) is the baseline to preserve, not the committed version.
