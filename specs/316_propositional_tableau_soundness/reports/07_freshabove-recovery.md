# Recovery Report: FreshAbove Machinery (Task 316)

- **Task**: 316 — propositional_tableau_soundness
- **Date**: 2026-06-24
- **Status**: RECOVERY COMPLETE — code reconstructed from transcripts, artifacts written
- **Source transcripts**:
  - `a3a08e73a2f1aa90c` (plan-06 implementation agent; created FreshAbove and lemmas)
  - `a9309a15c559f4aea` (follow-up agent; extended threading; latest state before revert)
- **Artifact**: `specs/316_propositional_tableau_soundness/recovered/freshabove-machinery.lean`

---

## Summary of What Was Lost and Recovered

Two agent sessions developed the `FreshAbove` freshness-invariant machinery for
`intExpandBranches_closed_unsat` in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`.
The code was reverted to the committed baseline (4 sorries at L945/950/961 and the L919
comment) before being committed. This report reconstructs the lost code.

**Total declarations recovered**: 8 standalone declarations + 1 large threading block + 1 call-site snippet.

**Lines recovered**: approximately 300–350 lines of Lean 4 across the recovery artifact.

**What was recovered**:
1. `def FreshAbove` — branch freshness invariant definition
2. `freshAbove_applyAllTImpRules` — preservation by persistence rule
3. `freshAbove_applyPersistenceFixpoint` — preservation by persistence fixpoint
4. `freshAbove_extendMany` — preservation by non-world-creating linear step
5. `freshAbove_world_create` — freshness upgrade for world-creating F(→) step
6. `monotoneEdges_of_agree` — monotonicity transfer under point-wise agreement (new lemma not in plan)
7. Threading of `FreshAbove` through `intExpandBranches_closed_unsat` — full strengthened induction
8. `hinitFresh` — proof of the initial `FreshAbove` for `intuitionisticTableau_sound` call site
9. The `hfresh` closure (discharging L945 and L961) — proved in the threading block

---

## Declaration Table

| Declaration | Final Signature (one line) | Status | Depends on | Insertion Point |
|-------------|---------------------------|--------|------------|-----------------|
| `FreshAbove` | `def FreshAbove (b : IBranch Atom) (edges : IEdges) (nw : Nat) : Prop` | **sorry-free** | `IBranch`, `IEdges` | After `monotoneEdges_update` (~L762), before `intExpandBranches_closed_unsat` (~L764) — in new `/-! ## Freshness Invariant -/` section |
| `freshAbove_applyAllTImpRules` | `private lemma freshAbove_applyAllTImpRules (b : IBranch Atom) (edges : IEdges) (nw : Nat) (hfresh : FreshAbove b edges nw) : FreshAbove (applyAllTImpRules b edges) edges nw` | **sorry-free** | `FreshAbove`, `applyAllTImpRules`, `intTImpRule` | After `FreshAbove` def |
| `freshAbove_applyPersistenceFixpoint` | `private lemma freshAbove_applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (nw : Nat) (fuel : Nat) (hfresh : FreshAbove b edges nw) : FreshAbove (applyPersistenceFixpoint b edges fuel) edges nw` | **sorry-free** | `freshAbove_applyAllTImpRules`, `applyPersistenceFixpoint` | After `freshAbove_applyAllTImpRules` |
| `freshAbove_extendMany` | `private lemma freshAbove_extendMany (b : IBranch Atom) (edges : IEdges) (nw : Nat) (newForms : List (ISF Atom)) (hfresh : FreshAbove b edges nw) (hnew : ∀ sf' ∈ newForms, sf'.label < nw) : FreshAbove (Branch.extendMany b newForms) edges nw` | **sorry-free** | `FreshAbove`, `Branch.extendMany` | After `freshAbove_applyPersistenceFixpoint` |
| `freshAbove_world_create` | `private lemma freshAbove_world_create (b : IBranch Atom) (edges : IEdges) (nw parentLabel : Nat) (newForms : List (ISF Atom)) (hfresh : FreshAbove b edges nw) (hparent_lt : parentLabel < nw) (hnew : ∀ sf' ∈ newForms, sf'.label ≤ nw) : FreshAbove (Branch.extendMany b newForms) (edges ++ [(nw, parentLabel)]) (nw + 1)` | **sorry-free** | `FreshAbove`, `Branch.extendMany` | After `freshAbove_extendMany` |
| `monotoneEdges_of_agree` | `private lemma monotoneEdges_of_agree {World : Type*} [Preorder World] (wo wo' : Nat → World) (edges : IEdges) (nw : Nat) (hfresh_edges : ∀ c p, (c, p) ∈ edges → c < nw ∧ p < nw) (hagree : ∀ k, k ≠ nw → wo' k = wo k) (hmono : MonotoneEdges wo edges) : MonotoneEdges wo' edges` | **sorry-free** | `FreshAbove`, `MonotoneEdges`, `isAccessible` | After `freshAbove_world_create` |
| `hfresh` (inline in threading) | `have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH := fun sf' hmem' hlab => absurd hlab (Nat.ne_of_lt (hfresh_bPers.1 sf' hmem'))` | **sorry-free** | `hfresh_bPers : FreshAbove bPers edgesH nwH` | Inside `intExpandBranches_closed_unsat` body, at former L945 and L961 (both `hfresh` sorry sites) |
| `hinitFresh` (call site) | `have hinitFresh : ∀ i (hi : i < [[⟨.neg, φ, 0⟩]].length), FreshAbove ...` | **sorry-free** | `FreshAbove` | Inside `intuitionisticTableau_sound`, before the `apply intExpandBranches_closed_unsat` call |
| Threading block (linearResult bp=bh) | Body of `intExpandBranches_closed_unsat` linearResult bp=bh case | **had sorry** (2 sub-sorries: FreshAbove for expanded branches + MonotoneEdges for `some e` arm) | all above | Former L950 sorry site |
| Threading block (branchingResult) | FreshAbove threading in branchingResult cases | **had sorry** (FreshAbove for new branches) | all above | Former L961 sorry + surrounding cases |

---

## Threading Plan

The `FreshAbove` invariant is threaded as an **indexed predicate** alongside the existing
`MonotoneEdges` pairing. Concretely:

### Shape of the threaded invariant

```
∀ i (hi : i < branches.length),
    FreshAbove branches[i] edgeSets[i]'(by omega) nextWorlds[i]'(by omega)
```

This is added to:
1. The **public signature** of `intExpandBranches_closed_unsat` (as a new hypothesis,
   after the three `*.length = branches.length` hypotheses).
2. The **`hcore` suffices** internal induction (same shape, same position).
3. The **`key` suffices** internal induction over the `go`-loop's pending list
   (same shape but indexing into `pending`/`pendingEdges`/`pendingNW`).

### How `FreshAbove` closes the hfresh sorries

At former L945 and L961 the proof needs `∀ sf' ∈ bPers, sf'.label ≠ nwH`. With the
threaded invariant in scope:

1. `hfresh_bh : FreshAbove bh edgesH nwH` — extracted at index 0 from `hpfresh`.
2. `hfresh_bPers : FreshAbove bPers edgesH nwH` — from `freshAbove_applyPersistenceFixpoint`.
3. `hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH` — via `Nat.ne_of_lt (hfresh_bPers.1 sf' hmem')`.

Both L945 and L961 sorries are replaced by a single `have` statement using `Nat.ne_of_lt`.

### How to discharge the remaining sorries (linearResult bp=bh, Phase B)

The linearResult `bp=bh` case (former L950) requires:

1. `applyPersistenceFixpoint_sat` → `hsat_pers : intBranchSatisfied val botForces wo bPers`
2. `intRule_preserves_sat` applied with `hfresh` → `hpres`
3. **`rw [hresult_sf] at hpres` FIRST** (conclusion is a `match`, not a product)
4. `obtain ⟨worldOf', hwo'_eq, hsat'⟩ := hpres`
5. Establish `MonotoneEdges worldOf' edges'`:
   - `newEdge = none` (T∧/F∨): use `monotoneEdges_of_agree` with `hfresh_bPers.2` and
     `fun k hne => (hwo'_eq k hne).symm`. This is now possible with the `monotoneEdges_of_agree`
     lemma recovered in this session.
   - `newEdge = some e` (F→): use `monotoneEdges_update` with:
     - `hnw_not_child`: from `hfresh_bPers.2 nwH parent hmem_e` gives `nwH < nwH` — contradiction
     - `hnw_not_parent`: from `hfresh_bPers.2 child nwH hmem_e` gives `nwH < nwH` — contradiction
     - `hnw_ne_parent`: from `hfresh sf hsf_mem` (sf.label ≠ nwH, and parentLabel = sf.label)
     - `hle`: `wo parentLabel ≤ w'` from the F→ arm of `intRule_preserves_sat`. **NOTE**: this
       requires that `intRule_preserves_sat` exposes `worldOf'` as `Function.update wo nwH w'`
       (which is what it does in the F→ branch internally). The current `obtain` form only gives
       `hwo'_eq`. One approach: use `worldOf' nwH` directly and derive `hle` from `hsat'`
       semantics (T(φ) and F(ψ) at nwH constrain worldOf' nwH). Alternative: extend
       `intRule_preserves_sat` to also return `worldOf parentLabel ≤ worldOf' nw` as a 4th
       component of the existential.
6. Supply FreshAbove for the new branches to the recursive `ih` call.
   - `newEdge = none`: use `freshAbove_extendMany` with labels from `hfresh_bPers`.
   - `newEdge = some (nwH, parentLabel)`: use `freshAbove_world_create` with `hfresh_bPers`
     and the fact that `parentLabel = sf.label < nwH` (from `hfresh`).
7. Apply the **fuel IH `ih`** (NOT `ih_inner`) to the expanded branch list.

---

## Re-Application Recipe

### Order to paste declarations (into Soundness.lean)

Insert all new standalone declarations **before** `intExpandBranches_closed_unsat` (currently
at L764 in the baseline file), in this order:

```
(existing) monotoneEdges_update ...  [L688–762]

/-! ## Freshness Invariant -/

def FreshAbove ...
private lemma freshAbove_applyAllTImpRules ...
private lemma freshAbove_applyPersistenceFixpoint ...
private lemma freshAbove_extendMany ...
private lemma freshAbove_world_create ...
private lemma monotoneEdges_of_agree ...

(existing) /-! If intExpandBranches returns closed ... -/
lemma intExpandBranches_closed_unsat ...  [L764+]
```

### Modifications to intExpandBranches_closed_unsat

1. **Add `FreshAbove` hypothesis** to the public signature (after `edgeSets.length = branches.length`):
   ```lean
   (∀ i (hi : i < branches.length), FreshAbove branches[i]
       edgeSets[i]'(by omega) nextWorlds[i]'(by omega)) →
   ```

2. **Mirror in `hcore` suffices**: add the same hypothesis.

3. **Pass through in the `suffices hcore by` block**: pass `hbranches_fresh` directly:
   ```lean
   exact hcore fuel branches expandedSets nextWorlds edgeSets
       hlength_exp hlength_nw hlength_edges hbranches_fresh
       h b edges hbe worldOf hmono hsat
   ```

4. **Add to the `key` suffices**: add `(∀ i (hi : i < pending.length), FreshAbove pending[i] ...)`.

5. **Pass through in the `from by` block** (applying `key` with `branches`): pass `hbranches_fresh`.

6. **In the `| cons bh bt ih_inner =>` arm**:
   - Extract `hfresh_bh` at index 0 from `hpfresh`.
   - Extract `hpfresh_bt` for the tail.
   - Derive `hfresh_bPers` via `freshAbove_applyPersistenceFixpoint`.
   - Replace BOTH `sorry` instances for `hfresh` with `Nat.ne_of_lt`.

7. **In the `ih_inner` closed case**: pass `hpfresh_bt` (no FreshAbove needed for `done`
   in the closed branch; `done` branches are not visited again).

8. **In the linearResult/branchingResult recursion via `ih`**: supply FreshAbove proofs
   using the lemmas above (see "remaining sorries" section).

### Verify after each step

1. After inserting the 6 standalone declarations: `lake build` should succeed (they are just
   additional definitions, not yet used).
2. After modifying the `intExpandBranches_closed_unsat` signature and threading:
   `lake build` — expect the three sorry sites (L945, L961, and L950) to produce warnings.
3. After discharging `hfresh` at L945 and L961: sorry count drops from 3 to 1.
4. After assembling the linearResult `bp=bh` case (Phase B): sorry count drops to 0.
5. Update the `intuitionisticTableau_sound` call site to pass `hinitFresh`.

### Known traps

1. **`rw [hresult_sf]` BEFORE `obtain`** — `intRule_preserves_sat`'s conclusion is a
   `match` on the `IntRuleResult`, not a product. Using `.1`/`.2` is invalid. Always
   `rw [hresult_sf] at hpres` first to specialize the match arm, then `obtain`.

2. **Use fuel IH `ih`, NOT `ih_inner`** — the recursion in the linearResult/branchingResult
   cases goes back to `intExpandBranches … fuel''`, so `ih` (which quantifies over all
   `branches`/`edgeSets`) is correct. `ih_inner` (the structural induction on `pending`) is
   NOT what is needed here. Using `ih_inner` was a confirmed trap in report 05.

3. **`List.zip_append` orientation** — the `List.zip_append` calls in the membership proofs
   for the `done` list use `hdlength_edges` (orientation `doneEdges.length = done.length`).
   The nested inner `zip_append` at the branchingResult `bp=bh` site needs `.symm`
   (orientation `done.length = doneEdges.length`). See the committed branchingResult `bp=bh`
   case at L978 in the baseline — it uses `(by exact hdlength_edges)` which is actually the
   source of the pre-existing `978:46` build error (Phase 0 of plan 06 fixes this to `.symm`).
   In the RECOVERY file, the branchingResult `bp=bh` case already has `.symm`.

4. **`monotoneEdges_of_agree` requires `isAccessible.go` induction** — the proof that any
   node reachable by `isAccessible.go` must appear as a child (resp. parent) in `edges` is
   an induction on the fuel argument of the DFS. The full proof is in the recovery file.

5. **`hinitFresh` indexing** — there were 5 iterated attempts at `hinitFresh` in the
   transcripts. The FINAL correct version uses `List.getElem_cons_zero` / `List.mem_singleton`
   and avoids a `List.getElem_nil` mismatch that earlier versions hit. Use the version in the
   recovery file's comment block.

6. **`intRule_preserves_sat` F→ witness access** — in the `newEdge = some e` arm of the
   `none`/`some` cases, to apply `monotoneEdges_update` you need `hle : wo parentLabel ≤ w'`.
   The current `intRule_preserves_sat` returns `∃ worldOf', (∀ k ≠ nw, worldOf' k = wo k) ∧
   intBranchSatisfied …`. It does NOT directly expose `hle`. Two paths forward:
   - **Option A** (preferred): extend `intRule_preserves_sat`'s existential to a 4-tuple
     `∃ worldOf' w', (∀ k ≠ nw, worldOf' k = wo k) ∧ worldOf' = Function.update wo nw w' ∧
     wo parentLabel ≤ w' ∧ intBranchSatisfied …`. This is a small signature change.
   - **Option B**: derive `hle` from `hsat'` by semantic reasoning (T(φ) at nwH satisfied
     implies the world assigned to nwH has `wo parentLabel ≤ worldOf' nwH` since F→ was the
     applied rule). This is less mechanical.
   The recovery artifact uses a `sorry` at this point with an explanation of both options.

---

## Confidence Assessment per Declaration

| Declaration | Confidence | Notes |
|-------------|-----------|-------|
| `def FreshAbove` | **High — faithfully recovered** | Identical definition appeared in both transcripts; two independent passes reached the same form |
| `freshAbove_applyAllTImpRules` | **High — faithfully recovered** | Final form appeared twice in a3a08e7 (early and late); both versions are consistent; the later version is slightly cleaner |
| `freshAbove_applyPersistenceFixpoint` | **High — faithfully recovered** | Simple induction; appeared twice in a3a08e7; both versions identical |
| `freshAbove_extendMany` | **High — faithfully recovered** | Appeared in both the `none` variant (first pass) and the term-mode rewrite (second pass); the term-mode version is the final form |
| `freshAbove_world_create` | **High — faithfully recovered** | Appeared as `freshAbove_extendMany_some` in first pass, then as `freshAbove_world_create` in final form; the two are substantively identical |
| `monotoneEdges_of_agree` | **High — faithfully recovered** | Complete proof in a3a08e7 lines 1130–1267; the `hw2_child` and `hw1_parent` sub-lemmas are fully proved by induction on fuel |
| Threading block (hfresh closure) | **High — faithfully recovered** | The `Nat.ne_of_lt` pattern appeared explicitly in a9309a1 |
| Threading block (FreshAbove indexing / hcore / key) | **High — faithfully recovered** | Multiple complete versions appeared; the a9309a1 version is clearly the latest |
| Threading (linearResult bp=bh, sorry sub-goals) | **Partial — structure recovered** | The shape is complete but the sorry placeholders represent genuine remaining work that had not been solved in either transcript |
| `hinitFresh` | **High — faithfully recovered** | 5 iterations in a9309a1; the last version (L1719–L1730 in the raw file) is definitively the final form |
| Threading (FreshAbove for expanded branches in recursion) | **Low — only had sorry** | Both transcripts show `sorry -- FreshAbove for expanded branches (deferred)` at these sites; no complete proof was found in either transcript |
