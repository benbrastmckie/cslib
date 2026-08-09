# Implementation Plan: Uniform frame for `openBranch_countermodel` conjunct 1

- **Task**: 603 - Construct a uniform frame for openBranch_countermodel and discharge the upward-closure conjunct
- **Status**: [COMPLETED]
- **Effort**: 6.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/603_construct_uniform_frame_for_openbranch_countermodel/reports/01_uniform-frame-construction.md`
- **Artifacts**: plans/01_rawedges-upward-closure.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Discharge conjunct 1 (upward closure of `intExtractValuation b` along `intAccessPreorder edges`)
for a uniformly-constructed `edges`, by instantiating `edges := rawEdges` — the tree-only
parent-child edge witness `intExpandBranches_openBranch_sat` already produces and
`openBranch_countermodel` currently discards as `_rawEdges`
(`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:7914`). The proof is the
already-sorry-free `IPosPersistRaw` (Scheme.lean:6701-6704) specialized to `χ := .atom p` and
chained over `Relation.ReflTransGen` by induction. Closing the one plumbing gap —
`IPosPersistRaw`'s `b.any (fun sf => sf.label == w') = true` side condition — requires two new
private corollaries plus one additional conjunct on `intExpandBranches_openBranch_sat`'s
existential, following the already-landed `ForestComparable` precedent in the same file. Done =
a new sorry-free lemma `openBranch_rawEdges_upward_closed` in Scheme.lean, full `lake build`
green, and the file's pre-existing sorries (Scheme.lean:768 and Scheme.lean:7965) unchanged in
count and location.

### Research Integration

Findings taken directly from `reports/01_uniform-frame-construction.md` and re-confirmed
against the source during planning:

- `intExpandBranches_openBranch_sat` (Scheme.lean:6815-6844) already returns
  `∃ edges rawEdges lbEdges nwF, ... ∧ IPosPersistRaw rawEdges b ∧ ... ∧ ForestComparable nwF rawEdges`.
  `openBranch_countermodel` (Scheme.lean:7914) discards `rawEdges` and the `IPosPersistRaw`
  conjunct (`_rawEdges`, `_hpp`).
- `IPosPersistRaw` is discharged sorry-free at the induction exit (Scheme.lean:7052-7055) via
  `applyPersistenceFixpoint_copy_complete`.
- The `ForestComparable` derivation (`edges_shape_of_worldHist` at Scheme.lean:3355-3382,
  `IWorldHist_forestComparable` at Scheme.lean:3491-3517, computed at the exit site
  Scheme.lean:7058) is the exact structural precedent: a pure corollary of already-threaded
  `IWorldHist`/`IWorldHistCounter`, needing no new invariant through the 10-case induction.
- `edges_shape_of_worldHist` already extracts `1 ≤ c < nw` internally and discards it
  (`_hc1 _hc2` at Scheme.lean:3381); returning it is what the planted-entry corollary needs, via
  `IWorldHist`'s (H3) clause `(⟨.neg, obl c, c⟩ : ISF Atom) ∈ b` (Scheme.lean:3272).

**Planning-time correction to the research skeleton (adopt this, not the report's version).**
Report §4 proposes `Relation.ReflTransGen.head_induction_on`. Plain `induction hle` is the
better first attempt: `ReflTransGen`'s own recursor peels from the RIGHT (`tail`), which matches
the goal shape directly. In the `tail` case the hypotheses are
`hchain : ReflTransGen R w y`, `hstep : isAccessible rawEdges y w' = true`, and
`ih : intExtractValuation b w p → intExtractValuation b y p`; the goal
`intExtractValuation b w' p` then follows by feeding `ih hval` into one `IPosPersistRaw` step at
`hstep`. `head_induction_on` remains the documented fallback if the `LE.le`-to-`ReflTransGen`
unfolding does not unify cleanly.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and `roadmap_flag` was not set; this
plan adds no roadmap-review or roadmap-update phases and does not read or write ROADMAP.md.

## Goals & Non-Goals

**Goals**:
- Add a standalone, sorry-free lemma in Scheme.lean proving upward closure of
  `intExtractValuation b` along `intAccessPreorder rawEdges` for any `b` arising from an
  `intExpandBranches ... = .openBranch b` run.
- Close the `b.any (fun sf => sf.label == w') = true` plumbing gap with two private corollaries
  and one additional export conjunct, following the in-file `ForestComparable` pattern.
- Keep the change additive: no existing statement weakened, no existing sorry touched.

**Non-Goals**:
- Conjunct 2 (`¬ IForces ...`) — successor task.
- Editing or discharging `openBranch_countermodel`'s own `sorry` at Scheme.lean:7965. Its
  `edges` binding is the augmented `augSets` witness that conjunct 2's `truthLemma` call already
  needs and cannot be swapped to `rawEdges` here.
- The maximal atom-set-inclusion frame `⊑`. Explicitly ruled out by the delegation and by task
  591's probe evidence; do not re-derive or re-propose it, even restricted to conjunct 1.
- A from-scratch `inclEdges b : IEdges` definition.
- Fixing `intFImpReuseWitnessAnc?` in `Expansion.lean`. Outside `file_scope`.
- Any edit outside `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Widening `intExpandBranches_openBranch_sat`'s existential breaks arms of the 10-case induction beyond the single tuple-construction site | H | M | The conclusion shape occurs at exactly three places (6843-6844 outer, 6882-6883 inner `suffices key`, 7059-7060 witness); the other nine cases only reapply `ih`. Phase 4 is `atomic-batch` and confirms the site count by grep before editing |
| `ReflTransGen` induction does not unify because `hle` is stated as `@LE.le Nat (intAccessPreorder edges).toLE` | M | M | `intAccessPreorder` is `@[reducible]`; re-bind via `have hle' : Relation.ReflTransGen (fun x y => isAccessible rawEdges x y = true) w w' := hle` before inducting. Fallback: `Relation.ReflTransGen.head_induction_on`, then `trans_induction_on` |
| `intExtractValuation` (a coerced `List.any`) to `∈ b` membership bridge is fiddly in the reverse direction | M | M | Forward direction has an in-file precedent at Scheme.lean:7911-7913. Reverse: `List.any_eq_true.mp` then `cases sf` + `simp` on the three `beq` field equalities. Prove the bridge as a local `have` inside Phase 5 rather than as a new exported lemma |
| Strengthening `edges_shape_of_worldHist` breaks an unnoticed second caller | M | L | Phase 2 greps for all callers first (Scope Hypothesis); if more than one exists, add a separate corollary lemma instead of strengthening in place |
| Full `lake build` of an 8018-line file is slow, making tight iteration expensive | M | H | Use `lean_diagnostic_messages` / `lean_goal` via lean-lsp for per-edit feedback; reserve full `lake build` for phase-closing verification and the Phase 6 gate |
| The planted-entry fact is derived for `bh` but the exported branch is `bPers` | M | M | Derive membership-shaped `(⟨.neg, obl c, c⟩ : ISF Atom) ∈ bh`, then transport with the `hmemP : ∀ x ∈ bh, x ∈ bPers` already in scope at Scheme.lean:7048 before converting to the `any` form |
| Accidental new sorry or axiom | H | L | Phase 6 runs `grep -nw sorry` on the file (expect exactly the two pre-existing hits at 768 and 7965) and `#print axioms` / `lean_verify` on every new declaration |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 3 |
| 4 | 5 | 1, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Structural `isAccessible` target-membership lemma [COMPLETED]

**Goal**: Prove, with no invariant hypotheses at all, that a non-reflexive `isAccessible`
success means the target is a child endpoint of some edge.

**Tasks**:
- [ ] Add a private lemma near the existing `parAncestor_of_isAccessible`
      (Scheme.lean:3384-3434), e.g.
      `private lemma isAccessible_target_mem_edges {edges : IEdges} {w w' : Nat}
        (h : isAccessible edges w w' = true) (hne : ¬ (w = w')) : ∃ p, (w', p) ∈ edges`
- [ ] Prove it by mirroring `parAncestor_of_isAccessible`'s DFS induction: `simp only
      [isAccessible]`, case on `w == w'`, then the `suffices key : ∀ current fuel,
      isAccessible.go edges w' current fuel = true → current = w' ∨ ∃ p, (w', p) ∈ edges`
      pattern with `induction fuel generalizing current`
- [ ] Add `omit [DecidableEq Atom] [Hashable Atom] in` if the lemma uses neither instance,
      matching the surrounding declarations
- [ ] Write a docstring in the file's established style, naming this as the structural half
      (no `IWorldHist` needed) of the `IPosPersistRaw` side-condition gap

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Verification**:
- `lean_diagnostic_messages` on Scheme.lean reports no new errors at the insertion point
- The new lemma elaborates with no `sorry` (confirm via `lean_goal` showing no goals)

---

### Phase 2: Strengthen `edges_shape_of_worldHist` to return the world bound [COMPLETED]

**Goal**: Make `edges_shape_of_worldHist` return the `1 ≤ c ∧ c < nw` bound it already computes
and discards, so the planted-entry corollary can invoke `IWorldHist`'s (H3) clause.

**Tasks**:
- [ ] `grep -n "edges_shape_of_worldHist"` across `Cslib/` to enumerate all callers before
      editing
- [ ] Change the conclusion at Scheme.lean:3358-3360 to
      `∀ p ∈ edges, ∃ c, 1 ≤ c ∧ c < nw ∧ p = (c, par c)`
- [ ] Replace the discarding pattern at Scheme.lean:3381 (`obtain ⟨c, ⟨_hc1, _hc2⟩, hceq⟩`) so
      the bound is returned rather than dropped
- [ ] Adapt each enumerated caller (known: `IWorldHist_forestComparable`'s `hshape` at
      Scheme.lean:3501-3502) with a one-line projection back to the old shape
- [ ] Update the lemma docstring to state the bound is now part of the conclusion

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: `edges_shape_of_worldHist` is asserted to have exactly one caller
(`IWorldHist_forestComparable`, Scheme.lean:3501-3502). Confirm at implementation time with
`grep -rn "edges_shape_of_worldHist" --include=*.lean Cslib/`. If more than one caller exists,
do NOT strengthen in place — add a sibling corollary
`edges_shape_bound_of_worldHist` with the strengthened conclusion and leave the original
untouched, then record the deviation in the phase notes.

**Verification**:
- `lean_diagnostic_messages` reports no errors in the 3355-3520 range
- `IWorldHist_forestComparable` still elaborates unchanged in statement

---

### Phase 3: `IWorldsPlanted` predicate and its `IWorldHist` corollary [COMPLETED]

**Goal**: Export "every edge-list child has a branch entry" as a predicate plus a corollary
derived purely from `IWorldHist` + `IWorldHistCounter`, mirroring `IWorldHist_forestComparable`.

**Tasks**:
- [ ] Add the predicate alongside `ForestComparable` (near Scheme.lean:3485):
      `private def IWorldsPlanted (edges : IEdges) (b : IBranch Atom) : Prop :=
        ∀ c p : Nat, (c, p) ∈ edges → b.any (fun sf => sf.label == c) = true`
- [ ] Add a monotonicity lemma `IWorldsPlanted_mono : (∀ x ∈ b, x ∈ b') → IWorldsPlanted edges b
      → IWorldsPlanted edges b'` (one `List.any_eq_true` round trip)
- [ ] Add the corollary
      `private lemma IWorldHist_worldsPlanted (hWH : IWorldHist φ0 b e nw edges)
        (hWHC : IWorldHistCounter nw edges) : IWorldsPlanted edges b`, proved by destructuring
      `hWH`, applying the Phase 2 strengthened shape lemma to get `1 ≤ c < nw` and `p = (c, par c)`,
      then projecting `IWorldHist`'s (H3) membership `(⟨.neg, obl c, c⟩ : ISF Atom) ∈ b` and
      converting to the `any` form via `List.any_eq_true.mpr`
- [ ] Write docstrings naming this as the provenance half of the gap and citing the
      `ForestComparable` precedent

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Verification**:
- Both new declarations elaborate with no errors and no `sorry`
- `IWorldHist_worldsPlanted` takes exactly the same two hypotheses as
  `IWorldHist_forestComparable` (so it can be computed at the same exit site in Phase 4)

---

### Phase 4: Widen `intExpandBranches_openBranch_sat`'s existential [COMPLETED]

**Goal**: Add `IWorldsPlanted rawEdges b` as a sixth conjunct to the sat lemma's conclusion and
discharge it at the existing induction exit site.

**Tasks**:
- [ ] `grep -n "ForestComparable nwF rawEdges"` to confirm the conclusion-shape site count
      before editing
- [ ] Extend the outer conclusion (Scheme.lean:6843-6844) with `∧ IWorldsPlanted rawEdges b`
- [ ] Extend the inner `suffices key ... from` conclusion identically (Scheme.lean:6882-6883)
- [ ] At the exit site (Scheme.lean:7058-7060), compute
      `have hwp : IWorldsPlanted edgesH bPers := IWorldsPlanted_mono hmemP
        (IWorldHist_worldsPlanted hWH_head hWHC_head)` immediately after the existing `hfc`, and
      add it as the sixth component of the returned anonymous constructor
- [ ] Update `openBranch_countermodel`'s destructuring (Scheme.lean:7914) from the 9-component
      pattern to 10, binding the new conjunct as `_hwp` (unused there — conjunct 1 in that
      lemma stays `sorry`)
- [ ] Confirm no other declaration in the repository destructures this lemma's result

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: atomic-batch

**Scope Hypothesis**: Exactly four edit sites are asserted — Scheme.lean:6843-6844 (outer
statement), 6882-6883 (inner `suffices key`), 7059-7060 (the single
`exact ⟨augH, edgesH, lbH, nwH, ...⟩` witness), and 7914 (`openBranch_countermodel`'s
`obtain`) — and `intExpandBranches_openBranch_sat` is asserted to have exactly one caller
(`openBranch_countermodel`). Confirm at implementation time with
`grep -n "ForestComparable nwF rawEdges" Cslib/.../Scheme.lean`,
`grep -n "augH, edgesH, lbH, nwH" Cslib/.../Scheme.lean`, and
`grep -rn "intExpandBranches_openBranch_sat" --include=*.lean Cslib/` (filtering prose
mentions in docstrings from real call sites). Any additional site found is added to the batch,
not deferred.

**Rationale for `atomic-batch`**: editing the statement without the witness (or vice versa)
leaves Scheme.lean red by construction, so per-substep commits are not achievable inside this
phase. The declared file set is the single file `Scheme.lean`; the batch closes on one green
build.

**Verification**:
- `lean_diagnostic_messages` on Scheme.lean reports no errors other than the two pre-existing
  `declaration uses sorry` warnings
- `openBranch_countermodel` still elaborates with its statement byte-identical to before

---

### Phase 5: The target lemma `openBranch_rawEdges_upward_closed` [COMPLETED]

**Goal**: State and prove the standalone conjunct-1 lemma over `rawEdges`, sorry-free.

**Tasks**:
- [ ] Add the lemma immediately after `openBranch_countermodel` (after Scheme.lean:7965), with
      a docstring stating: what it proves, that `edges := rawEdges` is the uniform construction,
      that conjunct 2 is deliberately not addressed, and that it is decoupled from
      `openBranch_countermodel`'s own `sorry` because that lemma's `edges` binding must
      simultaneously serve conjunct 2
- [ ] Statement:
      `lemma openBranch_rawEdges_upward_closed (S : IntMinScheme Atom) (φ : Proposition Atom)
        (b : IBranch Atom) (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] [intFuelExt φ]
        S.closurePred = .openBranch b) : ∃ edges : IEdges, ∀ {w w' : Nat} (p : Atom),
        @LE.le Nat (intAccessPreorder edges).toLE w w' →
        intExtractValuation b w p → intExtractValuation b w' p`
- [ ] Reuse `openBranch_countermodel`'s `obtain` block verbatim (Scheme.lean:7914-7946),
      widened by the Phase 4 conjunct, keeping `rawEdges`, `hpp` (`IPosPersistRaw`) and `hwp`
      (`IWorldsPlanted`) and discarding the rest
- [ ] `refine ⟨rawEdges, ?_⟩`; `intro w w' p hle hval`
- [ ] Re-bind `hle` to its `Relation.ReflTransGen` form, then `induction hle` (tail-peeling):
      `refl` closes by `hval`; `tail hchain hstep ih` case-splits on `y = w'` (trivial transfer)
      versus `y ≠ w'` (apply Phase 1's lemma to `hstep` to get `(w', p') ∈ rawEdges`, feed to
      `hwp` for the `b.any (label == w')` side condition, then one `hpp (.atom p) y w' hstep`
      step on `ih hval`)
- [ ] Prove the two `intExtractValuation`-to-membership bridge directions as local `have`s
      (forward: `List.any_eq_true.mpr`; reverse: `List.any_eq_true.mp` then `cases sf` + `simp`)
- [ ] Do not modify `openBranch_countermodel`'s `sorry` or its surrounding comment block

**Timing**: 2 hours

**Depends on**: 1, 4

**Verification Tier**: local

**Verification**:
- `lean_goal` at the end of the proof reports "no goals"
- `lean_diagnostic_messages` shows no `declaration uses sorry` warning attached to the new lemma
- The `sorry` at Scheme.lean:7965 is still present and unchanged

---

### Phase 6: Full gate, sorry/axiom audit, and standards compliance [COMPLETED]

**Goal**: Prove the whole change is green, additive, and debt-free.

**Tasks**:
- [ ] Run the full `lake build` for the Cslib target; require zero errors
- [ ] `grep -nw sorry Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — expect
      exactly the two pre-existing proof-term hits (lines 768 and 7965, modulo line drift from
      the additions); prose mentions of the word inside docstrings are not sorries
- [ ] Run `lean_verify` (or `#print axioms`) on `openBranch_rawEdges_upward_closed`,
      `isAccessible_target_mem_edges`, `IWorldHist_worldsPlanted`, and `IWorldsPlanted_mono` —
      require only the standard three axioms, no `sorryAx`
- [ ] Confirm `git diff --stat` touches exactly one file:
      `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- [ ] Confirm every new declaration has a docstring and follows the file's `private` /
      `omit [DecidableEq Atom] [Hashable Atom] in` conventions
- [ ] Confirm no new declaration cites a task number (deliverable files outside `specs/**` must
      reference durable anchors — lemma names, section headings — not task numbers)

**Timing**: 45 minutes

**Depends on**: 5

**Verification Tier**: full

**Verification**:
- Full `lake build` exits 0
- Sorry count in Scheme.lean unchanged at 2 proof-term occurrences
- No `sorryAx` in the axiom list of any new declaration
- Diff confined to one file

---

## Testing & Validation

- [x] Full `lake build` green with zero errors
- [x] `openBranch_rawEdges_upward_closed` elaborates with no goals remaining and no `sorry`
- [x] `#print axioms openBranch_rawEdges_upward_closed` shows no `sorryAx` (via `lean_verify`:
      `propext`, `Classical.choice`, `Quot.sound` only)
- [x] `openBranch_countermodel`'s statement is byte-identical to its pre-change form, and its
      `sorry` remains in place (only its internal `obtain` pattern grew one `_hwp` binder to
      match the widened `intExpandBranches_openBranch_sat` existential; verified via `git diff`)
- [x] Pre-existing sorries unchanged in count and semantics (now at Scheme.lean:768,
      Scheme.lean:8051 -- same two declarations, `truthLemma` and `openBranch_countermodel`,
      shifted by the additions above them)
- [x] `git diff --name-only -- Cslib/` lists only
      `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- [x] No new axioms (`grep -c "^axiom "` = 0), no new `Expansion.lean` / `Soundness.lean` /
      `Rules.lean` edits

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — five new private
  declarations (`isAccessible_target_mem_edges`, `IWorldsPlanted`, `IWorldsPlanted_mono`,
  `IWorldHist_worldsPlanted`), one strengthened private lemma (`edges_shape_of_worldHist`), one
  widened private export (`intExpandBranches_openBranch_sat`), and one new public lemma
  (`openBranch_rawEdges_upward_closed`)
- `specs/603_construct_uniform_frame_for_openbranch_countermodel/summaries/01_rawedges-upward-closure-summary.md`
- `specs/603_construct_uniform_frame_for_openbranch_countermodel/.orchestrator-handoff.json`
  (updated per implement dispatch)

## Rollback/Contingency

All changes are additive to a single file. To revert: `git revert` the task's phase commits, or
drop the new declarations and restore the three widened-conclusion sites plus
`edges_shape_of_worldHist`'s original conclusion. No other file, no existing statement, and no
existing `sorry` is modified, so a rollback cannot regress any currently-green proof.

Contingency if Phase 5's `ReflTransGen` induction resists: fall back to
`Relation.ReflTransGen.head_induction_on`, then `Relation.ReflTransGen.trans_induction_on`. If
all three resist, prove an intermediate helper
`∀ w w', ReflTransGen (isAccessible rawEdges · · = true) w w' → (∀ χ, ⟨.pos, χ, w⟩ ∈ b →
⟨.pos, χ, w'⟩ ∈ b)` at membership level first (avoiding the `intExtractValuation` coercion
inside the induction motive), and specialize afterwards. Do NOT introduce a `sorry` to close
the phase — mark the phase `[PARTIAL]` and hand off instead.
