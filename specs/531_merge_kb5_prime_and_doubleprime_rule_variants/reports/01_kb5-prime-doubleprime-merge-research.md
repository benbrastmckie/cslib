# Research Report: Merge KB5 Prime and Double-Prime Rule Variants

**Task:** 531 — Redundancy cleanup of the two KB5 tableau propagation-rule families in
`Cslib/Logics/Modal/Tableau/`.
**Status:** researched
**Ground-truth build:** `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` → green
(880 jobs, sorry-free; only pre-existing non-blocking `linter.flexible` info/warnings).
**Ground-truth axioms:** `kb5Valid_decides` (the public decision capstone) uses only
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, or `axiom`
declarations exist in any of the four in-scope files.

---

## 1. Executive Summary / Merge Verdict

**The merge is feasible, low-risk, and strictly easier than the task framing assumed.**

The two rule families differ in exactly **one boolean conjunct**. Everything else is
declaration-for-declaration parallel duplication. Critically:

- The **double-prime / `Univ` family** (corrected gate) is the *sole* support of the public
  API: `modalTableauKb5''_complete`, `modalTableauKb5''_sound`, `kb5Valid_decides`, and
  `instDecidableKb5Valid` all route through it and nothing else. It is fully self-contained.
- The **prime / `Full` family** (shallow root-only repair) is a **self-contained dead branch**:
  it compiles and is sorry-free, but *none* of its results are consumed by any downstream
  public theorem. Its entire proof chain terminates at the trophy capstone
  `modalTableauKb5'_sound`, which is referenced by **zero** proof bodies (only docstrings).

Therefore the "merge" reduces to: **confirm the single `Univ` rule discharges every live
obligation (it already does), then retire the redundant `Full`/prime declarations.** No
downstream re-proof is required. Zero-debt and axiom-cleanliness are preserved trivially because
retirement is pure deletion plus (optionally) one trivial corollary.

> **Refinement of the task premise.** The task states "both are currently load-bearing
> (referenced by live soundness/completeness theorems)". Precisely: the *double-prime* family is
> load-bearing for the public decision procedure; the *prime* family is "live" only in the sense
> that it compiles as a standalone parallel proof. Its outputs feed nothing but its own capstone.
> This makes the retirement safe — there is no obligation the merged rule must newly discharge.

---

## 2. The Exact Semantic Difference (the crux)

Both rules are structurally identical `RuleApply` functions. Reading
`modalApplyOneKb5'` (FiveSimplification.lean:1937) against `modalApplyOneKb5''` (2483): the mint
(existential) arms — `.pos .diamond` and `.neg .box` — are **byte-for-byte identical** (both
reuse `witnessWorldFive`, fresh K-mint fallthrough). The only divergence is which propagation
helper the two `Prop` siblings call:

| | Prime family (`Full`) | Double-prime family (`Univ`) |
|---|---|---|
| `RuleApply` | `modalApplyOneKb5'` (1937) | `modalApplyOneKb5''` (2483) |
| `Prop` sibling | `modalApplyOneKb5'Prop` (1759) | `modalApplyOneKb5''Prop` (2440) |
| box-pos target fn | `modalKb5BoxAllFull` (1539) | `modalKb5BoxAllUniv` (2180) |
| dia-neg target fn | `modalKb5DiaNegAllFull` (1556) | `modalKb5DiaNegAllUniv` (2198) |

The **only** functional difference between `Full` and `Univ` is the self-target (`w' = 0`) gate:

```
Full (1548):  if w == 0 && (cluster has a non-root member) then  ...emit ⟨sign,φ,0⟩
Univ (2189):  if           (cluster has a non-root member) then  ...emit ⟨sign,φ,0⟩
```

`Univ` **drops the `w == 0` conjunct**. Because the trigger `w` is then unused, `Univ`'s
signature is `(… (_w : WorldIndex))` — which is exactly why task 529 applied
`@[nolint unusedArguments]` to `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`. Consequently
`Univ b φ w ⊇ Full b φ w` for every trigger (equal when `w = 0`; a strict superset with the
`⟨sign,φ,0⟩` self-target when `w ≠ 0` and the cluster is non-root-nonempty).

**Why the gate change matters (documented in-code):** `modalTruthLemmaKb5` is *mathematically
false* for `Full`'s 0-target arm — the counterexample is `extractModelKb5_nonRoot_boxPos_gap`
(FrameCompleteness.lean:4374) at `φ₀ = ¬◇◇□p`. `extractModelKb5`'s forced relation is the total
cluster on the connected edge-touched world set, so the self-target must fire regardless of which
world triggered the rule. `Univ` is the corrected, complete rule; `Full` remains provably
incomplete.

---

## 3. Declaration Inventory and Reference Counts

Raw string counts (occurrences, includes split-lemma names and docstrings):
`modalApplyOneKb5''` = 390; `modalApplyOneKb5'` (excluding double) = 332. Per file:

| File | `Kb5''` occ. | `Kb5'` (excl. double) occ. |
|---|---|---|
| FiveSimplification.lean | 267 | 272 |
| FrameCompleteness.lean | 74 | 20 |
| FrameSoundness.lean | 35 | 38 |
| S5Simplification.lean | 1 | 2 (docstring only) |

### 3a. PRIME / `Full` family — retirement candidates (all consumed only within the prime branch)

**FiveSimplification.lean**
- Target fns: `modalKb5BoxAllFull` (1539), `modalKb5DiaNegAllFull` (1556)
- `Full` membership lemmas: `modalKb5BoxAllFull_mem` (1577), `modalKb5DiaNegAllFull_mem` (1645),
  `_mem_known` (1715, 1725), `_mem_eq` (1736, 1746)
- Prop sibling `modalApplyOneKb5'Prop` (1759) + `_eq_of_not_boxPos_diaNeg` (1787),
  `_boxPos_diaNeg_eq` (1801), `_knownWorlds_step` (1902), `_snd_eq` (3376), `_eq_of_linear`
  (3388), `_fresh_local_local` (3405), `_boxPos_diaNeg_shape` (3479)
- Rule `modalApplyOneKb5'` (1937) + split-lemma pairs: `_diaPos_eq_or_reuse` (1955),
  `_boxNeg_eq_or_reuse` (1975), `_boxPos_eq` (1995), `_diaNeg_eq` (2004),
  `_eq_of_not_mint_shape` (2014), `_diaPos_eq_or_reuse_ne_root` (2029),
  `_boxNeg_eq_or_reuse_ne_root` (2050), `_agree_or_reuse_ne_root` (2072), `_agree_or_reuse`
  (2098), `_fresh_local` (3417), `_boxPosNotExpanding` (3519), `_diaNegNotExpanding` (3529),
  `_localShapeInvariance` (3539), `_branchingLength` (3551), `_persistentFresh` (3585),
  `_outputsSubsetUniverse` (3686), `_diaPosWitness'` (3833), `_boxNegWitness'` (3853),
  `_specCore` (3874)
- Driver: `modalStepBranchKb5'` (2121), `modalExpandBranchesKb5'` (2129), `modalTableauKb5'`
  (2137), + `_eq` theorems (2141, 2147, 2154)
- Termination aliases (dead, `:= FiveWorldInv`): `Kb5'WorldInv` (4751), `Kb5'WorldInv_eq`
  (4759), `modalMaxWorld_lt_worldBound_of_Kb5'WorldInv` (4768) — verified consumed by nothing.

**FrameSoundness.lean** (the prime soundness sub-chain — dead-ends at `modalTableauKb5'_sound`)
- `modalKb5BoxAllFull_soundIn` (3136), `modalKb5DiaNegAllFull_soundIn` (3196)
- `modalStepBranchKb5'_preserves_accReachableInv` (3437)
- `modalStepBranchKb5'_preserves_satIn` (4384)
- `modalExpandBranchesKb5'_closed_unsatIn` (5472)
- `modalTableauKb5'_sound` (5810) ← **trophy capstone, consumed by nothing**

**FrameCompleteness.lean** (the prime completeness cluster — consumed by nothing but docstrings)
- `modalKb5BoxAllFull_mem_of` (3357), `modalKb5DiaNegAllFull_mem_of` (3394)
- `hintikkaKb5'_box_pos` (3436), `hintikkaKb5'_diamond_neg` (3478)
- Documentation counterexample cluster (private): `extractModelKb5_root_reach_scout` (4343),
  `extractModelKb5_nonRoot_boxPos_gap` (4374) — these only *demonstrate* `Full`'s incompleteness;
  they have no referent once `Full` is gone.

### 3b. DOUBLE-PRIME / `Univ` family — KEEP (sole support of public API)

**FiveSimplification.lean**: `modalKb5BoxAllUniv` (2180), `modalKb5DiaNegAllUniv` (2198) + their
`_mem`/`_mem_eq`/`_mem_of` lemmas (2219, 2284, 2349, 2359, 2372, 2405), `modalApplyOneKb5''Prop`
(2440) + lemmas, `modalApplyOneKb5''` (2483) + all `''` split lemmas, `modalStepBranchKb5''`
(2666)/`modalExpandBranchesKb5''` (2674)/`modalTableauKb5''` (2682) + `_eq`, the `''` worldInv +
worldGrowth + preserves_worldInv machinery (4787–5019).

**FrameSoundness.lean**: `modalKb5BoxAllUniv_soundIn` (3288)/`modalKb5DiaNegAllUniv_soundIn`
(3354), `modalStepBranchKb5''_preserves_accReachableInv` (3534),
`modalStepBranchKb5''_preserves_satIn` (4930), `Kb5''SoundInv` (5635),
`modalExpandBranchesKb5''_closed_unsatIn` (5648), `modalTableauKb5''_sound` (5844).

**FrameCompleteness.lean**: `hintikkaKb5''_box_pos` (3535)/`hintikkaKb5''_diamond_neg` (3577),
`modalApplyOneKb5''_eq_of_prop_shape` (3635), `modalApplyOneKb5''_edge_target_ne_root` (4027),
the `modalStepBranchKb5''_preserves_*` theorems (4047, 4080), `modalExpandBranchesKb5''_*`
(4103), `ModalLoopAuxKb5''` (4143) + bounds/stepPreserved, `modalLoopInvHintikkaKb5''_initial`
(4176), `modalOpenBranchKb5''_countermodel` (4212), `modalTableauKb5''_complete` (4231),
`kb5Valid_decides` (4306), `instDecidableKb5Valid` (4316).

---

## 4. Dependency Graph (verified by body-level grep, not just names)

```
PUBLIC API (KEEP):
  instDecidableKb5Valid (FC 4316)
    └─ kb5Valid_decides (FC 4306) = ⟨modalTableauKb5''_sound, modalTableauKb5''_complete⟩
         ├─ modalTableauKb5''_sound (FS 5844)
         │    └─ modalExpandBranchesKb5''_closed_unsatIn (FS 5648)
         │         ├─ modalStepBranchKb5''_preserves_accReachableInv (FS 3534)
         │         └─ modalStepBranchKb5''_preserves_satIn (FS 4930)
         │              └─ modalKb5BoxAllUniv_soundIn / DiaNeg (FS 3288/3354)  [self-contained]
         └─ modalTableauKb5''_complete (FC 4231)
              └─ modalTruthLemmaKb5 (FC 3688)
                   └─ hintikkaKb5''_box_pos / _diamond_neg (FC 3535/3577)
                        └─ modalKb5BoxAllUniv_mem_of / DiaNeg (Five 2372/2405)  [self-contained]

PRIME BRANCH (RETIRE) — consumed by NOTHING downstream:
  modalTableauKb5'_sound (FS 5810)   ← referenced only in docstrings
    └─ modalExpandBranchesKb5'_closed_unsatIn (FS 5472)   [used only @5825, inside the capstone]
         ├─ modalStepBranchKb5'_preserves_accReachableInv (FS 3437)  [used only @5575]
         └─ modalStepBranchKb5'_preserves_satIn (FS 4384)            [used only @5618]
              └─ modalKb5BoxAllFull_soundIn / DiaNeg (FS 3136/3196)  [used only @4431/4473]
  hintikkaKb5'_box_pos / _diamond_neg (FC 3436/3478)   ← referenced only in docstrings
       └─ modalKb5BoxAllFull_mem_of / DiaNeg (FC 3357/3394)   [used only inside hintikkaKb5']
  extractModelKb5_nonRoot_boxPos_gap (FC 4374)   ← private, referenced only in docstrings
       └─ extractModelKb5_root_reach_scout (FC 4343)   [used only @4383, inside the gap lemma]
```

**Verified negatives (the entanglement that would have blocked a clean retirement — all absent):**
- `modalKb5BoxAllUniv_soundIn` (Univ, load-bearing) does **not** call `modalKb5BoxAllFull_soundIn`
  in its body (docstring mentions it; grep of body lines 3288–3436 for `Full` = empty).
- `modalTruthLemmaKb5` / `hintikkaKb5''` use **only** the `Univ` intro lemmas, never `Full`'s.
- No `Univ`/public declaration consumes any `Kb5'`/`Full` symbol in a proof body.
- The prime `Kb5'WorldInv`/`modalMaxWorld_lt_worldBound_of_Kb5'WorldInv` aliases are consumed by
  nothing (the double chain uses the `Kb5''` versions).

---

## 5. Recommended Merge Strategy (sorry-free, axiom-clean)

**Approach: "Univ-as-canonical" consolidation.** The single surviving rule is the corrected-gate
`Univ` rule. Two ordered phases.

### Phase A — Confirm the merged rule discharges every obligation (the "merge" proof step)
The `Univ` rule already is the sole basis of `instDecidableKb5Valid`/`kb5Valid_decides`/
`modalTableauKb5''_complete`/`modalTableauKb5''_sound`. Nothing downstream requires `Full`.
The only prime result not reproduced by the `Univ` capstone is `modalTableauKb5'_sound`
(soundness of the *Full-gate* tableau). Decide its fate:
- **Option A1 (recommended): retire it.** It is a trophy consumed by nothing; the canonical KB5
  soundness statement is `modalTableauKb5''_sound`. This is exactly the "retiring the redundant
  lemma pairs" the task sanctions.
- **Option A2 (only if an external caller of the prime name must be preserved — none found
  in-repo): thin alias.** Redefine `modalApplyOneKb5' := modalApplyOneKb5''` and restate
  `modalTableauKb5'_sound := modalTableauKb5''_sound`. **Caveat:** this makes `Full` complete,
  which *contradicts* `extractModelKb5_nonRoot_boxPos_gap` (proves `Full` incomplete); that
  counterexample lemma and its docstrings must then be deleted. A2 is strictly more work than A1
  for no downstream benefit — prefer A1.

This honors "NOT a delete of the prime variant": the plan first *proves* the merged rule covers
every live obligation, rather than blindly `git rm`-ing the prime rule and discovering dangling
references or a lost soundness result.

### Phase B — Retire the redundant `Full`/prime declarations
Delete the Section 3a inventory across all three code files. The counterexample documentation
cluster (`extractModelKb5_root_reach_scout` + `_nonRoot_boxPos_gap`) explains *why* the gate
correction was needed — durable value — but as executable lemmas *about* `modalKb5BoxAllFull` it
cannot survive `Full`'s deletion; relocate its mathematical content into a `Univ` module
docstring (durable anchor) rather than keeping it as dead code. Update the many cross-referencing
docstrings in all four files (including `S5Simplification.lean:2057–2062`, docstring-only) that
name the prime symbols.

### Naming decision — OPEN, for the planner
Whether to rename the surviving `Univ` rule `modalApplyOneKb5''` → a suffix-free canonical name.
Note the unprimed `modalApplyOneKb5` is **already taken** by the sound-but-incomplete Five-alias
(`modalApplyOneKb5 := modalApplyOneFive`, Five 1451), which `modalTableauKb5_sound` (FS 5902)
consumes via frame-class monotonicity. A full rename to the unprimed name is therefore a larger,
riskier change touching `modalTableauKb5_eq_modalTableauFive` and `modalTableauKb5_sound`.
Recommendation: keep the `Univ` rule under a stable name; at most perform a mechanical
`''` → `'` rename *after* `Full` is deleted (freeing the prime names). Renaming is optional churn;
the substance of the task is `Full`-branch retirement, not renaming.

### Zero-debt / axiom posture
Retirement is pure deletion (+ at most one trivial `:= modalTableauKb5''_sound` corollary under
A2). No new goal states arise that could require `sorry`. The public API already verifies against
only `propext`/`Classical.choice`/`Quot.sound`; deleting dead declarations cannot introduce
axioms. No `native_decide` is used or introduced.

---

## 6. Sequencing Constraint (MUST flag to planner/implementer)

A concurrent sibling cleanup task is making **docstring-only** edits to
`FrameCompleteness.lean` (~lines 476 and 552) and to `GenericDriver.lean`. Read-only research
here is unaffected. **The merge implementation must be sequenced AFTER that docstring task lands.**
This merge substantially rewrites `FrameCompleteness.lean` (deleting the prime completeness
cluster at 3357–3478 and the counterexample cluster at 4343–4430, plus many docstring updates),
so concurrent edits to the same file will conflict. Gate the implementation on that task's
completion (or coordinate a rebase) before touching `FrameCompleteness.lean`.

---

## 7. Verification Checklist for Post-Merge (acceptance criteria)

1. `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` green, sorry-free.
2. `lake build Cslib.Logics.Modal.Tableau.S5Simplification` green (it references the KB5 public
   names in docstrings only, but rebuild to catch stale references).
3. `lean_verify` on `Cslib.Logic.Modal.Tableau.kb5Valid_decides` → axioms exactly
   `[propext, Classical.choice, Quot.sound]` (baseline captured this run — must be unchanged).
4. `instDecidableKb5Valid` and `modalTableauKb5''_complete` still present and used.
5. Grep confirms zero remaining references to any retired prime symbol (Section 3a) across
   `Cslib/` — including docstrings.
6. No new `@[nolint …]`, `sorry`, `admit`, `axiom`, or `native_decide` introduced.

---

## 8. Tactic / Reuse Notes

- No Mathlib search was warranted: this is an internal-refactor task, not a new-lemma task. The
  reuse-first check confirms the keeper (`Univ`) rule and all its supporting lemmas already
  exist; the merge *removes* duplication rather than adding abstractions.
- Relevant existing foundations the `Univ` rule already leans on (do not re-derive):
  `Relation.symm_rightEuclidean_root_refl`, `Relation.rooted_cluster_isEquiv`,
  `Relation.rooted_mem_cod`, `Relation.EuclGen`/`SymmGen` (Euclidean/closure lemmas), and
  `witnessWorldFive`. These are untouched by the merge.
