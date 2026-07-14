# Implementation Plan: CS4 Completeness Integration

- **Task**: 508 - unblock_CK_CS4_CS5_completeness
- **Status**: [NOT STARTED]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: `specs/508_unblock_CK_CS4_CS5_completeness/reports/01_cs4-cs5-completeness-technique.md`
- **Artifacts**: plans/01_cs4-completeness-integration.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, `.claude/rules/cslib.md`, CONTRIBUTING.md, NOTATION.md, ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Lift the fully verified CS4 soundness+completeness development from
`probes/cs4-completeness-verified.lean` into
`Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean`, placing the weakened frame condition
`cs4FC'` beside `cs4FC` in `CKExtension.lean`. **The mathematics is settled**: the probe compiles
sorry-free with `#print axioms` reporting exactly `[propext, Classical.choice, Quot.sound]`. This
is a transcription + integration task, not a proof-discovery task. CS5 completeness is explicitly
**out of scope** and remains blocked; its blocking comment is re-grounded on the newly mechanized
`bDia` obstruction. Definition of done: `cs4_soundness_completeness` lives in CS4.lean, the full
CSLib CI pipeline is green, and no downstream user of `cs4FC` is broken.

### Research Integration

Key findings integrated:

- **Two required changes** (research §3): weaken `cs4FC` to `cs4FC'` (still validates
  `fourBox`/`fourDia`), and replace `diamRefutingSegment`'s one-step `A`-exclusion with a
  hereditary `◇A`-exclusion. `dia_refuting_theory` is reused **unchanged** at `A := ◇A₀`.
- **`cs4_not_dia_dia`** (`◇A ∉ H → ◇◇A ∉ H`, via `fourDia` contraposition) is the hereditary step
  that makes the construction propagate.
- **`cs4_boxInv_trans`** is the workhorse discharging the `boxInv` obligation in both non-trivial
  FC conjuncts.
- **No new foundational abstraction is needed** (research §6): `CKExtension.lean`'s
  `ckvalidFC_completeness` is already abstract over `World`. `CT.lean`, `CK.lean`, `Segment.lean`,
  `SegmentLindenbaum.lean`, `CKTruthLemma.lean` are untouched.
- **Import closure is already sufficient**: the probe compiles with only
  `import Cslib.Logics.Modal.Metalogic.Constructive.CS4`, so every name it uses
  (`dia_refuting_theory`, `box_refuting_theory`, `imp_refuting_theory`,
  `quasi_head_realization`, `ckvalidFC_completeness`, `mem_of_bot_mem`, `cbotForces_*`,
  `cval_upward_closed`, `quasiPrime_univ`, `boxInv`, `Preorder.lift`) already resolves from
  CS4.lean's existing import of `CKExtension`. **No new imports are expected.**
- **CS5 is a mechanized negative result** (research §5.2): `bDia_not_valid_over_cs5FCweak` is a
  two-world `Bool` countermodel showing `◇□p → p` fails over the weakened FC that makes CS4 work.
  CS5 cannot be closed by the CS4 technique.

### Deviation from Research: the `cs4FC` naming decision

Research §7.2 recommends **replacing** `cs4FC` outright, on the stated grounds that
"nothing downstream depends on it" and it is "used only by `cs4_soundness*`".

**This claim is false, and was verified false during planning.** `grep -rn "cs4FC" --include=*.lean`
finds two live downstream users in
`Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeMonotonicity.lean`:

- `cs5FC_implies_cs4FC` (line 72): `cs5FC r → cs4FC r`
- `cs4FC_implies_ctFC` (line 77): `cs4FC r → ctFC r`
- (and `cs5FC_implies_ctFC`, line 82, composing the two)

These form the frame-condition inclusion chain for the constructive modal cube. Replacing `cs4FC`
would break them.

**This plan therefore adopts research option (ii): keep both, and prove `cs4FC → cs4FC'`.**
This was verified during planning — the bridging lemma compiles clean (`lake env lean`, exit 0):

```lean
theorem cs4FC_implies_cs4FC' {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs4FC r) : cs4FC' r :=
  ⟨h.1,
   fun hwu hle hu't => ⟨_, le_refl _, h.2 hwu hle hu't⟩,
   fun hwu => ⟨_, le_refl _, fun _ hut => h.2 hwu (le_refl _) hut⟩⟩
```

This choice is strictly better than replacement: it keeps `ConstructiveLatticeMonotonicity.lean`
**completely untouched** (zero downstream migration), preserves `cs4FC` as a meaningful public
frame class, and — per Phase 4 — lets the existing soundness theorems be *re-derived* as
three-line corollaries rather than duplicated.

### Prior Plan Reference

No prior plan for task 508. Task 501 is the predecessor task whose recorded blocker this work
resolves; its obstruction analysis is confirmed correct but was scoped against `cs4FC` as fixed,
whereas the frame condition is the free parameter (research §2).

### Roadmap Alignment

No roadmap context provided in the delegation context. No ROADMAP.md consultation performed.

## Goals & Non-Goals

**Goals**:

- Add `cs4FC'` and `cs4FC_implies_cs4FC'` to `CKExtension.lean` beside `ctFC`/`cs4FC`/`cs5FC`.
- Transcribe the verified probe's Parts A-G into `CS4.lean`, yielding `cs4_completeness` and
  `cs4_soundness_completeness`, sorry-free and axiom-clean.
- Reconcile the existing soundness section with the probe's soundness section (no blind
  duplication) — see Phase 4.
- Rewrite `CS4.lean`'s module docstring, removing the now-obsolete completeness blocker note.
- Re-ground `CS5.lean`'s blocking comment on the mechanized `bDia` obstruction from this task,
  replacing the task-501 tail-exclusion reasoning, and repair its now-dangling cross-reference
  into `CS4.lean`'s deleted blocker paragraph.
- Pass the full CSLib CI pipeline with zero downstream breakage.

**Non-Goals**:

- **CS5 completeness.** Mechanically refuted for this technique (research §5.2). Do not attempt.
  Do not introduce `sorry`, axioms, or vacuous definitions toward it.
- The §5.1 `bBox` canonical proof (needs new list-splitting/finite-conjunction machinery).
- The §5.3 `Set.univ`-free tail redesign for CS5.
- Any change to `CT.lean`, `CK.lean`, `Segment.lean`, `SegmentLindenbaum.lean`,
  `CKTruthLemma.lean`, or `ConstructiveLatticeMonotonicity.lean`.
- Filtration or Zorn approaches (research §4b/§4c — rejected as wrong tool / provably impossible).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Module-system friction: the probe was written outside `module`/`@[expose] public section`; CS4.lean uses the new module system | M | M | Transcribe inside the existing `@[expose] public section`. If `structure CS4Segment`/`instance` need `public`/`expose` annotations, follow the pattern already used by `CKSegment` in `Segment.lean`. Build after each phase. |
| Re-deriving `cs4_axiom_sound` from `cs4_axiom_sound'` hits universe friction | L | L | Fallback: keep the existing proof body verbatim (it already compiles). The re-derivation is an optimization, not a requirement. Phase 4 states both paths. |
| `lake lint` docBlame on new `def`s/`theorem`s | M | H | Phase 6 is a dedicated docstring pass; probe already carries docstrings on `cs4Tail`, `cs4Seg`, `CS4Segment` (incl. fields), `cs4Mreach`, `cs4Val`, `cs4Bot`. Let `lake lint` be the arbiter. |
| `lake shake` proposes import changes | L | M | Probe compiles under CS4.lean's existing import closure, so no new imports are expected. Run shake without `--fix` first; inspect before applying. |
| `cs4FC'` prime name is unidiomatic for permanent public API | L | M | Default to `cs4FC'` verbatim to match the probe (lowest transcription risk). `cs4FC'` follows Mathlib's primed-variant convention. If review objects, rename is mechanical and local (Phase 1 + call sites). |
| CS5.lean cross-reference into CS4.lean's deleted blocker paragraph dangles | M | H | Explicitly handled in Phase 7; Phase 8 greps for stale references to the removed text. |
| Transcription drift from the verified probe | H | L | The probe is ground truth. Copy verbatim; do not "improve" proofs. Any deviation must be re-verified by build. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 7 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 8 | 6, 7 |

Phases within the same wave can execute in parallel. Phases 2-6 all edit `CS4.lean` and are
therefore strictly sequential; Phase 7 edits `CS5.lean` only and is territory-disjoint from
Phase 2.

---

### Phase 1: Add `cs4FC'` and the bridging lemma to CKExtension.lean [COMPLETED]

**Goal**: Make the weakened frame condition available, with the `cs4FC → cs4FC'` bridge, without
disturbing any existing definition.

**Tasks**:

- [ ] In `CKExtension.lean`, in the `## ≤-Composed Frame Conditions` section, add `cs4FC'`
      immediately after `cs4FC` (line 119-120), verbatim from probe lines 111-114.
- [ ] Add a docstring for `cs4FC'` explaining: it weakens `cs4FC`'s blanket transitivity to two
      existential clauses; `fourBox` is discharged at a re-based world `v ≥ w''` since `□A@w'`
      quantifies over all `z ≥ w'`; `fourDia` needs a genuine `r`-successor of `w''` but may
      unfold `◇A@u` at any `u' ≥ u`, so the FC supplies a good `u'`. Note that validity over
      `cs4FC'` is a **stronger** statement than over `cs4FC` (soundness harder, completeness
      easier) and that this is what makes canonical completeness go through.
- [ ] Add `cs4FC_implies_cs4FC'` immediately after `cs4FC'`, with a docstring noting it witnesses
      that `cs4FC'` is a genuine weakening (`v := w`, `u' := u`). Body verified during planning:
      `⟨h.1, fun hwu hle hu't => ⟨_, le_refl _, h.2 hwu hle hu't⟩, fun hwu => ⟨_, le_refl _, fun _ hut => h.2 hwu (le_refl _) hut⟩⟩`
- [ ] Update `CKExtension.lean`'s module docstring (lines 30, 42, 77) to mention `cs4FC'` alongside
      `ctFC`/`cs4FC`/`cs5FC`.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CKExtension`

**Note on placement**: the bridge lemma must live in `CKExtension.lean`, **not** in
`ConstructiveLatticeMonotonicity.lean`'s "Frame-Condition Inclusions" section, because CS4.lean
consumes it in Phase 4 and `ConstructiveLatticeMonotonicity` imports CS4 (transitively via
`ConstructiveLatticeSubsumption`) — placing it there would be an import cycle.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` - add `cs4FC'` + `cs4FC_implies_cs4FC'`, docstring touch-up

**Verification**:

- Scoped build succeeds.
- `ConstructiveLatticeMonotonicity.lean` still builds unchanged (pure addition, nothing renamed).

---

### Phase 2: Transcribe probe Parts A-C into CS4.lean (closure lemmas, tail, segment, world type) [COMPLETED]

**Goal**: Establish the CS4 canonical world type and its constructors.

**Tasks**:

- [ ] Append a `## Canonical Model` section to `CS4.lean` after the soundness section.
- [ ] Transcribe Part A verbatim (probe lines 14-41): `cs4_box_four`, `cs4_not_dia_dia`,
      `cs4_dia_of_mem`, `cs4_boxInv_subset`, `cs4_boxInv_trans`.
- [ ] Transcribe Part B verbatim (probe lines 43-72): `cs4Tail`, `cs4Seg`.
- [ ] Transcribe Part C verbatim (probe lines 74-106): `CS4Segment` (with field docstrings), the
      `Preorder` instance via `Preorder.lift`, `cs4Mreach`, `CS4Segment.ofHead`,
      `CS4Segment.diaRefuting`.
- [ ] Preserve the probe's explanatory comments: `cs4_not_dia_dia` is "THE hereditary step";
      `cs4Seg`'s `diam_witness` for `E = some A` needs `◇◇A ∉ H`, supplied by `fourDia`;
      `excl` is DATA not an existential, which keeps `tail_eq` usable by `rw`.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS4`

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` - add Parts A-C (~110 lines)

**Verification**:

- Scoped build succeeds, zero `sorry`.
- No new imports were required (expected — confirms the probe's import-closure finding).

---

### Phase 3: Transcribe probe Part D (canonical frame-condition verification) [NOT STARTED]

**Goal**: Prove the canonical CS4 model satisfies `cs4FC'`.

**Tasks**:

- [ ] Transcribe Part D verbatim (probe lines 108-144, excluding the `cs4FC'` definition already
      placed in Phase 1): `cs4_refl`, `cs4_fc4`, `cs4_fcdia`, `cs4FC'_cs4Mreach`.
- [ ] Add docstrings to each: `cs4_refl` derives reflexivity from `boxInv H ⊆ H` (`tBox`) plus
      `excl_head` — note the T-invariant comes for free, so unlike `CTSegment`, `CS4Segment` needs
      no `refl` field. `cs4_fc4`/`cs4_fcdia` both discharge their `boxInv` obligation via
      `cs4_boxInv_trans`.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS4`

**Timing**: 0.75 hours

**Depends on**: 2

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` - add Part D (~40 lines)

**Verification**:

- Scoped build succeeds, zero `sorry`.
- `cs4FC'_cs4Mreach` type-checks against the Phase 1 `cs4FC'` definition.

---

### Phase 4: Soundness reconciliation — add primed soundness, re-derive existing soundness [NOT STARTED]

**Goal**: Resolve the overlap between CS4.lean's existing soundness section (over `cs4FC`) and the
probe's soundness section (over `cs4FC'`) **without duplicating ~90 lines of near-identical proof**.

**Context**: CS4.lean already has `cs4_axiom_sound` / `cs4_soundness` / `cs4_soundness_derivable`,
all stated over `cs4FC` (lines 129, 185, 218). The probe has `cs4_axiom_sound'` /
`cs4_soundness'` / `cs4_soundness_derivable'` over `cs4FC'`. The two axiom-soundness proofs differ
**only** in the `fourDia` and `fourBox` cases; the other 13 cases are byte-identical.

**Resolution**: the primed versions are strictly stronger (validity over the weaker FC quantifies
over more frames). So the primed versions become the primary proofs, and the existing unprimed
public names are **retained as re-derived corollaries** via `cs4FC_implies_cs4FC'`. Nothing is
deleted from the public API; ~90 lines of duplication are avoided.

**Tasks**:

- [ ] Transcribe `cs4_axiom_sound'` verbatim from probe lines 146-196 (Part E).
- [ ] Transcribe `cs4_soundness'` verbatim from probe lines 198-226.
- [ ] Transcribe `cs4_soundness_derivable'` verbatim from probe lines 336-341.
- [ ] Replace the body of the existing `cs4_axiom_sound` with a corollary of `cs4_axiom_sound'`:
      `intro World _ r hfc val botForces v_uc bf_uc bf_val bf_r bf_r_wit w` then
      `exact cs4_axiom_sound' h_ax World r (cs4FC_implies_cs4FC' hfc) val botForces v_uc bf_uc bf_val bf_r bf_r_wit w`
- [ ] Similarly re-derive `cs4_soundness` and `cs4_soundness_derivable` from their primed
      counterparts via `cs4FC_implies_cs4FC'`.
- [ ] Update the docstrings of the unprimed trio to say they are corollaries of the primed
      versions over the stronger (`cs4FC`) frame class, retained for the
      `ConstructiveLatticeMonotonicity` inclusion chain.
- [ ] **Fallback**: if any re-derivation hits universe-unification friction
      (`cs4_axiom_sound` is `.{u, v}`; `cs4_axiom_sound'` is also `.{u, v}`, so this is not
      expected), restore the original proof body verbatim — it already compiles — and note the
      duplication in the summary. Do **not** spend more than 20 minutes fighting this.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS4`

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` - add primed soundness trio, re-derive unprimed trio

**Verification**:

- Scoped build succeeds, zero `sorry`.
- Both `cs4_soundness_derivable` and `cs4_soundness_derivable'` are present and type-check.
- Signatures of the three unprimed theorems are **unchanged** (public API preserved).

---

### Phase 5: Transcribe probe Parts F-G (truth lemma and completeness) [NOT STARTED]

**Goal**: Land `cs4_completeness` and `cs4_soundness_completeness`.

**Tasks**:

- [ ] Transcribe Part F verbatim (probe lines 228-300): `cs4Val`, `cs4Bot`, `cs4_truth_lemma`.
- [ ] Transcribe Part G verbatim (probe lines 302-346): `cs4Val_upward_closed`,
      `cs4Bot_upward_closed`, `cs4Bot_val`, `cs4Bot_mreach`, `cs4Bot_mreach_wit`,
      `cs4_completeness`, `cs4_soundness_completeness`.
- [ ] Note in the `cs4_truth_lemma` docstring that the diamond-backward case is the one the whole
      technique exists for: it uses `CS4Segment.diaRefuting` and closes via `cs4_dia_of_mem`
      (`tDia`) against the hereditary `◇A`-exclusion.
- [ ] Preserve the universe signatures exactly: `cs4_completeness` and
      `cs4_soundness_completeness` are `CKValidFC.{u, u}` (monomorphic — forced by
      `ckvalidFC_completeness`'s `World : Type u`), while `cs4_soundness_derivable'` is
      `.{u, v}`. Do not attempt to unify these.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS4`
- [ ] Verify axiom cleanliness:
      `#print axioms Cslib.Logic.Modal.cs4_completeness` and
      `#print axioms Cslib.Logic.Modal.cs4_soundness_completeness`
      must each report exactly `[propext, Classical.choice, Quot.sound]`.

**Timing**: 1.25 hours

**Depends on**: 4

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` - add Parts F-G (~130 lines)

**Verification**:

- Scoped build succeeds, zero `sorry`, zero new axioms.
- `#print axioms` output matches the probe's verified baseline exactly.

---

### Phase 6: CS4.lean module docstring rewrite and docstring/lint pass [NOT STARTED]

**Goal**: Bring CS4.lean to CSLib house style and remove the obsolete blocker narrative.

**Tasks**:

- [ ] **Delete** the completeness-blocker paragraph (CS4.lean lines 22-38) — the entire
      "**Completeness for `CS4` is not established in this module**" narrative. It is now false.
- [ ] Rewrite the module docstring to state: CS4 is sound for `CKValidFC cs4FC` **and** sound and
      complete for `CKValidFC cs4FC'`. Explain the two changes that unblock it (weakened FC;
      hereditary `◇A`-exclusion) and why the one-step `A`-exclusion of `diamRefutingSegment` could
      not work, citing that `cs4FC` forces every world with a nonempty realized tail to be
      diamond-degenerate (research §2) — i.e. the task-501 obstruction was real but was an
      obstruction to `cs4FC`, not to CS4 completeness.
- [ ] Update `## Main Definitions` to add `cs4Tail`, `cs4Seg`, `CS4Segment`, `cs4Mreach`,
      `cs4Val`, `cs4Bot`.
- [ ] Add a `## Main Results` section listing `cs4_axiom_sound`/`cs4_soundness`/
      `cs4_soundness_derivable` (over `cs4FC`), their primed counterparts (over `cs4FC'`),
      `cs4FC'_cs4Mreach`, `cs4_truth_lemma`, `cs4_completeness`, `cs4_soundness_completeness`.
- [ ] Keep the existing `## References` (Wijesekera1990, Simpson1994); verify both BibKeys resolve
      in `references.bib`.
- [ ] `lake lint` — add docstrings for every new `def` and `theorem` flagged by docBlame.
- [ ] `lake exe lint-style` (use `--fix` for mechanical line-length/whitespace issues).
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS4`

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` - module docstring, per-declaration docstrings

**Verification**:

- `lake lint` reports zero warnings for CS4.lean.
- `lake exe lint-style` clean.
- No occurrence of the string "not established" or "open item" remains in CS4.lean.

---

### Phase 7: Re-ground CS5.lean's blocking comment on the mechanized obstruction [COMPLETED]

**Goal**: Leave CS5 completeness **BLOCKED**, but cite the correct, newly mechanized reason.

**Scope guard**: this phase is docstring-only. Do **not** add, attempt, or stub any CS5
completeness content. No `sorry`, no axioms, no vacuous definitions.

**Tasks**:

- [ ] **Delete** CS5.lean's current blocker paragraph (lines 30-37), which attributes the block to
      "CS4's open completeness blocker (task 501 Phase 5)" and the one-step tail-exclusion
      reasoning. That attribution is now **obsolete**: CS4 completeness is proved, so CS5 cannot
      inherit a blocker that no longer exists.
- [ ] **Repair the dangling cross-reference**: line 33 currently points at "`CS4.lean`'s module
      docstring ... for the full analysis" — that paragraph is deleted in Phase 6. This reference
      must not survive.
- [ ] Write the replacement blocker note citing the mechanized negative result from task 508:
  - `bDia` (`◇□A → A`) is **not sound** over `cs5FCweak` — the natural CS5 analogue of the
    weakened frame condition that makes CS4 work (reflexivity + both `cs4FC'` clauses +
    the weakened symmetry `FCsym_box`). Witness: a two-world `Bool` countermodel (`false`
    consistent, `true` exploding) in which `◇□p → p` fails. So the CS4 technique **cannot** be
    extended to CS5 — this is a soundness failure, which no amount of canonical-model work fixes.
  - `FCbdia` (the FC strong enough to validate `bDia`) fails canonically: at `w := ofHead(H)` with
    `H` consistent and `u := cexpl`, any `u' ≥ cexpl` has head `Set.univ`, forcing `t = cexpl`,
    so `t ≤ w` would give `Set.univ ⊆ H` — false.
  - Note the one lead for future work: **CS5 ⊢ `◇⊥ → ⊥`** (also mechanized in task 508; CK/CT/CS4
    do not prove this), which may permit a `Set.univ`-free tail redesign. It does not finish the
    job — `FCbdia` still needs genuine canonical symmetry, whose classical proof needs maximality
    (`B ∉ w.head ⇒ ¬B ∈ w.head`), unavailable for quasi-prime heads. This is the known-hard core
    of constructive S5 canonical completeness.
  - State plainly that CS5 completeness is **genuinely open** and re-scoped to a separate research
    task, not deferred with placeholders.
- [ ] Point the reference at task 508's artifacts:
      `specs/508_unblock_CK_CS4_CS5_completeness/reports/01_cs4-cs5-completeness-technique.md` §5
      and `probes/cs5-obstruction-verified.lean`.
- [ ] Note that `bBox` is *not* the problem (research §5.1) — the weakened symmetry `FCsym_box`
      validates it; `bDia` alone is the blocker.
- [ ] `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5`

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` - module docstring blocker paragraph only

**Verification**:

- Scoped build succeeds.
- CS5.lean contains no reference to a CS4 completeness blocker.
- CS5.lean's soundness content is byte-identical to before (docstring-only change).

---

### Phase 8: Downstream migration check and full CI pipeline [NOT STARTED]

**Goal**: Prove zero downstream breakage and green CI.

**Tasks**:

- [ ] `grep -rn "cs4FC" --include=*.lean .` (excluding `specs/`) and confirm every hit is either
      (a) an intended `cs4FC'` addition, or (b) an untouched pre-existing `cs4FC` user. Expected
      pre-existing users, which must still compile **unchanged**:
      `ConstructiveLatticeMonotonicity.lean:72` (`cs5FC_implies_cs4FC`),
      `:77` (`cs4FC_implies_ctFC`), `:82` (`cs5FC_implies_ctFC`).
- [ ] Grep for stale prose referencing the removed blockers across the repo (not just `.lean`):
      search for "completeness blocker", "task 501 Phase 5", "not established" in
      `Cslib/`, `README.md`, and any docs. Update or remove.
- [ ] Optional (only if it reads naturally in the inclusion chain): add `cs5FC_implies_cs4FC'` to
      `ConstructiveLatticeMonotonicity.lean`'s "Frame-Condition Inclusions" section as
      `cs4FC_implies_cs4FC' (cs5FC_implies_cs4FC h)`. **Skip if it adds no value** — it is not
      required by anything in this plan.
- [ ] Run the full CSLib CI pipeline in order:
  - [ ] `lake exe cache get` (if Mathlib cache is cold)
  - [ ] `lake build`
  - [ ] `lake exe checkInitImports`
  - [ ] `lake lint`
  - [ ] `lake exe lint-style`
  - [ ] `lake test`
  - [ ] `lake shake --add-public --keep-implied --keep-prefix` (inspect output; do **not**
        blind-`--fix`. No import changes are expected — see Research Integration.)
- [ ] `lake exe mk_all --module` is **not** required: no new files are added. Confirm
      `Cslib.lean` is unchanged.
- [ ] Final axiom audit: `#print axioms Cslib.Logic.Modal.cs4_soundness_completeness` reports
      exactly `[propext, Classical.choice, Quot.sound]`.
- [ ] Confirm zero `sorry` across the touched files: `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/Constructive/`

**Timing**: 1 hour

**Depends on**: 6, 7

**Files to modify**:

- Possibly `Cslib/Logics/Modal/Metalogic/InterSystem/ConstructiveLatticeMonotonicity.lean` (only if
  the optional convenience lemma is added)
- Any file carrying stale blocker prose

**Verification**:

- Every CI step exits 0.
- `ConstructiveLatticeMonotonicity.lean` compiles with no edits forced by this task.

---

## Testing & Validation

- [ ] `lake build` — full project, zero errors, zero warnings.
- [ ] `lake exe checkInitImports` — all touched files import `Cslib.Init`.
- [ ] `lake lint` — zero environment-linter warnings (docBlame in particular).
- [ ] `lake exe lint-style` — zero text-linter warnings.
- [ ] `lake test` — `CslibTests/` suite passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no import minimization proposed.
- [ ] Zero `sorry`, zero new axioms, zero vacuous definitions (`def X := True` and relatives) in
      any touched file.
- [ ] `#print axioms Cslib.Logic.Modal.cs4_completeness` = `[propext, Classical.choice, Quot.sound]`.
- [ ] `#print axioms Cslib.Logic.Modal.cs4_soundness_completeness` = `[propext, Classical.choice, Quot.sound]`.
- [ ] Public API preservation: `cs4FC`, `cs4_axiom_sound`, `cs4_soundness`,
      `cs4_soundness_derivable` all still exist with unchanged signatures.
- [ ] CS5.lean still has **no** completeness theorem and **no** `sorry`.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — `cs4FC'`, `cs4FC_implies_cs4FC'`
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` — canonical model, truth lemma,
  `cs4_completeness`, `cs4_soundness_completeness`; blocker narrative removed
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — re-grounded blocking comment
- `specs/508_unblock_CK_CS4_CS5_completeness/summaries/01_cs4-completeness-integration-summary.md`
- Unchanged (verify): `CT.lean`, `CK.lean`, `Segment.lean`, `SegmentLindenbaum.lean`,
  `CKTruthLemma.lean`, `ConstructiveLatticeMonotonicity.lean`, `Cslib.lean`

## Rollback/Contingency

- All work is additive to two files plus a docstring change to a third. `git checkout --
  Cslib/Logics/Modal/Metalogic/Constructive/{CKExtension,CS4,CS5}.lean` reverts cleanly.
- Commit per phase (`task 508 phase {P}: {name}`) so any phase can be reverted independently.
- The probes under `specs/508_unblock_CK_CS4_CS5_completeness/probes/` are the ground truth and
  are never modified; if transcription diverges, re-run
  `lake env lean specs/508_unblock_CK_CS4_CS5_completeness/probes/cs4-completeness-verified.lean`
  to re-establish the baseline and diff against it.
- If Phase 4's re-derivation proves troublesome, revert only that phase's corollary bodies to the
  original proofs (kept in git history) — the primed theorems and completeness do not depend on
  the re-derivation.
- If a genuine mathematical problem surfaces (not expected — the probe compiles), mark the phase
  **[BLOCKED]**, document the goal state reached, and return `status: "partial"`. Do **not**
  introduce `sorry`, axioms, or vacuous definitions.
