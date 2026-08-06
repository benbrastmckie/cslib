/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Dedup
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.S4.BirthKey
public import Cslib.Logics.Modal.Tableau.S4.Driver
public import Cslib.Logics.Modal.Tableau.S4.Guard
public import Cslib.Logics.Modal.Tableau.S4.Hintikka
public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds

/-! # S4 Loop-Checking Machinery

This module builds the equality-blocking loop-checking machinery for the S4
(reflexive-transitive) modal tableau: per-world relevant-formula-set extraction, a
decidable equality test over `modalSubfmls φ₀`, the minting guard that consults this test
before creating a fresh world, the S4 rule-application function, and the S4 Hintikka-set
characterization.

S4 is deliberately **not** an instantiation of `RuleApplicationSpec` (`GenericDriver.lean`):
its transitively-propagating 4-rule places `T(□φ)` (unchanged modal depth) at successor
worlds, which falsifies the exact-decrement edge invariant (`rankStep`) that
`RuleApplicationSpec` demands. S4 reuses the generic driver (`modalStepBranchGen` etc.)
**definitionally only**, via a `φ₀`-parameterized `RuleApply` value, and supplies its own
sibling termination argument (`S4LoopInv`, a pigeonhole bound on `2 ^ (2 * |modalSubfmls φ₀|)`
possible signed-relevant-formula sets) instead of the K/T rank-decrease argument.

**Redesign note**: an earlier `blockingWorld` guard and `worldSetsDistinct` invariant were
both found to be structurally unsound -- distinctness
over the *live* branch is not a loop invariant (relevant sets grow monotonically), and the
guard compared the *source* world's set rather than the *prospective successor's* birth
content. This module now uses `blockingWorldS4`/`successorBirthContent` (stable birth-content
guard) and `S4LoopInv`'s `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse` fields
(stable per-world birth keys) in their place.

## Main Definitions

- `formulasAtWorld`: the sub-list of a branch's signed formulas at a given world.
- `sameRelevantSet`: the decidable equality-of-relevant-formula-set test over
  `modalSubfmls φ₀`, used for comparison (retained as the comparison primitive).
- `signedSubfmls`/`relevantSetFinset`: the finite `Finset (Sign × Proposition Atom)` codomain
  and the live relevant set restated as a `Finset`.
- `successorBirthContent`/`blockingWorldS4`: the redesigned minting guard:
  blocks iff an existing known world's CURRENT relevant set equals the PROSPECTIVE successor's
  birth content, fixing Gap 2 (the old guard compared the source world's set instead).
- `modalApplyOneS4`: the `φ₀`-parameterized S4 rule-application function (Decision D1):
  at the two minting shapes, consult `blockingWorldS4` before falling through to the
  underlying rule's fresh-world minting.
- `modalStepBranchS4`/`modalExpandBranchesS4`/`modalTableauS4`: the S4 driver, reusing
  `Saturation.lean`'s generic driver **definitionally only** (no `RuleApplicationSpec`
  instance -- Correction 3).
- `modalHintikkaSetS4`: the S4 Hintikka-set characterization, a small delta over
  `modalHintikkaSet` (Decision D3).

## Strategy

Blocking is **equality-of-relevant-formula-set**, not subset-blocking: two worlds `w`,
`w'` are considered "the same" for loop-checking purposes exactly when they agree, for
every `ψ ∈ modalSubfmls φ₀` and every sign `s`, on whether `⟨s, ψ, w⟩` (`⟨s, ψ, w'⟩`
respectively) is on the branch. This is simpler than subset blocking and still yields a
`2 ^ (2 * |modalSubfmls φ₀|)` bound on the number of distinct worlds a saturating S4 tableau
can create (below), since each world's *birth key* is a distinct element of the powerset of
`modalSubfmls φ₀ × Sign` -- the *birth key*, not the live relevant set, is what the
pigeonhole argument now injects (see `S4LoopInv`).

Do **not** import `LoopInduction.lean`: despite the name, it is a `Forall2` list lemma
about the *fuel* loop in the generic driver, unrelated to modal loop-checking.

## Measured Baseline (modal Tableau subsystem)

Recorded here because several size and inventory figures for this subsystem drifted between
prose descriptions and the tree. **Every row below carries the command that reproduces it.**
The rule this section exists to enforce: if a figure is quoted anywhere in this subsystem's
documentation, quote the command with it, and re-run the command rather than trusting the
stored number.

Captured at commit `7eb51f69`, toolchain Lake 5.0.0-src+68218e8 (Lean 4.31.0), and re-confirmed
against the working tree when this section landed.

### Size and declaration density

```
wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean
wc -l Cslib/Logics/Modal/Tableau/FrameSoundness.lean
wc -l Cslib/Logics/Modal/Tableau/FrameCompleteness.lean
PAT='^(private )?(protected )?(noncomputable )?'
PAT="$PAT(theorem|lemma|def|abbrev|instance|structure|inductive) "
grep -cE "$PAT" Cslib/Logics/Modal/Tableau/LoopChecking.lean
```

At `7eb51f69`: `LoopChecking.lean` 10,540 lines, `FrameSoundness.lean` 5,317,
`FrameCompleteness.lean` 4,307 -- 20,164 across the three. `LoopChecking.lean` declares 230
top-level items. The three line-count rows are pinned to that commit and are the one part of
this table that moves under ordinary documentation edits (landing this very section moved two of
them); the declaration count does not. Re-run `wc -l` rather than citing the stored figure.

### Sorry census

```
{ grep -rnE '^[[:space:]]*sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; \
  grep -rnE '(:=|\bby)[[:space:]]+sorry([[:space:]]*--.*)?$' --include='*.lean' Cslib/; } \
  | sort -u | grep 'Modal/Tableau/'
```

**1** in this subsystem: `branchSatisfiableIn_s4FC_ancestor_redirect` in `FrameSoundness.lean`,
the retained, user-decided, immovable obstruction (see that lemma's docstring). Dropping the
final `grep` gives **29** code-position sorries repo-wide.

Three different definitions of "sorry count" circulate and they do not agree, so state which one
is meant. The 29 above counts sorries in *code position*. The CI-pipeline grep
(`grep -rn "\bsorry\b" Cslib/`, minus comment-leading lines) returns 158 because it also matches
docstring prose such as "sorry-free". The `declaration uses 'sorry'` warning count from an
incremental `lake build` is an **undercount** and must never be used as a census: cached modules
do not re-elaborate and so never re-emit their warnings.

### Axiom census -- a scope distinction, not a corrected number

```
grep -rnE '^axiom ' Cslib/Logics/Modal/Tableau/ | wc -l    # 0
grep -rnE '^axiom ' Cslib/ | wc -l                         # 26
grep -row 'axiom' Cslib/Logics/Modal/Tableau/ | wc -l      # 3
grep -row 'axiom' Cslib/ | wc -l                           # 1701
```

These are **two scopes, not two candidate values for one quantity, and neither supersedes the
other**: this subsystem declares **0** axioms; the repository declares **26**, none of them here.
The 3 and 1,701 figures are raw word occurrences in prose and identifiers, not declarations, and
are recorded only to show why a naive word-count grep diverges. A previously-noted "26 vs 47"
discrepancy was a scope confusion of exactly this kind, not a drift.

### Inventory figures that drifted

```
grep -rho 'Local re-derivation' Cslib/ | wc -l                                    # 55
grep -rl 'ModalTableauResult' --include='*.lean' Cslib/Logics/Modal/Tableau/ | wc -l   # 8
grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake | wc -l    # 9
grep -nE '^(private )?(theorem|lemma) hintikkaS4_' \
  Cslib/Logics/Modal/Tableau/LoopChecking.lean | wc -l   # 8
grep -n 'structure S4LoopInv' Cslib/Logics/Modal/Tableau/LoopChecking.lean
wc -l CslibTests/S4LoopGuardRegression.lean                                       # 197
```

* **Local re-derivation sites: 55**, not the 77 previously carried (figure as it stood before the
  de-duplication effort below; retained here as a historical baseline, not a live count). 77 is
  not reproducible by any obvious command (`-i 're-derivation'` gives 80, `-i 're-deriv'` gives
  106) and is retired. **The smaller headline does not mean less work.** Every per-lemma
  spot-check behind the old figure was an undercount (`modalSubfmls_trans` 4 sites not 3,
  `modalKnownWorlds_fold_spec` 6 not 4, `hasEdge_addEdge_cases` 7 not 4), and the old per-file
  distribution omitted `LoopChecking.lean`'s **14** sites entirely -- the largest file in the
  subsystem. The de-duplication work is larger, not smaller.
* **Post-de-duplication update**: the comment-string count is now **12** (`grep -rho 'Local
  re-derivation' Cslib/ | wc -l`, re-measured after `modalSubfmls_self_mem_S5` was deleted from
  `S5Simplification.lean` and its call sites routed to the public `FmpMeasure.lean` origin),
  down from 55 -- but this number was NEVER the authoritative
  measure of duplication and should not be read as "duplication resolved: 55 minus 12". The
  actual tracking mechanism throughout the de-duplication effort was a declaration-level census
  (base-name/suffix-family matching across the subsystem, driven by a reusable script kept
  alongside the project's task-management artifacts), which is systematically more accurate: the
  comment census both undercounts (several genuine duplicates carried no `Local re-derivation`
  comment at all -- comment-driven deletion would have missed them silently) and overcounts in
  the other direction (some `Local re-derivation`-labelled facts are genuinely distinct
  propositions over frame-specific types like `modalUniverseS4`, not re-derivations of the same
  fact, discovered only by a build-time type mismatch when treated as a duplicate). The remaining
  12 comment sites correspond to the residue documented as Reasoned Exclusions (either the origin
  is already public, the copy dodges an ambient instance, or the dependency graph does not reach
  the origin) plus a handful of genuine specializations (frame-specific restatements,
  keyed-driver variants) that were never duplicates. The declaration-level census, not this
  comment count, is the authoritative figure for future maintenance.
* **`ModalTableauResult` spans 8 modules here, 9 repo-wide** (the ninth is
  `CslibTests/S4LoopGuardRegression.lean`). A previously reported span of 11 is drift.
* **`hintikkaS4_*` bridge set: 8 declarations.** Counting *distinct identifiers* instead returns
  11, because three further names occur only in call positions or prose. See the
  "Redirect Forward-Cone Free Transfer" section for what was removed and when.
* **One root-level `Boneyard/` directory exists** (`find . -type d -name 'Boneyard' -not -path
  './.lake/*'` returns exactly `./Boneyard`), holding declarations archived from this file as
  zero-consumer under the convention documented in `Boneyard/README.md`. It is excluded from
  `lake build`, every census, and every linter by import-reachability -- see that README's
  "Why This Is Free" section for the mechanism.

### Figures deliberately NOT re-measured

Recorded as gaps rather than filled with substitutes. **No number has been fabricated for any of
these, and none should be quoted as measured.**

* The two amplification figures inherited from earlier analysis -- **4 declarations / 1,036
  lines**, and **43 declarations / 1,983 lines reachable from `modalTableauS4Keyed_complete`** --
  are unverified inheritances. Re-measuring them needs a transitive-dependency closure over the
  elaborated environment, which needs built `.olean`s for these modules.
* The redirect semantic surface (reported as 4 clauses / 14 code lines) is likewise an inherited
  figure, not a row of this capture.

Anything depending on these must re-measure them, or say plainly that it is relying on an
unverified inheritance.

### Build gate at capture

`lake build` failed at capture, and the failure is **outside this subsystem**: a non-exhaustive
match in `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean` (introduced by
commit `88b198bf`, belonging to in-flight work on the constructive nested-sequent development).
`lake exe checkInitImports` then fails downstream as a consequence, not as an independent defect.
While that holds, `checkInitImports` verifies nothing and must not be reported as passing.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

omit [Hashable Atom] in
/-- **`keyLowerBd`'s minting case, box-negative shape**: the prospective birth content computed
PRE-step (`successorBirthContent`) is a subset of the freshly-minted world's relevant set
computed POST-step (`relevantSetFinset` over `newForms ++ b`). Consumes the additive keyed
mint's literal box-neg minting payload (`modalApplyOneS4KeyedMint_boxNeg_eq_S4`) via the
`hnewForms` hypothesis (stated in terms of `modalApplyOneS4KeyedMint` rather than the raw
payload literal, so the caller only needs its actual output, not to hand-reconstruct its list
shape) plus the branch-closure witness fact (`hb`/`hsf`, via `modalUniverseS4_mem_formula`/
`modalSubfmls_trans`) that the witness formula `φ` itself lies in `signedSubfmls φ₀`. The two
box-plus disjuncts (`successorBirthContent`'s third/fourth) land inside `boxPlusExtraS4`, which
is why `newForms` must already be the ENRICHED keyed payload -- the raw `modalApplyOne` payload
never contains the boxed transmission (report §4). -/
private lemma successorBirthContent_boxNeg_subset_relevantSetFinset
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (φ : Proposition Atom)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (newForms : List (SignedFormula (Proposition Atom) WorldIndex))
    (hnewForms : (modalApplyOneS4KeyedMint
        (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = RuleResult.linear newForms) :
    successorBirthContent φ₀ b .neg φ w ⊆
      relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b) := by
  rw [congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc φ w)] at hnewForms
  injection hnewForms with hnewForms
  subst hnewForms
  have hφsub : φ ∈ modalSubfmls φ₀ := by
    have h1 : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
    have h2 : φ ∈ modalSubfmls (Proposition.box φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
    exact modalSubfmls_trans h2 h1
  have hwit : ((Sign.neg, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ :=
    mem_signedSubfmls_of_formula_S4 .neg hφsub
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, hdisj⟩
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hwit, any_beq_of_mem_S4 ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hpmem, any_beq_of_mem_S4 ?_⟩
    rcases hdisj with ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩
    · -- box-positive transmission: p.1 = pos, T(□p.2)@w ∈ b
      have hbmem : (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hbp : (p.2, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box p.2, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (boxPositivesOf b).filterMap (fun (ψ, src) =>
            if src == w then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
              if b.any (· == sf') then none else some sf'
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨(p.2, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_cons_of_mem _ htarget)))
    · -- diamond-negative transmission: p.1 = neg, F(◇p.2)@w ∈ b
      have hbmem : (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hdedup : b.any (· == (⟨.neg, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          b.filterMap (fun sf' =>
            if sf'.sign == .neg && sf'.label == w then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex :=
                  ⟨.neg, ψ, modalNextWorld b⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨⟨.neg, .diamond p.2, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ htarget))
    · -- box-plus positive: p.1 = pos, p.2 = box ψ, T(□ψ)@w ∈ b -- own box-positive, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_pos_disjunct_elim hpb
      have hbp : (ψ, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box ψ, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, .box ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨(ψ, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)
    · -- box-plus negative: p.1 = neg, p.2 = diamond ψ, F(◇ψ)@w ∈ b -- own diamond-negative, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_neg_disjunct_elim hpb
      have hdedup : b.any (· == (⟨.neg, .diamond ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append]
        refine Or.inr ?_
        simp only [List.mem_filterMap]
        exact ⟨⟨.neg, .diamond ψ, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)

omit [Hashable Atom] in
/-- **`keyLowerBd`'s minting case, diamond-positive shape** (dual of the box-negative case):
the prospective birth content computed PRE-step is a subset of the freshly-minted world's
relevant set computed POST-step. -/
private lemma successorBirthContent_diamondPos_subset_relevantSetFinset
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (φ : Proposition Atom)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (newForms : List (SignedFormula (Proposition Atom) WorldIndex))
    (hnewForms : (modalApplyOneS4KeyedMint
        (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
        = RuleResult.linear newForms) :
    successorBirthContent φ₀ b .pos φ w ⊆
      relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b) := by
  rw [congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc φ w)] at hnewForms
  injection hnewForms with hnewForms
  subst hnewForms
  have hφsub : φ ∈ modalSubfmls φ₀ := by
    have h1 : (Proposition.diamond φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
    have h2 : φ ∈ modalSubfmls (Proposition.diamond φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
    exact modalSubfmls_trans h2 h1
  have hwit : ((Sign.pos, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ :=
    mem_signedSubfmls_of_formula_S4 .pos hφsub
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, hdisj⟩
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hwit, any_beq_of_mem_S4 ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hpmem, any_beq_of_mem_S4 ?_⟩
    rcases hdisj with ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩
    · -- box-positive transmission: p.1 = pos, T(□p.2)@w ∈ b
      have hbmem : (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hbp : (p.2, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box p.2, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (boxPositivesOf b).filterMap (fun (ψ, src) =>
            if src == w then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
              if b.any (· == sf') then none else some sf'
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨(p.2, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_cons_of_mem _ htarget)))
    · -- diamond-negative transmission: p.1 = neg, F(◇p.2)@w ∈ b
      have hbmem : (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hdedup : b.any (· == (⟨.neg, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          b.filterMap (fun sf' =>
            if sf'.sign == .neg && sf'.label == w then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex :=
                  ⟨.neg, ψ, modalNextWorld b⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨⟨.neg, .diamond p.2, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ htarget))
    · -- box-plus positive: p.1 = pos, p.2 = box ψ, T(□ψ)@w ∈ b -- own box-positive, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_pos_disjunct_elim hpb
      have hbp : (ψ, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box ψ, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, .box ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨(ψ, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)
    · -- box-plus negative: p.1 = neg, p.2 = diamond ψ, F(◇ψ)@w ∈ b -- own diamond-negative, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_neg_disjunct_elim hpb
      have hdedup : b.any (· == (⟨.neg, .diamond ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append]
        refine Or.inr ?_
        simp only [List.mem_filterMap]
        exact ⟨⟨.neg, .diamond ψ, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)

/-! ## Assembling `keyLowerBd`'s Preservation -/

/-- **`keyLowerBd`'s driver-level preservation**: every key
recorded after an S4Keyed step remains a lower bound on its live relevant set, over EVERY
branch the step produces. Assembles `modalStepBranchS4Keyed_branch_superset` (handles every
OLD key uniformly, via `relevantSetFinset_mono`, regardless of which rule fired) with the two
closed minting-content subset lemmas (`successorBirthContent_boxNeg_subset_relevantSetFinset`
/ `_diamondPos_subset_relevantSetFinset`, for the NEW key at the two minting leaves). -/
lemma modalStepBranchS4_preserves_keyLowerBd (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hLB : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → k ⊆ relevantSetFinset φ₀ b' w := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b' w :=
    fun b' hb' w k hwk => (hLB w k hwk).trans (relevantSetFinset_mono φ₀ b b' w (hsuper b' hb'))
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_boxNeg_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_diamondPos_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`keyLowerBd`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keyLowerBd` against the ordered stepper: the argument never uses
"`sf` is the first applicable formula in `b`", only "`sf ∈ b`, `sf ∉ e`, and this specific rule
application produced `keys'`" -- exactly what `modalStepBranchS4KeyedOrdered_selected_mem`
supplies. Uses the ordered form of the branch-superset fact
(`modalStepBranchS4KeyedOrdered_branch_superset`) for the OLD-key half of the argument. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keyLowerBd (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hLB : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → k ⊆ relevantSetFinset φ₀ b' w := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b' w :=
    fun b' hb' w k hwk => (hLB w k hwk).trans (relevantSetFinset_mono φ₀ b b' w (hsuper b' hb'))
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_boxNeg_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_diamondPos_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`keysInUniverse`'s driver-level preservation**: every key
recorded after an S4Keyed step is drawn from `signedSubfmls φ₀`. Unlike `keyLowerBd`, this
obligation is independent of the (possibly several) output branches `newBs` -- it is a fact
about `keys'` alone. Assembled the same way: old keys survive via the `keysInUniverse`
hypothesis directly (`keys ⊆ keys'` always), new keys (the two minting leaves) via
`successorBirthContent_subset_signedSubfmls`, whose witness-formula-membership side
condition is derived exactly as in `successorBirthContent_boxNeg_subset_relevantSetFinset`/
`_diamondPos_subset_relevantSetFinset` above. -/
lemma modalStepBranchS4_preserves_keysInUniverse (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hIU : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ w k, (w, k) ∈ keys' → k ⊆ signedSubfmls φ₀ := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hIU w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.box ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .neg ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.diamond ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .pos ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk

/-- **`keysInUniverse`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keysInUniverse` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysInUniverse (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hIU : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ w k, (w, k) ∈ keys' → k ⊆ signedSubfmls φ₀ := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hIU w k hwk
    | skip
  case neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.box ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .neg ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk
  case pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.diamond ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .pos ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk

/-! ## Assembling `keysTotal`'s Preservation -/

/-- **`keysTotal`'s driver-level preservation** (the crux): every
known world after an S4Keyed step has a recorded key. Assembled by a top-level split on whether
`sf` is one of the two minting shapes: at the 2 minting shapes, the newly-minted world's label
is exactly `modalNextWorld b` (`mintGroup_label_eq_freshWorld`), which `keys'` gains an entry
for by construction; at the other 12 shapes, `modalApplyOneS4Keyed_nonMint_known_S4` shows no
label beyond `modalKnownWorlds b` is ever introduced, so the new-known-world case never
actually arises there and old keys (`keys ⊆ keys'`, `modalStepBranchS4Keyed_keys_subset`)
suffice. -/
lemma modalStepBranchS4_preserves_keysTotal (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ keys' := by
  have hkeysub := modalStepBranchS4Keyed_keys_subset φ₀ b e acc keys newBs newExps newAcc keys'
    hstep
  have hold : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys' :=
    fun w hw => (hKT w hw).imp (fun k hk => hkeysub hk)
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .neg ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .pos ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' w hw
    have hwb : w ∈ modalKnownWorlds b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' (List.mem_flatten.mpr ⟨br, hbr, hsf'⟩)
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf; simp at hsf
    exact hold w hwb

/-- **`keysTotal`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keysTotal` against the ordered stepper: the top-level
minting/non-minting split, the `mintGroup_label_eq_freshWorld` argument at the two minting
shapes, and `modalApplyOneS4Keyed_nonMint_known_S4` at the other twelve all consume only
"`sf ∈ b`, this rule application produced `keys'`" -- never "`sf` is the first applicable
formula" -- so the argument transfers unchanged once fed
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysTotal (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ keys' := by
  have hkeysub := modalStepBranchS4KeyedOrdered_keys_subset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys' :=
    fun w hw => (hKT w hw).imp (fun k hk => hkeysub hk)
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .neg ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .pos ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' w hw
    have hwb : w ∈ modalKnownWorlds b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' (List.mem_flatten.mpr ⟨br, hbr, hsf'⟩)
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf; simp at hsf
    exact hold w hwb

/-- **`keysDistinct`'s driver-level preservation**: every pair of
distinctly-labeled keys recorded after an S4Keyed step remains distinct-keyed. Assembled the
same way as `keyLowerBd`/`keysInUniverse`/`keysTotal`: a `sf.sign`/`sf.formula` case split via
`modalStepBranchS4Keyed_result_keys_eq`, 12 leaves trivial (`keys' = keys`), the 2 minting
leaves reduce to exactly `keysUpdate_preserves_keysDistinct`'s own match shape. -/
lemma modalStepBranchS4_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ w1 w2 k1 k2, (w1, k1) ∈ keys' → (w2, k2) ∈ keys' → w1 ≠ w2 → k1 ≠ k2 := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w1 w2 k1 k2 h1 h2 hne
  rw [hkeq] at h1 h2
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at h1 h2
  all_goals first
    | exact hKD w1 w2 k1 k2 h1 h2 hne
    | skip
  case neg.neg.box =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .neg ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne
  case neg.pos.diamond =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .pos ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne

/-- **`keysDistinct`'s ordered-driver preservation (escalation-trigger sub-lemma).**
Identical statement and proof shape to `modalStepBranchS4_preserves_keysDistinct`, transcribed
against the ordered stepper via `modalStepBranchS4KeyedOrdered_selected_mem` in place of the
direct `findSome?` extraction from `modalStepBranchS4Keyed`. The plan flags this sub-lemma as the
escalation trigger: if it required ANY weakening of `keysUpdate_preserves_keysDistinct`, that
would contradict the plan's central claim that reordering only changes *timing*, never producing
a duplicate key. It does not need any such weakening -- the argument is verbatim
selection-independent, since `modalStepBranchS4Keyed_result_keys_eq` and
`keysUpdate_preserves_keysDistinct` only ever consume "some formula `sf` fired, producing this
key list", never "`sf` is the first such formula in `b`". -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ w1 w2 k1 k2, (w1, k1) ∈ keys' → (w2, k2) ∈ keys' → w1 ≠ w2 → k1 ≠ k2 := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w1 w2 k1 k2 h1 h2 hne
  rw [hkeq] at h1 h2
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at h1 h2
  all_goals first
    | exact hKD w1 w2 k1 k2 h1 h2 hne
    | skip
  case neg.box =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .neg ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne
  case pos.diamond =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .pos ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne

/-- **`eNodup`'s driver-level preservation**: `modalStepBranchS4Keyed` preserves `Nodup`-ness of
the expanded set `e`, exactly like the generic `modalStepBranch_preserves_expandedNodup_gen`
(`FmpMeasure.lean`) -- fully rule-agnostic, only the top-level `RuleResult` constructor shape
matters, `keys`/`keys'` never enter the argument. Direct case split on `result` (not routed
through the generic lemma, since `modalStepBranchS4Keyed` returns a 4-tuple with `keys'` bolted
on rather than literally being `modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)`). -/
lemma modalStepBranchS4_preserves_eNodup (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys'))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfnotmem : sf ∉ e := by
    intro hmem
    exact hexp (by simp only [List.any_eq_true]; exact ⟨sf, hmem, by simp⟩)
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hnodup
  · rw [hres] at hsf; simp at hsf

/-- **`eNodup`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_eNodup`: fully rule-agnostic (only the top-level `RuleResult`
constructor shape matters), so the selected formula's identity plays no role beyond `sf ∉ e`,
which `modalStepBranchS4KeyedOrdered_selected_mem` supplies directly. -/
lemma modalStepBranchS4KeyedOrdered_preserves_eNodup (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys'))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  obtain ⟨sf, hsfmem, hsfnotmem, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsfnotmem hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hnodup
  · rw [hres] at hsf; simp at hsf

/-- **`keysWorldsKnown`, a proof-internal auxiliary invariant** (not an `S4LoopInv` field: adding
one would reopen the already-finalized struct design): every RECORDED key's world is
already a known world of the branch. Not literally implied by any single `S4LoopInv` field
(`keysTotal` only gives the converse direction), but true by construction -- `keys` only ever
gains an entry `(modalNextWorld b, ...)` in the SAME step that mints the branch formula carrying
that exact label, so the keyed world is known from the moment its key is recorded onward. Needed
by `accFresh`/`accKnown`'s preservation, whose guard-BLOCKED minting sub-case adds an edge to
`blockingWorldS4Keyed`'s result `wBlock` -- a RECORDED-key world, not necessarily K's usual
"freshly-minted" witness, so the standard `hFreshLocal`-style dichotomy (nonempty `.linear`
headed by the fresh witness) does not apply; `wBlock ∈ modalKnownWorlds b` is what closes the
gap instead. Threaded as an extra hypothesis/conclusion alongside `S4LoopInv` at every call site
(including the final assembly), exactly like `RuleApplicationSpec`-style raw hypotheses
elsewhere in this development. -/
lemma modalStepBranchS4_preserves_keysWorldsKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b' := by
    intro b' hb' w k hwk
    obtain ⟨sf', hsf', hlab⟩ := (mem_modalKnownWorlds b w).mp (hKW w k hwk)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf', hlab⟩
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`keysWorldsKnown`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keysWorldsKnown` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem`/`modalStepBranchS4KeyedOrdered_branch_superset` in
place of their unordered counterparts. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysWorldsKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b' := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b' := by
    intro b' hb' w k hwk
    obtain ⟨sf', hsf', hlab⟩ := (mem_modalKnownWorlds b w).mp (hKW w k hwk)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf', hlab⟩
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-! ### Origin-Edge Invariant — Step Preservation

`keysOriginS4` (defined above, alongside its entry and monotonicity lemmas) survives a single
`modalStepBranchS4Keyed`/`modalStepBranchS4KeyedOrdered` step, over every branch produced.
Mirrors `keysWorldsKnown`'s preservation shape (proof-internal auxiliary, threaded as an extra
hypothesis/conclusion, never an `S4LoopInv` field): twelve of the fourteen `sf.sign`/
`sf.formula` shapes are free -- `modalApplyOneS4Keyed_nonMint_snd_eq_acc` gives `newAcc = acc`
outright and the `keys'`-defining match falls to its `_, _ => keys` catch-all -- so
`keysOriginS4_mono_branch`/`_mono_acc` alone close them. The blocked-mint sub-case adds an edge
but no key, closed the same way via a direct `Accessibility.addEdge`/`hasEdge` unfolding. Only
the unblocked-mint sub-case establishes a genuinely new key, by construction: the new entry is
`(modalNextWorld b, successorBirthContent φ₀ b s φ v)`, born together with the freshly-added
edge `v → modalNextWorld b`, so `u := v` and the witness pair is `(s, φ)` itself -- exactly the
`insert (s, φ) (...)` head of `successorBirthContent`. -/

/-- **`keysOriginS4`'s single-step preservation.** -/
lemma modalStepBranchS4Keyed_preserves_keysOriginS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (haK : accTargetsKnown b acc)
    (hKO : keysOriginS4 b acc keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, keysOriginS4 b' newAcc keys' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- box-negative minting shape
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .neg, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
    · -- diamond-positive minting shape (symmetric)
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .pos, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
  · -- non-mint: keys' = keys, newAcc = newAcc0 = acc, regardless of which of the 12 shapes fired
    rw [hpair] at hsf
    dsimp only at hsf
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnewAcc0eq : newAcc0 = acc :=
      (congrArg Prod.snd hpair).symm.trans
        (modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem haK hnbd)
    have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
      rw [hnewAcc0eq]; exact fun u w h => h
    have hold : ∀ b' ∈ newBs, keysOriginS4 b' newAcc0 keys := fun b' hb' =>
      keysOriginS4_mono_acc b' acc newAcc0 keys haccsub
        (keysOriginS4_mono_branch b b' acc keys (hsuper b' hb') hKO)
    have hkeq0 := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have haccEq := modalStepBranchS4Keyed_result_acc_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have hkeq : keys' = keys := by
      rw [hkeq0]
      rcases hs : sf.sign with _ | _ <;>
        rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
    intro b' hb'
    rw [haccEq, hkeq]
    exact hold b' hb'

/-- **`keysOriginS4`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4Keyed_preserves_keysOriginS4` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem`/`modalStepBranchS4KeyedOrdered_branch_superset` in
place of their unordered counterparts. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysOriginS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (haK : accTargetsKnown b acc)
    (hKO : keysOriginS4 b acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, keysOriginS4 b' newAcc keys' := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- box-negative minting shape
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .neg, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
    · -- diamond-positive minting shape (symmetric)
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .pos, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
  · -- non-mint: keys' = keys, newAcc = newAcc0 = acc, regardless of which of the 12 shapes fired
    rw [hpair] at hsf
    dsimp only at hsf
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnewAcc0eq : newAcc0 = acc :=
      (congrArg Prod.snd hpair).symm.trans
        (modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem haK hnbd)
    have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
      rw [hnewAcc0eq]; exact fun u w h => h
    have hold : ∀ b' ∈ newBs, keysOriginS4 b' newAcc0 keys := fun b' hb' =>
      keysOriginS4_mono_acc b' acc newAcc0 keys haccsub
        (keysOriginS4_mono_branch b b' acc keys (hsuper b' hb') hKO)
    have hkeq0 := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have haccEq := modalStepBranchS4Keyed_result_acc_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have hkeq : keys' = keys := by
      rw [hkeq0]
      rcases hs : sf.sign with _ | _ <;>
        rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
    intro b' hb'
    rw [haccEq, hkeq]
    exact hold b' hb'

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `Soundness.lean`'s `private lemma accFreshInv_append` (unavailable
across files): prepending formulas to a branch preserves `accFreshInv`. -/
private lemma accFreshInv_append_S4
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (hInv : accFreshInv b acc)
    (xs : List (SignedFormula (Proposition Atom) WorldIndex)) :
    accFreshInv (xs ++ b) acc := by
  intro w w' hedge
  obtain ⟨hw, hw'⟩ := hInv w w' hedge
  exact ⟨Nat.lt_of_lt_of_le hw (modalNextWorld_le_append xs b),
         Nat.lt_of_lt_of_le hw' (modalNextWorld_le_append xs b)⟩

/-- **`accFresh`'s driver-level preservation**: the per-branch freshness invariant `accFreshInv`
survives an S4Keyed step. At the 12 non-minting shapes, `acc` is unchanged
(`modalApplyOneS4Keyed_nonMint_snd_eq_acc`) and every produced branch is a prepend of `b`, so
`accFreshInv_append_S4` carries the invariant forward directly. At the 2 minting shapes'
UNBLOCKED sub-case, `modalApplyOneS4Keyed` reduces to plain K's `modalApplyOne`, whose unique new
edge targets the genuinely fresh witness `modalNextWorld b` -- the standard K freshness argument
applies. At the BLOCKED sub-case the new edge targets `wBlock` instead -- NOT necessarily fresh,
so `keysWorldsKnown` (`wBlock ∈ modalKnownWorlds b`, hence `wBlock < modalNextWorld b` via
`modalNextWorld_gt`) is what bounds it, in place of the standard freshness argument. -/
lemma modalStepBranchS4_preserves_accFresh (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hFresh : accFreshInv b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.neg, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.pos, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      exact accFreshInv_append_S4 hFresh x
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf; simp at hsf

/-- **`accFresh`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_accFresh` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction; the
three-regime case split (non-minting / minting-unblocked / minting-blocked) and its
`keysWorldsKnown` dependency at the blocked sub-case are otherwise unchanged. -/
lemma modalStepBranchS4KeyedOrdered_preserves_accFresh (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hFresh : accFreshInv b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.neg, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.pos, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      exact accFreshInv_append_S4 hFresh x
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf; simp at hsf

/-- **`accKnown`'s driver-level preservation**: every `acc`-edge target stays a known branch
world across an S4Keyed step. Mirrors `accFresh`'s case split exactly (same three regimes,
same `keysWorldsKnown` dependency at the BLOCKED sub-case), but concludes membership in
`modalKnownWorlds b'` rather than a numeric bound, via `modalKnownWorlds_mono_append` to lift
old facts across a branch prepend. -/
lemma modalStepBranchS4_preserves_accKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
            hblock)
        · exact hknown w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
            hblock)
        · exact hknown w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf; simp at hsf

/-- **`accKnown`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_accKnown` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction; the
three-regime case split mirrors `accFresh`'s exactly, as in the unordered original. -/
lemma modalStepBranchS4KeyedOrdered_preserves_accKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
            hblock)
        · exact hknown w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
            hblock)
        · exact hknown w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf; simp at hsf

/-! ## Pigeonhole World Bound -/

/-- **Proof-internal auxiliary invariant**: the known worlds of a branch
form the contiguous range `{0, ..., modalMaxWorld b}` -- not an `S4LoopInv` field (would reopen
the finalized struct design), threaded as an extra hypothesis/conclusion alongside the
struct at every call site, exactly like `keysWorldsKnown`. Holds by construction: the driver
only ever mints the SINGLE next integer `modalNextWorld b = modalMaxWorld b + 1`, never skipping
a label -- this is the "worlds are consecutive from 0" fact `modalStepBranchS4_worldBound`
converts a pigeonhole *length* bound into a STRICT `modalMaxWorld` bound with. -/
def worldsContiguousS4 (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Prop :=
  ∀ w, w ≤ modalMaxWorld b → w ∈ modalKnownWorlds b

/-- `worldsContiguousS4`'s driver-level preservation: mirrors `keysWorldsKnown`'s assembly shape
(top split on minting vs. non-minting, reusing `modalStepBranchS4Keyed_branch_superset` for the
"old worlds carry over" half). At the 12 non-minting shapes, every emitted formula's label is
already a known world of `b` (`modalApplyOneS4Keyed_nonMint_known_S4`), so `modalMaxWorld`
cannot grow. At the 2 minting UNBLOCKED shapes, every emitted formula's label is exactly
`modalNextWorld b` (`mintGroup_label_eq_freshWorld`), so `modalMaxWorld` grows by exactly the
one new label, which is directly known via the witness formula's own membership. At the BLOCKED
sub-case, `result = .linear []` so the branch is unchanged. -/
lemma modalStepBranchS4_preserves_worldsContiguousS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b) (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, worldsContiguousS4 b' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b' := by
    intro b' hb' w hw
    obtain ⟨sf', hsf'mem, hlab⟩ := (mem_modalKnownWorlds b w).mp (hWC w hw)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf'mem, hlab⟩
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb'
    have hmaxle : modalMaxWorld b' ≤ modalMaxWorld b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ := (mem_modalKnownWorlds b sf''.label).mp
            (hnm sf'' (List.mem_flatten.mpr ⟨br, hbr, hnew⟩))
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf; simp at hsf
    intro w hw
    exact hold b' hb' w (le_trans hw hmaxle)

/-- **`worldsContiguousS4`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_worldsContiguousS4` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem`/`modalStepBranchS4KeyedOrdered_branch_superset` in
place of their unordered counterparts; the top-level minting/non-minting split and its
sub-arguments are otherwise unchanged. -/
lemma modalStepBranchS4KeyedOrdered_preserves_worldsContiguousS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b) (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, worldsContiguousS4 b' := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b' := by
    intro b' hb' w hw
    obtain ⟨sf', hsf'mem, hlab⟩ := (mem_modalKnownWorlds b w).mp (hWC w hw)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf'mem, hlab⟩
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb'
    have hmaxle : modalMaxWorld b' ≤ modalMaxWorld b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ := (mem_modalKnownWorlds b sf''.label).mp
            (hnm sf'' (List.mem_flatten.mpr ⟨br, hbr, hnew⟩))
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf; simp at hsf
    intro w hw
    exact hold b' hb' w (le_trans hw hmaxle)

omit [Hashable Atom] in
/-- **The pigeonhole cardinality bound**: the number of known worlds of a branch is
bounded by `modalWorldBoundS4 φ₀`. Injects known worlds into `keys` via `keysTotal`, injectivity
via `keysDistinct`, codomain bound via `keysInUniverse` + `signedSubfmls_powerset_card_le`,
cardinality via `Finset.card_le_card_of_injOn`. -/
lemma modalKnownWorlds_length_le_worldBoundS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀ := by
  classical
  set f : WorldIndex → Finset (Sign × Proposition Atom) :=
    fun w => if hw : w ∈ modalKnownWorlds b then (hKT w hw).choose else ∅ with hf
  have hmapsto : ∀ w ∈ (modalKnownWorlds b).toFinset, f w ∈ (signedSubfmls φ₀).powerset := by
    intro w hw
    rw [List.mem_toFinset] at hw
    simp only [hf, dif_pos hw]
    rw [Finset.mem_powerset]
    exact hKI w _ (hKT w hw).choose_spec
  have hinj : Set.InjOn f (modalKnownWorlds b).toFinset := by
    intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_coe, List.mem_toFinset] at hw1 hw2
    by_contra hne
    have hk1 : (w1, f w1) ∈ keys := by
      simp only [hf, dif_pos hw1]; exact (hKT w1 hw1).choose_spec
    have hk2 : (w2, f w2) ∈ keys := by
      simp only [hf, dif_pos hw2]; exact (hKT w2 hw2).choose_spec
    exact (hKD w1 w2 (f w1) (f w2) hk1 hk2 hne) heq
  have hcard := Finset.card_le_card_of_injOn f hmapsto hinj
  rw [List.toFinset_card_of_nodup (modalKnownWorlds_nodup b)] at hcard
  calc (modalKnownWorlds b).length ≤ (signedSubfmls φ₀).powerset.card := hcard
    _ ≤ modalWorldBoundS4 φ₀ := signedSubfmls_powerset_card_le φ₀

omit [Hashable Atom] in
/-- **`modalStepBranchS4_worldBound`**: the
STRICT world bound `modalMaxWorld b < modalWorldBoundS4 φ₀`, the deliverable that makes any
fresh mint's label (`modalNextWorld b = modalMaxWorld b + 1`) stay within `modalWorldBoundS4`'s
fixed range. Combines the pigeonhole length bound
(`modalKnownWorlds_length_le_worldBoundS4`) with the density fact `worldsContiguousS4` provides:
`{0, ..., modalMaxWorld b} ⊆ modalKnownWorlds b`, so `modalMaxWorld b + 1 ≤
(modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀`. -/
lemma modalStepBranchS4_worldBound (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    modalMaxWorld b < modalWorldBoundS4 φ₀ := by
  have hlen := modalKnownWorlds_length_le_worldBoundS4 φ₀ b keys hKT hKD hKI
  have hsub : (List.range (modalMaxWorld b + 1)).toFinset ⊆ (modalKnownWorlds b).toFinset := by
    intro w hw
    rw [List.mem_toFinset, List.mem_range] at hw
    rw [List.mem_toFinset]
    exact hWC w (Nat.lt_succ_iff.mp hw)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup List.nodup_range,
      List.toFinset_card_of_nodup (modalKnownWorlds_nodup b), List.length_range] at hcard
  calc modalMaxWorld b < modalMaxWorld b + 1 := Nat.lt_succ_self _
    _ ≤ (modalKnownWorlds b).length := hcard
    _ ≤ modalWorldBoundS4 φ₀ := hlen

/-! ## Sanity Checks

`modalTableauS4` was confirmed to evaluate and close exactly on the T and 4 components via
an interactive `#eval` session (not embedded in this file as a permanent `#eval`/`#guard`/
`native_decide` declaration: this file's `module`/`public meta import` boundary makes all
three of those forms either fail to elaborate (`Proposition.atom` is not `meta`-accessible
without an additional `public meta import`) or fail at the native-code-lookup stage
(`modalFuel`'s compiled implementation is not resolvable in this configuration) -- no
existing file in `Cslib/Logics/Modal/Tableau/` uses any of these forms, confirming this is a
structural constraint of the module system here, not specific to this phase's code).
Confirmed interactively:
- `□p → p` (the T schema) evaluates to `.closed`: S4 is reflexive.
- `□p → □□p` (the 4 schema) evaluates to `.closed`: S4 is transitive -- this is the
  component that distinguishes S4 from T, and the entire reason this task's 4-rule exists.
- A bare atom `p` evaluates to `.openBranch _ _`: S4 does not prove arbitrary atoms. -/

/-! ## The S4 Loop Invariant `S4LoopInv` -/

/-- **Correction 1**: `S4LoopInv` is a **sibling** of `ModalPotentialInv` (`FmpMeasure.lean`),
not an extension of it. `ModalPotentialInv` holds two rank fields (`rankBound`/`rankEdge`)
encoding "modal depth strictly decreases along every edge", which the 4-rule (placing
`T(□ψ)`, unchanged modal depth, at a successor) and loop-back edges (creating `w → w''`
with `rank w'' + 2 = rank w`) both falsify. `S4LoopInv` reuses the five rule-independent
fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`, over
`modalUniverseS4` in place of `modalUniverse`), omits the two rank fields entirely, and adds
the four **stable birth-key** fields (replacing the structurally-unsound
`worldSetsDistinct`): `keysTotal`/`keyLowerBd`/`keysDistinct`/`keysInUniverse`, stated over
the threaded `keys` list (`modalStepBranchS4Keyed`) rather than the live branch. `keys` never
changes after a world is born and each key only ever lower-bounds a monotonically-growing live
relevant set, so this invariant survives every step (Gap 1), and `keysDistinct` is exactly
what the birth-content guard `blockingWorldS4` enforces at minting time (Gap 2).
`FmpMeasure.lean` is not modified here. -/
structure S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every branch formula is a member of the fixed finite S4 universe `U_{S4}(φ₀)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀
  /-- The expanded set has no duplicate entries. -/
  eNodup : e.Nodup
  /-- Every expanded-set formula is a member of `U_{S4}(φ₀)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- Every known world has a recorded birth key. -/
  keysTotal : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys
  /-- **Survives Gap 1**: a world's recorded birth key is a LOWER BOUND on its live relevant
  set. This is monotone-stable -- birth keys never change after a world is born, and live
  relevant sets only grow (`relevantSetFinset_mono`) -- unlike the old `worldSetsDistinct`,
  which compared live sets directly and so could be falsified by a later persistent step. -/
  keyLowerBd : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w
  /-- **Fixes Gap 2**: distinct worlds have DISTINCT birth keys. This is exactly what the
  redesigned guard (`blockingWorldS4`) enforces at minting time (`blockingWorldS4_none_fresh`),
  and no later step can violate it since keys themselves never change. This is the hypothesis
  the pigeonhole argument (`modalKnownWorlds_length_le_worldBoundS4`, below) consumes. -/
  keysDistinct : ∀ w w' k k', (w, k) ∈ keys → (w', k') ∈ keys → w ≠ w' → k ≠ k'
  /-- Birth keys are drawn from the powerset of the finite signed-subformula codomain
  `signedSubfmls φ₀`: the pigeonhole argument's injection target (below). -/
  keysInUniverse : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀

/-! ## `bClosure`/`eClosure` (both fully closed)

Both remaining `S4LoopInv` fields, closed:

- **`eClosure`** turned out to be immediate: `modalStepBranchS4Keyed`'s `newExps` component is
  `e ++ [sf]` (or `e` unchanged for `.persistent`) -- it only ever gains the *selected* formula
  `sf` (already `∈ b`, hence covered directly by `hb`), never the rule's output content (that
  goes to `newBs`, `bClosure`'s concern).
- **`bClosure`** needed exactly that formula-subset composite (`modalApplyOneS4Keyed_nonMint_
  universe_S4` and its supporting T-augmented/S4Rules-augmented pieces, "Non-Minting
  Universe-Membership Composite" section above) for its 12 non-minting shapes, plus the
  pigeonhole world-bound deliverable (`modalStepBranchS4_worldBound`, "Pigeonhole World
  Bound" section above) as a genuine PREREQUISITE for its 2 minting shapes: the newly-minted
  witness's label (`modalNextWorld b = modalMaxWorld b + 1`) needs the STRICT bound
  `modalMaxWorld b < modalWorldBoundS4 φ₀` to hold on the PRE-step branch `b`, which is exactly
  what `modalStepBranchS4_worldBound` supplies (consuming a new proof-internal auxiliary
  invariant `worldsContiguousS4`, threaded the same way as `keysWorldsKnown`). -/

/-- **`eClosure`'s driver-level preservation**: closes directly via the same case-split shape as
`modalStepBranchS4_preserves_eNodup` -- `newExps`'s only new content is the selected formula
`sf`, already in `b` and hence covered by `hb`. -/
lemma modalStepBranchS4_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀)
    (_hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS4 φ₀ := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfbound : sf ∈ modalUniverseS4 φ₀ := hb sf hsfmem
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x0, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hres] at hsf; simp at hsf

/-- **`eClosure`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_eClosure` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. -/
lemma modalStepBranchS4KeyedOrdered_preserves_eClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀)
    (_hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverseS4 φ₀ := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  have hsfbound : sf ∈ modalUniverseS4 φ₀ := hb sf hsfmem
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x0, -, rfl⟩ := List.mem_map.mp he'
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact heclosure x hx
    · exact hsfbound
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact heclosure
  · rw [hres] at hsf; simp at hsf

/-- **`bClosure`'s driver-level preservation**: at the 12 non-minting shapes, the "Non-Minting
Universe-Membership Composite" section's `modalApplyOneS4Keyed_nonMint_universe_S4` bounds
emitted content directly; at the 2 minting shapes, the pigeonhole world-bound
(`modalStepBranchS4_worldBound`, consuming `worldsContiguousS4`) supplies the STRICT
`modalMaxWorld b < modalWorldBoundS4 φ₀` bound `modalApplyOne_boxNeg_outputs_subset_S4`/
`modalApplyOne_diamondPos_outputs_subset_S4` need to place the freshly-minted witness in
range. -/
lemma modalStepBranchS4_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS4 φ₀ := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem'
          hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' x hx
    rcases hres : result with lf | brs | lf | -
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x (List.mem_flatten.mpr ⟨br, hbr, hxnew⟩)
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf; simp at hsf

/-- **`bClosure`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_bClosure` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. The
pigeonhole world-bound prerequisite `modalStepBranchS4_worldBound` is consumed UNCHANGED: it is
stated purely over the pre-step `b`/`keys`, independent of which traversal produced the step, so
no ordered analogue of it is needed. -/
lemma modalStepBranchS4KeyedOrdered_preserves_bClosure (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ x ∈ b', x ∈ modalUniverseS4 φ₀ := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hcontent := modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem'
          hW
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb' x hx
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rcases List.mem_append.mp hx with hxnew | hxold
        · exact hcontent x hxnew
        · exact hb x hxold
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' x hx
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hb x hx
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' x hx
    rcases hres : result with lf | brs | lf | -
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x (List.mem_flatten.mpr ⟨br, hbr, hxnew⟩)
      · exact hb x hxold
    · rw [hres] at hsf hnm
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      rw [← hsf.1] at hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      rcases List.mem_append.mp hx with hxnew | hxold
      · exact hnm x hxnew
      · exact hb x hxold
    · rw [hres] at hsf; simp at hsf

/-- **`modalStepBranchS4_preserves_S4LoopInv`**: every `modalStepBranchS4Keyed` step preserves
`S4LoopInv`, over every
branch/expanded-set pair it produces (any `b' ∈ newBs` paired with any `e' ∈ newExps` -- valid
because `modalStepBranchS4Keyed` never produces distinct `newExps` entries for distinct `newBs`
entries: the `.branching` arm maps EVERY branch to the identical `e ++ [sf]`, and the
`.linear`/`.persistent` arms produce singleton lists of each, so any member of one is
definitionally paired with any member of the other). Also threads and re-establishes TWO
proof-internal auxiliary invariants (neither an `S4LoopInv` field itself, to avoid reopening the
finalized struct design): `keysWorldsKnown` (needed by `accFresh`/`accKnown`) and
`worldsContiguousS4` (needed by `bClosure`'s own minting-case pigeonhole prerequisite,
`modalStepBranchS4_worldBound`), so repeated steps through this assembly can re-supply both at
each call.

**All nine fields are now fully closed, zero sorry** (`keysDistinct`/`keyLowerBd`/
`keysInUniverse`/`keysTotal`: the four "key" fields; `eNodup`/
`accFresh`/`accKnown`; and `eClosure`/`bClosure`,
`eClosure` directly and `bClosure` via the pigeonhole world-bound
(`modalStepBranchS4_worldBound`) as a genuine prerequisite for its minting-case obligation). -/
theorem modalStepBranchS4_preserves_S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4LoopInv φ₀ b e acc keys)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hWC : worldsContiguousS4 b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    (∀ b' ∈ newBs, ∀ e' ∈ newExps, S4LoopInv φ₀ b' e' newAcc keys') ∧
    (∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b') ∧
    (∀ b' ∈ newBs, worldsContiguousS4 b') := by
  obtain ⟨hbC, heN, heC, haF, haK, hkT, hkL, hkD, hkI⟩ := hinv
  refine ⟨?_, modalStepBranchS4_preserves_keysWorldsKnown φ₀ b e acc keys newBs newExps newAcc
    keys' hKW hstep, modalStepBranchS4_preserves_worldsContiguousS4 φ₀ b e acc keys newBs newExps
    newAcc keys' hWC haK hstep⟩
  intro b' hb' e' he'
  exact
    { bClosure := modalStepBranchS4_preserves_bClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC hWC hkT hkD hkI haK hstep b' hb'
      eNodup := modalStepBranchS4_preserves_eNodup φ₀ b e acc keys newBs newExps newAcc keys'
        hstep heN e' he'
      eClosure := modalStepBranchS4_preserves_eClosure φ₀ b e acc keys newBs newExps newAcc keys'
        hbC heC haK hstep e' he'
      accFresh := modalStepBranchS4_preserves_accFresh φ₀ b e acc keys newBs newExps newAcc keys'
        haK hKW haF hstep b' hb'
      accKnown := modalStepBranchS4_preserves_accKnown φ₀ b e acc keys newBs newExps newAcc keys'
        haK hKW hstep b' hb'
      keysTotal := modalStepBranchS4_preserves_keysTotal φ₀ b e acc keys newBs newExps newAcc
        keys' haK hkT hstep b' hb'
      keyLowerBd := modalStepBranchS4_preserves_keyLowerBd φ₀ b e acc keys newBs newExps newAcc
        keys' hbC hkL hstep b' hb'
      keysDistinct := modalStepBranchS4_preserves_keysDistinct φ₀ b e acc keys newBs newExps
        newAcc keys' hkD hstep
      keysInUniverse := modalStepBranchS4_preserves_keysInUniverse φ₀ b e acc keys newBs newExps
        newAcc keys' hbC hkI hstep }

/-- **`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv`** (originally established for the
ordered driver, later extended with the origin-edge invariant's fourth conjunct): every
`modalStepBranchS4KeyedOrdered`
step preserves `S4LoopInv`, mirroring `modalStepBranchS4_preserves_S4LoopInv` exactly -- a
`refine`+`exact` assembly with no independent proof content of its own, just twelve calls to this
section's ordered per-field sub-lemmas (`modalStepBranchS4KeyedOrdered_preserves_{bClosure,
eNodup,eClosure,accFresh,accKnown,keysTotal,keyLowerBd,keysDistinct,keysInUniverse}`
plus the three proof-internal auxiliaries `modalStepBranchS4KeyedOrdered_preserves_{
keysWorldsKnown,worldsContiguousS4,keysOriginS4}`), each of which was itself verified against the
ordered stepper via `modalStepBranchS4KeyedOrdered_selected_mem` in place of the unordered
`findSome?` extraction. No landed statement (`keysUpdate_preserves_keysDistinct`,
`blockingWorldS4Keyed_none_fresh`, or any individual `S4LoopInv` field) required ANY weakening to
reach this point -- the plan's escalation trigger (`keysDistinct`, attempted first) did not fire,
confirming settled-context scheduling changes only *timing*, never producing a duplicate key or
otherwise degrading any invariant.

**Note**: `keysOriginS4` (like `keysWorldsKnown`/`worldsContiguousS4` before it) is
threaded as an extra hypothesis/conclusion, NOT an `S4LoopInv` field -- the struct itself is
untouched, and the unordered wrapper `modalStepBranchS4_preserves_S4LoopInv` is byte-for-byte
unchanged (this extension applies to the ordered driver only). -/
theorem modalStepBranchS4KeyedOrdered_preserves_S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4LoopInv φ₀ b e acc keys)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hWC : worldsContiguousS4 b)
    (hKO : keysOriginS4 b acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    (∀ b' ∈ newBs, ∀ e' ∈ newExps, S4LoopInv φ₀ b' e' newAcc keys') ∧
    (∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b') ∧
    (∀ b' ∈ newBs, worldsContiguousS4 b') ∧
    (∀ b' ∈ newBs, keysOriginS4 b' newAcc keys') := by
  obtain ⟨hbC, heN, heC, haF, haK, hkT, hkL, hkD, hkI⟩ := hinv
  refine ⟨?_, modalStepBranchS4KeyedOrdered_preserves_keysWorldsKnown φ₀ b e acc keys newBs
    newExps newAcc keys' hKW hstep,
    modalStepBranchS4KeyedOrdered_preserves_worldsContiguousS4 φ₀ b e acc keys newBs newExps
    newAcc keys' hWC haK hstep,
    modalStepBranchS4KeyedOrdered_preserves_keysOriginS4 φ₀ b e acc keys newBs newExps newAcc
    keys' haK hKO hstep⟩
  intro b' hb' e' he'
  exact
    { bClosure := modalStepBranchS4KeyedOrdered_preserves_bClosure φ₀ b e acc keys newBs newExps
        newAcc keys' hbC hWC hkT hkD hkI haK hstep b' hb'
      eNodup := modalStepBranchS4KeyedOrdered_preserves_eNodup φ₀ b e acc keys newBs newExps
        newAcc keys' hstep heN e' he'
      eClosure := modalStepBranchS4KeyedOrdered_preserves_eClosure φ₀ b e acc keys newBs newExps
        newAcc keys' hbC heC haK hstep e' he'
      accFresh := modalStepBranchS4KeyedOrdered_preserves_accFresh φ₀ b e acc keys newBs newExps
        newAcc keys' haK hKW haF hstep b' hb'
      accKnown := modalStepBranchS4KeyedOrdered_preserves_accKnown φ₀ b e acc keys newBs newExps
        newAcc keys' haK hKW hstep b' hb'
      keysTotal := modalStepBranchS4KeyedOrdered_preserves_keysTotal φ₀ b e acc keys newBs
        newExps newAcc keys' haK hkT hstep b' hb'
      keyLowerBd := modalStepBranchS4KeyedOrdered_preserves_keyLowerBd φ₀ b e acc keys newBs
        newExps newAcc keys' hbC hkL hstep b' hb'
      keysDistinct := modalStepBranchS4KeyedOrdered_preserves_keysDistinct φ₀ b e acc keys newBs
        newExps newAcc keys' hkD hstep
      keysInUniverse := modalStepBranchS4KeyedOrdered_preserves_keysInUniverse φ₀ b e acc keys
        newBs newExps newAcc keys' hbC hkI hstep }

/-! ## Keyed S4 Driver (Bespoke, Path (b))

This section closes `Decidable (s4Valid φ)` via a bespoke, S4-specific `keys`-threaded driver,
rather than generalizing the shared generic driver (`Saturation.lean`'s `modalExpandBranchesGen`)
to thread opaque per-branch state -- that path would serve only S4 (K/T/B/S5/Five have all already
reached decidability via the state-free generic driver) while risking every one of their landed
proofs. `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` below mirror
`modalExpandBranchesGen`/`processNext`/`modalTableauGen` structurally (copy-and-thread), with
`keys` (the stable per-world birth-key list `modalStepBranchS4Keyed` already threads) carried as
a fourth parallel worklist column alongside `(branch, expanded, acc)`. The live `modalTableauS4`
is left untouched as the reference artifact the `heq1`-style bridges and `modalHintikkaSetS4_eq`
consume; `instDecidableS4Valid` points at `modalTableauS4Keyed` instead. -/

/-- The keyed S4 modal tableau decision procedure: the entry point for the bespoke keyed driver,
mirroring `modalTableauGen`/`modalTableauS4`'s entry-branch shape (`F(φ)@0`), with
`keys := [(0, ∅)]` at the start: the root world `0` is pre-existing (not minted), so it is seeded
with the trivial (empty) birth key rather than left absent from `keys`. **Correction:**
an earlier version of this entry used `keys := []`; that violates `S4LoopInv.keysTotal` (every
known world has a recorded key) since `0 ∈ modalKnownWorlds [F(φ)@0]` from the very first
formula's label, and no step ever mints world `0` again to backfill a key for it. Seeding `(0, ∅)`
satisfies `keysTotal` trivially (`∅ ⊆ relevantSetFinset φ₀ b 0` and `∅ ⊆ signedSubfmls φ₀` both
hold unconditionally) and is invisible to every lemma established earlier in this file, all of
which are stated for an arbitrary `keys` list. Fuel is `modalFuelS4 φ`, the S4-specific fuel
bound (sufficiency: `modalExpMeasure_entry_le_fuelS4`) -- K's `modalFuel φ` is confirmed NOT
provably sufficient for
the S4 keyed loop's pigeonhole world bound `modalWorldBoundS4`. The live `modalTableauS4` is NOT
redefined; `instDecidableS4Valid` (deferred) would point at this declaration instead. -/
def modalTableauS4Keyed (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranchesS4Keyed φ [initialBranch] [[]] [Accessibility.empty]
    [[(0, (∅ : Finset (Sign × Proposition Atom)))]] (modalFuelS4 φ)

/-- **Entry-point corollary, closing the `RuleApplySt` ladder story end-to-end.**
`modalTableauS4Keyed` -- the keyed S4 decision procedure's entry point -- equals the generic
state-threaded entry-point machinery (`modalExpandBranchesGenSt`) instantiated at the keyed
`RuleApplySt` rule `modalApplyOneS4KeyedSt φ`, at the same initial branch/accessibility/keys and
the same `modalFuelS4 φ` fuel bound. This cannot route through `modalTableauGenSt`
(`Saturation.lean`) instead, because that entry point hardwires K's `modalFuel φ`, whereas the S4
keyed loop needs `modalFuelS4 φ` for its pigeonhole world bound `modalWorldBoundS4` -- K's fuel is
confirmed NOT provably sufficient here (see `modalTableauS4Keyed`'s own docstring above). No fuel
parameter is added to `modalTableauGenSt`, and `modalTableauGen_eq_St` is untouched. -/
theorem modalTableauS4Keyed_eq_modalExpandBranchesGenSt (φ : Proposition Atom) :
    modalTableauS4Keyed φ =
      modalExpandBranchesGenSt (modalApplyOneS4KeyedSt φ)
        [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[(0, (∅ : Finset (Sign × Proposition Atom)))]]
        (modalFuelS4 φ) := by
  unfold modalTableauS4Keyed
  rw [modalExpandBranchesGenSt_eq_S4Keyed]

/-! ## Ordered Keyed S4 Driver and Entry Point (Successor to the Bespoke Driver Above)

Structural copies of `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` above, with the reordered
stepper `modalStepBranchS4KeyedOrdered` (settled-context scheduling: non-minting candidates
first, minting fallback only once the branch has settled) substituted for
`modalStepBranchS4Keyed` at the single per-branch step call. Termination of the copied `fuel'`
recursion is not a new obligation here: the existing measure lemma
(`modalExpMeasure_step_lt_S4KeyedOrdered`) already establishes strict decrease for the ordered
stepper's `some` case, and the `processNext` recursion shape (structural recursion on the outer
`fuel`, exactly as in `modalExpandBranchesS4Keyed`) is unchanged from the original, so Lean's
termination checker accepts the copy identically. `modalStepBranchS4Keyed`,
`modalExpandBranchesS4Keyed`, and `modalTableauS4Keyed` themselves are left untouched pending
Phase 15's destructive retirement, once every consumer below has an ordered replacement. -/

/-- The ordered-stepper analogue of `modalTableauS4Keyed`: the entry point for the settled-context
scheduling driver, mirroring its predecessor's entry-branch shape (`F(φ)@0`) and seeding exactly
`keys := [(0, ∅)]` -- **not** `keys := []`, per the correction at `modalTableauS4Keyed`
above (an empty `keys` list violates `S4LoopInv.keysTotal`, since `0 ∈ modalKnownWorlds [F(φ)@0]`
from the first formula's label and no step re-mints world `0` to backfill a key for it). Fuel is
the same S4-specific bound `modalFuelS4 φ` used by `modalTableauS4Keyed`
(`modalExpMeasure_entry_le_fuelS4` was confirmed to apply verbatim to the ordered
driver, independent of traversal order). Successor to `modalTableauS4Keyed`, which Phase 15
retires once this entry point has a proved soundness/completeness pair of its own. -/
def modalTableauS4KeyedOrdered (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranchesS4KeyedOrdered φ [initialBranch] [[]] [Accessibility.empty]
    [[(0, (∅ : Finset (Sign × Proposition Atom)))]] (modalFuelS4 φ)

/-! ## Keyed-Driver Termination Measure: Combinatorial Primitives

Territory-local re-derivations of the four generic `List.countP`-based combinatorial facts
underpinning the per-step measure decrease (`FmpMeasure.lean:2788-2922`). Those originals are
`private` and hence unreachable from this file; since the keyed S4 driver's territory is
additive-only within `LoopChecking.lean` (not an edit to `FmpMeasure.lean`), the four lemmas are
re-derived here verbatim (same proofs, `_S4`-suffixed names) rather than exposed upstream. -/

/-! ## Keyed-Driver Termination Measure: Per-Call Obligations for `modalApplyOneS4Keyed`

The three raw measure-step hypotheses (`hBranchingLength`/`hPersistentFresh`/
`hOutputsSubsetUniverse`, the shape consumed by `modalExpMeasure_step_lt_gen`,
`FmpMeasure.lean:3227-3246`) as S4Keyed analogues, each universally quantified over `keys` so a
single lemma serves every fuel step. Built by the same mint-blocked/mint-unblocked/non-mint case
split as `modalStepBranchS4_preserves_bClosure`. The T-rule/4-rule propagation arms
(`modalTBoxSelf`/`modalTDiaNegSelf`/`modalFourBoxProp`/`modalFourDiaNegProp`, `FrameRules.lean`)
never appear in K's own dispatch, so their persistent-freshness is new content, established here
via their shared filter-guard shape (mirroring `diamondNeg_filterMap_fresh`,
`FmpMeasure.lean:3032`). -/

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness/freshness for `modalApplyOneT`** (T-augmented K): whenever
`modalApplyOneT sf b acc` produces a `.persistent` result, the emitted formulas are nonempty and
fresh. At the two T-relevant shapes (`T(□φ)@w`/`F(◇φ)@w`), composes K's own
`modalApplyOne_persistent_props` with `modalTBoxSelf_fresh`/`modalTDiaNegSelf_fresh`; at every
other shape `modalApplyOneT` reduces to `modalApplyOne` directly
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so K's fact applies unchanged. -/
lemma modalApplyOneT_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneT sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneT at hca
    dsimp only at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
      have hself := modalTBoxSelf_fresh b ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
      · intro x hx
        rw [← hca] at hx
        rcases List.mem_append.mp hx with hxk | hxs
        · exact hkfresh x hxk
        · exact hself x (List.mem_of_mem_filter hxs)
    · rw [hk] at hca
      dsimp only at hca
      split_ifs at hca with hemp
      · simp only [RuleResult.persistent.injEq] at hca
        refine ⟨?_, ?_⟩
        · rw [← hca]; simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
        · intro x hx; rw [← hca] at hx; exact modalTBoxSelf_fresh b ψ sf.label x hx
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneT at hca
      dsimp only at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
        have hself := modalTDiaNegSelf_fresh b ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
        · intro x hx
          rw [← hca] at hx
          rcases List.mem_append.mp hx with hxk | hxs
          · exact hkfresh x hxk
          · exact hself x (List.mem_of_mem_filter hxs)
      · rw [hk] at hca
        dsimp only at hca
        split_ifs at hca with hemp
        · simp only [RuleResult.persistent.injEq] at hca
          refine ⟨?_, ?_⟩
          · rw [← hca]; simp only [Bool.not_eq_true] at hemp
            exact List.isEmpty_eq_false_iff.mp hemp
          · intro x hx; rw [← hca] at hx; exact modalTDiaNegSelf_fresh b ψ sf.label x hx
    · have heq : modalApplyOneT sf b acc = modalApplyOne sf b acc :=
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

omit [Hashable Atom] in
/-- **Branching-length for `modalApplyOneT`**: `modalApplyOneT` never introduces branching at
the two T-relevant shapes (K's own dispatch is `persistent`/`notApplicable` only there, and the
T-merge never turns either into `.branching`), so any `.branching` result must come from the
`_,_` fallthrough, i.e. from `modalApplyOne` directly, where K's own
`modalApplyOne_branching_length` applies. -/
lemma modalApplyOneT_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneT sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneT at hca
    dsimp only at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      dsimp only at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOne_branching_length _ b acc kbrs hk
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      dsimp only at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneT at hca
      dsimp only at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        dsimp only at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOne_branching_length _ b acc kbrs hk
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        dsimp only at hca
        split_ifs at hca
    · have heq : modalApplyOneT sf b acc = modalApplyOne sf b acc :=
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness/freshness for `modalApplyOneS4Rules`** (T+4-augmented K):
same recipe as `modalApplyOneT_persistentFresh`, one layer up -- composes
`modalApplyOneT_persistentFresh` with `modalFourBoxProp_fresh`/`modalFourDiaNegProp_fresh` at the
two 4-relevant shapes, and reduces to `modalApplyOneT` directly elsewhere
(`modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`). -/
private lemma modalApplyOneS4Rules_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneS4Rules sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneS4Rules at hca
    dsimp only at hca
    rcases ht : (modalApplyOneT (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨htf, htfresh⟩ := modalApplyOneT_persistentFresh _ b acc tf ht
      have hfour := modalFourBoxProp_fresh b acc ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil htf _
      · intro x hx
        rw [← hca] at hx
        rcases List.mem_append.mp hx with hxt | hxs
        · exact htfresh x hxt
        · exact hfour x (List.mem_of_mem_filter hxs)
    · rw [ht] at hca
      dsimp only at hca
      split_ifs at hca with hemp
      · simp only [RuleResult.persistent.injEq] at hca
        refine ⟨?_, ?_⟩
        · rw [← hca]; simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
        · intro x hx; rw [← hca] at hx; exact modalFourBoxProp_fresh b acc ψ sf.label x hx
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneS4Rules at hca
      dsimp only at hca
      rcases ht : (modalApplyOneT (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨htf, htfresh⟩ := modalApplyOneT_persistentFresh _ b acc tf ht
        have hfour := modalFourDiaNegProp_fresh b acc ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil htf _
        · intro x hx
          rw [← hca] at hx
          rcases List.mem_append.mp hx with hxt | hxs
          · exact htfresh x hxt
          · exact hfour x (List.mem_of_mem_filter hxs)
      · rw [ht] at hca
        dsimp only at hca
        split_ifs at hca with hemp
        · simp only [RuleResult.persistent.injEq] at hca
          refine ⟨?_, ?_⟩
          · rw [← hca]; simp only [Bool.not_eq_true] at hemp
            exact List.isEmpty_eq_false_iff.mp hemp
          · intro x hx; rw [← hca] at hx
            exact modalFourDiaNegProp_fresh b acc ψ sf.label x hx
    · have heq : modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc :=
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOneT_persistentFresh sf b acc nf hca

omit [Hashable Atom] in
/-- **Branching-length for `modalApplyOneS4Rules`**: same argument as
`modalApplyOneT_branchingLength`, one layer up. -/
private lemma modalApplyOneS4Rules_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneS4Rules sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneS4Rules at hca
    dsimp only at hca
    rcases ht : (modalApplyOneT (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      dsimp only at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOneT_branchingLength _ b acc tbrs ht
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      dsimp only at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneS4Rules at hca
      dsimp only at hca
      rcases ht : (modalApplyOneT (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        dsimp only at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOneT_branchingLength _ b acc tbrs ht
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        dsimp only at hca
        split_ifs at hca
    · have heq : modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc :=
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOneT_branchingLength sf b acc brs hca

/-- **`hPersistentFresh` obligation for `modalApplyOneS4Keyed`**, for any `keys`: mint-blocked
gives `.linear []` (vacuous, never `.persistent`); mint-unblocked reduces to raw `modalApplyOne`
(K's own `modalApplyOne_persistent_props` applies directly); non-mint reduces to
`modalApplyOneS4Rules` (`modalApplyOneS4Rules_persistentFresh` applies). -/
private lemma modalApplyOneS4Keyed_persistentFresh_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd] at hca
    by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exact modalApplyOneS4Rules_persistentFresh sf b acc nf hca
    · have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
      rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd2,
          modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd2] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

/-- **`hBranchingLength` obligation for `modalApplyOneS4Keyed`**, for any `keys`: same
mint-blocked/mint-unblocked/non-mint split as `modalApplyOneS4Keyed_persistentFresh_S4`. -/
private lemma modalApplyOneS4Keyed_branchingLength_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd] at hca
    by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exact modalApplyOneS4Rules_branchingLength sf b acc brs hca
    · have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
      rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd2,
          modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd2] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

/-- **`hOutputsSubsetUniverse` obligation for `modalApplyOneS4Keyed`**, assembled from the
mint-unblocked outputs-subset facts (`modalApplyOne_boxNeg_outputs_subset_S4`/
`modalApplyOne_diamondPos_outputs_subset_S4`, needing the STRICT world bound `hW`, supplied by
`modalStepBranchS4_worldBound`), the vacuous mint-blocked case, and the already-landed
`modalApplyOneS4Keyed_nonMint_universe_S4` for the 12 non-minting shapes. Mirrors
`modalStepBranchS4_preserves_bClosure`'s case split exactly, concluding the raw universe-subset
match fact instead of branch-closure. -/
private lemma modalApplyOneS4Keyed_outputsSubsetUniverse_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀) (hsfmem : sf ∈ b)
    (hknown : accTargetsKnown b acc)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (match (modalApplyOneS4Keyed φ₀ keys sf b acc).fst with
      | .linear fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .branching brs => ∀ x ∈ brs.flatten, x ∈ modalUniverseS4 φ₀
      | .persistent fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True) := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
    rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label)]
        exact modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2]; simp
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label)]
        exact modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2]; simp
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    exact modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd

/-! ## Keyed-Driver Termination Measure: Entry-Measure Sufficiency for `modalFuelS4`

`modalFuel φ₀` (K's fuel) is confirmed NOT provably sufficient for the S4 keyed loop: at
`modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ = 2 ^ (2 * 1) = 4` exceeds K's
`modalWorldBound φ₀ = 1`. The dedicated `modalFuelS4` (defined earlier, alongside
`modalWorldBoundS4`/`modalUniverseS4`, so it is in scope for `modalTableauS4Keyed`'s fuel
argument) is shown sufficient here, mirroring `modalExpMeasure_entry_le_fuel`
(`FmpMeasure.lean:208-251`). -/

omit [Hashable Atom] in
/-- **Entry-measure sufficiency for `modalFuelS4`**: at the S4 keyed tableau's entry point, the
worklist measure over `modalUniverseS4 φ₀` is bounded by `modalFuelS4 φ₀`. Direct transcription
of `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:208-251`), substituting `modalUniverseS4`/
`modalWorldBoundS4`/`modalUniverseS4_length_le` for their K counterparts -- the
`modalWork ≤ 2 * U.length` step is universe-agnostic (`List.countP_le_length` + `simp` on the
empty expanded-set case), so it transfers verbatim. -/
lemma modalExpMeasure_entry_le_fuelS4 (φ₀ : Proposition Atom) :
    modalExpMeasure (modalUniverseS4 φ₀) [[(⟨.neg, φ₀, 0⟩ :
      SignedFormula (Proposition Atom) WorldIndex)]] [[]] ≤ modalFuelS4 φ₀ := by
  have hmeas : modalExpMeasure (modalUniverseS4 φ₀)
      [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      = 3 ^ modalWork (modalUniverseS4 φ₀)
          [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] := by
    simp [modalExpMeasure]
  rw [hmeas]
  have hwork : modalWork (modalUniverseS4 φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 2 * (modalUniverseS4 φ₀).length := by
    unfold modalWork
    have h1 : (modalUniverseS4 φ₀).countP
        (fun sf => !(([(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]).any
          (· == sf))) ≤ (modalUniverseS4 φ₀).length :=
      List.countP_le_length
    have h2 : (modalUniverseS4 φ₀).countP
        (fun sf => !((([] : List (SignedFormula (Proposition Atom) WorldIndex))).any
          (· == sf))) = (modalUniverseS4 φ₀).length := by
      simp
    omega
  have hUlen := modalUniverseS4_length_le φ₀
  have hfinal : modalWork (modalUniverseS4 φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] ≤
      4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by
    have h2U : 2 * (modalUniverseS4 φ₀).length ≤
        2 * (2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) :=
      Nat.mul_le_mul_left 2 hUlen
    have heq : 2 * (2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) =
        4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by ring
    rw [heq] at h2U
    omega
  calc 3 ^ modalWork (modalUniverseS4 φ₀)
        [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 3 ^ (4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) :=
        Nat.pow_le_pow_right (by norm_num) hfinal
    _ = modalFuelS4 φ₀ := rfl

/-! ## Keys-Threaded Hintikka-Tracking Invariant Bundle

The bespoke keys-threaded analogue of the `ModalLoopInvHintikka` bundle
(`CompletenessLoop.lean:293-325`), for `modalApplyOneS4Keyed φ₀ keys`. The frozen `S4LoopInv`
structure (defined above in this file) already carries the universe-closure/keys-bookkeeping
conjuncts (`bClosure`/`eClosure`/`eNodup`/`accFresh`/`accKnown`), so this bundle carries ONLY
the five Hintikka-specific conjuncts
(`hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`), threaded
alongside `S4LoopInv` as a separate ambient hypothesis at each call site rather than duplicating
its fields. -/

/-- **Keys-threaded Hintikka-tracking invariant bundle** for `modalApplyOneS4Keyed φ₀ keys`: the
bespoke analogue of `ModalLoopInvHintikka`'s five Hintikka-specific conjuncts
(`CompletenessLoop.lean:310-325`), carrying ONLY those five fields. The universe-closure/
keys-bookkeeping conjuncts already live in the frozen `S4LoopInv` structure (defined above in this
file) and are threaded as a separate ambient hypothesis at each call site rather than duplicated
here. -/
structure S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e,
    modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys) sf.sign sf.formula sf.label b acc
  /-- Every box-shaped formula in the expanded set `e` has sign `.neg`. -/
  eBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg
  /-- Every `boxNeg`-shaped formula already has a witness successor on the branch. -/
  eBoxNegWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
  /-- Every diamond-shaped formula in the expanded set `e` has sign `.pos`. -/
  eDiamondOnlyPos : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos
  /-- Every `diamondPos`-shaped formula already has a witness successor on the branch. -/
  eDiamondPosWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b

/-- **`S4KeyedHintikkaInv` weakens across branch/accessibility growth** at a FIXED expanded set
`e`: this discharges the Hintikka-tracking invariant's monotonicity obligations directly --
`hintikkaInv` transports via the branch/`acc`-independence of non-box/diamond shapes
(`modalHintikkaClauseGen_lift` fed `modalApplyOneS4Keyed_fst_eq_of_not_box`; box/diamond
shapes are vacuously `True` on both sides), and the two witness-existence fields are permanent
once recorded since `acc`/`b` only grow (`hbsub`/`haccsub`). `eBoxOnlyNeg`/`eDiamondOnlyPos`
mention no `b`/`acc` at all and transport unchanged. This is the building block the
single-step-preservation lemma below composes against the OLD `e`'s facts lifted to the post-step
`(b', acc')`. -/
lemma S4KeyedHintikkaInv_weaken (φ₀ : Proposition Atom)
    (b b' e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hbsub : b ⊆ b')
    (haccsub : ∀ w w', acc.hasEdge w w' = true → acc'.hasEdge w w' = true)
    (hinv : S4KeyedHintikkaInv φ₀ b e acc keys) :
    S4KeyedHintikkaInv φ₀ b' e acc' keys := by
  refine ⟨?_, hinv.eBoxOnlyNeg, ?_, hinv.eDiamondOnlyPos, ?_⟩
  · intro sf hsf
    exact modalHintikkaClauseGen_lift (modalApplyOneS4Keyed φ₀ keys)
      (modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys) sf.sign sf.formula sf.label b b' acc acc'
      hbsub (hinv.hintikkaInv sf hsf)
  · intro sf hsf ψ w hsfeq
    obtain ⟨w', hedge, hwit⟩ := hinv.eBoxNegWitness sf hsf ψ w hsfeq
    exact ⟨w', haccsub w w' hedge, hbsub hwit⟩
  · intro sf hsf ψ w hsfeq
    obtain ⟨w', hedge, hwit⟩ := hinv.eDiamondPosWitness sf hsf ψ w hsfeq
    exact ⟨w', haccsub w w' hedge, hbsub hwit⟩

/-! ## GATE B -- `modalS4Saturated` at a Settled Ordered-Stepper State

Determines whether `modalS4Saturated φ₀ b acc` is available at an INTERMEDIATE ordered-stepper
state -- specifically a settled state (`modalNonMintCandidates φ₀ keys b e acc = []`) where a
blocked step is about to fire. Gate B **PASSES at its cheapest**: the gate lemma closes
sorry-free from `hsettled` + `hHI` + a per-shape keyed/unkeyed congruence argument alone (in the
same spirit as `hintikka_congr_S4`), with no additional invariant field needed. See
`#### Phase 2 Verdict` in `plans/07_canonical-witness-truth-lemma.md`
(`specs/553_s4_loop_guard_soundness_reachability_restriction/`) for the full write-up.

The apparent gap the plan flagged -- `S4KeyedHintikkaInv.hintikkaInv`'s use of
`modalHintikkaClauseGen`, which is vacuous at EVERY box/diamond-shaped formula regardless of
sign, seemingly supplies nothing for the box-positive/diamond-negative (T-self/4-rule) shapes a
member of `e` might have -- turns out not to arise: `S4KeyedHintikkaInv.eBoxOnlyNeg`/
`eDiamondOnlyPos` already force any box/diamond-shaped member of `e` to be exactly one of the two
MINTING shapes (`.neg,.box`/`.pos,.diamond`), which the non-mint-shape hypothesis in scope here
already excludes. So a non-mint-shaped `sf ∈ e` is never box/diamond-shaped at all, and
`hintikkaInv`'s clause gives genuine (non-vacuous) content there, matching `modalS4Saturated`'s
own requirement exactly once the keyed/unkeyed congruence is applied. -/

lemma modalS4Saturated_of_ordered_settled (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hsettled : modalNonMintCandidates φ₀ keys b e acc = [])
    (hHI : S4KeyedHintikkaInv φ₀ b e acc keys) :
    modalS4Saturated φ₀ b acc := by
  intro sf hsfmem
  by_cases hms : modalMintShape sf = true
  · unfold modalMintShape at hms
    rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;> simp_all
  · have hnb : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) := by
      simp only [Bool.not_eq_true] at hms
      rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
        simp_all [modalMintShape]
    by_cases he : sf ∈ e
    · -- `sf ∈ e`: `eBoxOnlyNeg`/`eDiamondOnlyPos` rule out `sf` being box/diamond-shaped at
      -- all, once the two mint shapes are already excluded by `hnb` -- a box-shaped member of
      -- `e` is forced `.neg` (mint-shaped), a diamond-shaped member is forced `.pos`
      -- (mint-shaped), and `hnb` excludes both. So `sf` is a genuinely non-modal shape here,
      -- where `modalHintikkaClauseGen`'s vacuity at box/diamond formulas does not apply and
      -- `hHI.hintikkaInv` supplies real content.
      have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
        unfold modalApplyOneS4Keyed
        rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
          simp_all
      have hclause := hHI.hintikkaInv sf he
      unfold modalHintikkaClauseGen at hclause
      rw [heq1] at hclause
      simp only
      rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
        simp only [hfm] at hclause ⊢ <;>
        first
          | trivial
          | exact hclause
          | (exact absurd (hHI.eBoxOnlyNeg sf he _ hfm) (by simp [hsg]))
          | (exact absurd (hHI.eDiamondOnlyPos sf he _ hfm) (by simp [hsg]))
    · have hdisj := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hsettled sf hsfmem
      have hnotapp : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable := by
        rcases hdisj with hms' | hex | hnotapp'
        · exact absurd hms' hms
        · exact absurd hex he
        · exact hnotapp'
      have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
        unfold modalApplyOneS4Keyed
        rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
          simp_all
      rw [heq1] at hnotapp
      simp only
      rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
        simp_all

/-! ## The `red` Channel: General Infrastructure Retained Post-Gate-B

Route (3) (`Massacci2000` Technique 8.2, subtractive blocking; see this task's plan
`specs/553_s4_loop_guard_soundness_reachability_restriction/plans/
04_subtractive-blocking-red-channel.md`) proposed moving the redirect a blocked minting step
would otherwise justify OUT of `acc` (the soundness-tracked structure) and into a separate,
completeness-only channel `red`, with a bifurcated Hintikka predicate (`modalHintikkaSetS4Sub`)
substituting `accWithReds acc red` for `acc` in the witness/forward-cone conjuncts only.

**Route (3) is dead** (see `plans/04_subtractive-blocking-red-channel.md`):
Decision Gate B refuted the cone-extension lemma the bifurcated predicate's forward-cone
conjuncts require, because the free transfer below (`blockedRedirect_unwrapped_boxPos_mem`/
`blockedRedirect_unwrapped_diaNeg_mem`) yields only an *unwrapped* branch fact at the redirect
target, and unwrapped facts have no persistence mechanism in this tableau's Hintikka apparatus.
`modalHintikkaSetS4Sub`, `modalHintikkaSetS4Sub_saturated`, and `S4KeyedSubHintikkaInv` were
removed as part of the post-Gate-B triage (see plan v4's `#### Post-Gate-B Triage` note); the
route (1) truth-lemma successor plan does not use the `red` channel at all.

What remains below is genuinely route-independent: `Reds` and `accWithReds` are a plain
"accessibility plus a recorded extra-edge list" packaging with no route-specific content, and
`hasEdge_accWithReds_iff` / `reflTransGen_accWithReds_first_red` are general `simp`/path-
decomposition bridges over that packaging. They are retained as minimal support for those two
bridges and for the two sorry-free, standard-axioms-only free-transfer lemmas
(`blockedRedirect_unwrapped_boxPos_mem`/`blockedRedirect_unwrapped_diaNeg_mem`), which route (1)
may reuse. -/

/-- A recorded blocking decision under subtractive blocking: `(source, blockTarget, sign,
witnessFormula)`. Threaded alongside `keys`, read only by the completeness direction. Matches
the probe's working type
(`specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4subtractive3.lean:43`).
-/
@[nolint unusedArguments]
abbrev Reds (Atom : Type*) [DecidableEq Atom] [Hashable Atom] :=
  List (WorldIndex × WorldIndex × Sign × Proposition Atom)

/-- `acc` augmented with every recorded redirect edge from `red`, materialized as a genuine
`Accessibility`. Since `Accessibility` is a bare edge list (`Branch.lean:55-57`), this lets
`extractModelS4` and its five lemmas (`FrameCompleteness.lean:143-189`) be reused verbatim at
`accWithReds acc red` -- no `extractModelS4Sub` is needed. -/
def accWithReds (acc : Accessibility) (red : Reds Atom) : Accessibility :=
  ⟨acc.edges ++ red.map (fun r => (r.1, r.2.1))⟩

/-- Bridge: `accWithReds acc red` has an edge `x → y` iff `acc` already has it, or some recorded
redirect in `red` targets `y` from `x`. -/
theorem hasEdge_accWithReds_iff (acc : Accessibility) (red : Reds Atom) (x y : WorldIndex) :
    (accWithReds acc red).hasEdge x y =
      (acc.hasEdge x y || red.any (fun r => r.1 == x && r.2.1 == y)) := by
  simp only [accWithReds, Accessibility.hasEdge, List.any_append, List.any_map,
    Function.comp_def]

/-! ## Path Decomposition over `accWithReds`

Retained per the post-Gate-B triage as a general fact about the `Reds`/`accWithReds` packaging
above; independent of the now-dead bifurcated Hintikka predicate that originally motivated it
(`plans/04_subtractive-blocking-red-channel.md`). -/

/-- **Path decomposition** for `ReflTransGen (accWithReds acc red)`: a path `w ⤳ u` either stays
entirely inside `acc.hasEdge`, or its first `red`-hop can be isolated -- it decomposes as an
`acc`-only prefix `w ⤳ x`, a recorded redirect `(x, wB, s, φ) ∈ red`, and a residual
`ReflTransGen (accWithReds acc red)`-suffix `wB ⤳ u`. Proved by
`Relation.ReflTransGen.head_induction_on` plus `hasEdge_accWithReds_iff`: the `head` case's own
edge splits (via the bridge) into an `acc`-edge or a `red`-edge; a `red`-edge terminates the
prefix immediately (the residual is exactly the induction's own tail path, no recursion needed),
while an `acc`-edge prepends onto whichever disjunct the inductive hypothesis already produced. -/
lemma reflTransGen_accWithReds_first_red (acc : Accessibility) (red : Reds Atom)
    (w u : WorldIndex)
    (hpath : Relation.ReflTransGen (fun x y => (accWithReds acc red).hasEdge x y = true) w u) :
    Relation.ReflTransGen (fun x y => acc.hasEdge x y = true) w u ∨
    ∃ (x wB : WorldIndex) (s : Sign) (φ : Proposition Atom),
      Relation.ReflTransGen (fun x y => acc.hasEdge x y = true) w x ∧
      (x, wB, s, φ) ∈ red ∧
      Relation.ReflTransGen (fun x y => (accWithReds acc red).hasEdge x y = true) wB u := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | head hedge htail ih =>
    rename_i w' x
    rw [hasEdge_accWithReds_iff] at hedge
    simp only [Bool.or_eq_true] at hedge
    rcases hedge with hacc | hred
    · rcases ih with hleft | ⟨x', wB, s, φ, hpre, hmemred, hsuf⟩
      · exact Or.inl (Relation.ReflTransGen.head hacc hleft)
      · exact Or.inr ⟨x', wB, s, φ, Relation.ReflTransGen.head hacc hpre, hmemred, hsuf⟩
    · obtain ⟨r, hr_mem, hr_eq⟩ := List.any_eq_true.mp hred
      obtain ⟨rw', rx, rs, rphi⟩ := r
      simp only [Bool.and_eq_true, beq_iff_eq] at hr_eq
      obtain ⟨hrw_eq, hrx_eq⟩ := hr_eq
      rw [hrw_eq, hrx_eq] at hr_mem
      exact Or.inr ⟨w', x, rs, rphi, Relation.ReflTransGen.refl, hr_mem, htail⟩

/-! ## Redirect Forward-Cone Free Transfer (Route-Independent Remnant)

Route (3)'s Decision Gate B (`plans/04_subtractive-blocking-red-channel.md`)
refuted the cone-extension lemma that would have let the two free transfers below
propagate beyond the redirect target `wBlock` itself. The two boxed bridge variants
`hintikkaS4_box_pos_reflTransGen_boxed`/`hintikkaS4_dia_neg_reflTransGen_boxed`, and the
forward-cone conjuncts they fed (`S4KeyedSubHintikkaInv.redBoxForwardCone`/`redDiaForwardCone`),
were deleted from the repository in the post-Gate-B triage by commit `c4b33f63` ("revert
red-channel machinery orphaned by Gate B, retain route-independent assets"). **They no longer
exist**: the only remaining occurrences of all four identifiers anywhere under `Cslib/` are the
two prose mentions in this paragraph, so nothing below may be read as depending on them.

Consequence for the bridge count: the `hintikkaS4_*` bridge set in this file is now **8**
declarations, not the ten that existed when this paragraph was first written (the figure of ten
was correct then; `c4b33f63` removed two of them).

```
grep -nE '^(private )?(theorem|lemma) hintikkaS4_' \
  Cslib/Logics/Modal/Tableau/LoopChecking.lean | wc -l
```

Beware a near-miss measurement: counting *distinct identifiers* over the same file returns 11,
because three further `hintikkaS4_*` names occur only in call positions or prose. The declared
bridge set is 8.

The two lemmas below are the surviving reflexive-case fragment: sorry-free,
standard-axioms-only, true statements about the guard, kept because they are genuinely
route-independent and may be reused by the route (1) successor plan. -/

omit [Hashable Atom] in
/-- **Free transfer, box-context half (condition (c))**: near-transcription of
`modalStepBranchS4Keyed_blocked_witness_mem`'s proof. When a minting attempt at `src` is
blocked to `wBlock`, every box-positive formula `T(□χ)@src` already on the branch (with `χ`
`φ₀`-relevant) transfers, UNWRAPPED, to `wBlock`: `T(χ)@wBlock ∈ b`. This is the reflexive
(`u = wBlock`) base case of a forward-cone obligation that does **not** extend to `u` strictly
beyond `wBlock` in the cone (Decision Gate B refuted that extension; see the module doc above).
**Measured 0 failures / 24,314** (condition (c), `specs/553_.../artifacts/s4subtractive3.lean`). -/
lemma blockedRedirect_unwrapped_boxPos_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.pos, χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.pos, .box χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.pos, χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inl ⟨rfl, ?_⟩⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

omit [Hashable Atom] in
/-- **Free transfer, diamond-context half (condition (e))**: dual of
`blockedRedirect_unwrapped_boxPos_mem`. When a minting attempt at `src` is blocked to `wBlock`,
every diamond-negative formula `F(◇χ)@src` already on the branch (with `χ` `φ₀`-relevant)
transfers, UNWRAPPED, to `wBlock`: `F(χ)@wBlock ∈ b`. **Measured 0 failures / 24,314**
(condition (e)). -/
lemma blockedRedirect_unwrapped_diaNeg_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.neg, χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.neg, .diamond χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.neg, χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

omit [Hashable Atom] in
/-- **Free transfer, BOXED box-context half -- the box-plus payoff.** Dual of
`blockedRedirect_unwrapped_boxPos_mem`, using the box-plus filter arm instead of the unwrapped
one: when a minting attempt at `src` is blocked to `wBlock`, every box-positive formula
`T(□χ)@src` already on the branch (with `□χ` itself `φ₀`-relevant) transfers in its own BOXED
form to `wBlock`: `T(□χ)@wBlock ∈ b`, not merely the unwrapped `T(χ)@wBlock ∈ b` the unenriched
key could only ever give. This is the box-plus enrichment's payoff: `successorBirthContent`'s
third disjunct records `(pos, □χ)` directly, so `keyLowerBd` lower-bounds it into
`relevantSetFinset`'s BOXED slot at `wBlock`, giving the boxed membership as a three-line
consequence -- exactly the "Redirect-Inertness Assembly -- REMOVED" section's recommended
repair route, landed. -/
lemma blockedRedirect_boxed_boxPos_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.pos, .box χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.pos, .box χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, .box χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.pos, .box χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

omit [Hashable Atom] in
/-- **Free transfer, BOXED diamond-context half -- the box-plus payoff.** Dual of
`blockedRedirect_boxed_boxPos_mem`, using the box-plus filter's fourth disjunct: when a minting
attempt at `src` is blocked to `wBlock`, every diamond-negative formula `F(◇χ)@src` already on
the branch (with `◇χ` itself `φ₀`-relevant) transfers in its own BOXED (diamond) form to
`wBlock`: `F(◇χ)@wBlock ∈ b`. -/
lemma blockedRedirect_boxed_diaNeg_mem (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock)
    (χ : Proposition Atom) (hsf : (Sign.neg, .diamond χ) ∈ signedSubfmls φ₀)
    (hmem : (⟨.neg, .diamond χ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, .diamond χ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  have hkey := blockingWorldS4Keyed_eq_birthContent φ₀ b keys s φ src wBlock hblock
  have hsub := hkL wBlock (successorBirthContent φ₀ b s φ src) hkey
  have hmemSet : (Sign.neg, .diamond χ) ∈ successorBirthContent φ₀ b s φ src := by
    unfold successorBirthContent
    refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter]
    refine ⟨hsf, Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))⟩
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨_, hmem, rfl⟩
  have hrel := hsub hmemSet
  unfold relevantSetFinset at hrel
  rw [Finset.mem_filter] at hrel
  simp only [List.any_eq_true, beq_iff_eq] at hrel
  obtain ⟨sf', hsf'mem, heq⟩ := hrel.2
  rw [heq] at hsf'mem
  exact hsf'mem

/-! ## Saturation Preservation Under the Keyed Redirect (Plan v6, re-scoped Phases 3-5)

Per the `#### Phase 1 Verdict` in `plans/07_canonical-witness-truth-lemma.md`
(`specs/553_s4_loop_guard_soundness_reachability_restriction/`), the sole remaining obligation
for the redirect-preservation argument is `modalS4Saturated` preservation under the specific
`addEdge src wBlock` a keyed-guard block performs. `modalApplyOneS4`'s output at a signed formula
`sf` depends on `acc` ONLY through `acc.successorsOf sf.label` (`blockingWorldS4`, the K rules,
the T self-propagation arms, and the 4-rule arms are all either acc-independent or route through
`successorsOf sf.label` alone), so the two `successorsOf`/`addEdge` lemmas below make that
dependence explicit at the two points this obligation needs: invariance when `sf.label ≠ src`,
and the extended-successor content when `sf.label = src`. -/

omit [Hashable Atom] in
/-- `Accessibility.successorsOf` is unaffected by `addEdge` at any world other than the
redirect's source: the new edge only ever extends `src`'s own successor list. -/
lemma successorsOf_addEdge_of_ne (acc : Accessibility) (src wBlock v : WorldIndex)
    (hne : v ≠ src) : (acc.addEdge src wBlock).successorsOf v = acc.successorsOf v := by
  unfold Accessibility.successorsOf Accessibility.addEdge
  simp only [List.filterMap_cons, beq_iff_eq]
  rw [if_neg (Ne.symm hne)]

omit [Hashable Atom] in
/-- `Accessibility.successorsOf` at the redirect's source, after `addEdge`, is `wBlock`
prepended to the original successor list. -/
lemma successorsOf_addEdge_self (acc : Accessibility) (src wBlock : WorldIndex) :
    (acc.addEdge src wBlock).successorsOf src = wBlock :: acc.successorsOf src := by
  unfold Accessibility.successorsOf Accessibility.addEdge
  simp

/-- Closed form for `modalApplyOneS4`'s `.fst` at the box-positive shape `T(□ψ)@w`: the T-rule
(`modalTBoxSelf`) and 4-rule (`modalFourBoxProp`) propagation arms' merge on top of K's
`boxPropagation`, spelled out explicitly rather than left behind a `let`. Reusable scaffolding
for both `modalApplyOneS4_fst_congr_successorsOf` and `modalS4Saturated_addEdge_of_blocked`:
both need to compare this expression at two different accessibilities, and it is far easier to
compare the closed form (which isolates every acc-dependent subterm as `boxPropagation`/
`modalFourBoxProp` applied to that accessibility) than to re-derive it twice. -/
lemma modalApplyOneS4_boxPos_fst_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4 φ₀ (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
    (match (match (if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
              else RuleResult.persistent (boxPropagation b acc ψ w)) with
          | RuleResult.persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | RuleResult.notApplicable =>
            if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTBoxSelf b ψ w)
          | other => other) with
      | RuleResult.persistent tForms =>
        RuleResult.persistent
          (tForms ++ (modalFourBoxProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
      | RuleResult.notApplicable =>
        if (modalFourBoxProp b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (modalFourBoxProp b acc ψ w)
      | other => other) := by
  have hk : (modalApplyOne (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
      else RuleResult.persistent (boxPropagation b acc ψ w) := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTBoxSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  have htS4 : (modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent tForms =>
          RuleResult.persistent
            (tForms ++ (modalFourBoxProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalFourBoxProp b acc ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalFourBoxProp b acc ψ w)
        | other => other) := by
    unfold modalApplyOneS4Rules
    obtain ⟨tResult, tAcc⟩ := modalApplyOneT (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases tResult <;> first | rfl | (simp only []; split <;> rfl)
  have hshape : modalApplyOneS4 φ₀ (⟨.pos, .box ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.pos, .box ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape, htS4, htR, hk]
  rfl

/-- Dual of `modalApplyOneS4_boxPos_fst_eq` for the diamond-negative shape `F(◇ψ)@w`, via
`modalTDiaNegSelf`/`modalFourDiaNegProp` and the inline diamond-negative K rule arm (there is no
separately named `def` for the K layer here, unlike `boxPropagation`, so its filterMap is
spelled out directly). -/
lemma modalApplyOneS4_diaNeg_fst_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneS4 φ₀ (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
    (match (match (if ((acc.successorsOf w).filterMap fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
              if b.any (· == sf') then none else some sf').isEmpty then
            RuleResult.notApplicable
          else
            RuleResult.persistent ((acc.successorsOf w).filterMap fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
              if b.any (· == sf') then none else some sf')) with
          | RuleResult.persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | RuleResult.notApplicable =>
            if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTDiaNegSelf b ψ w)
          | other => other) with
      | RuleResult.persistent tForms =>
        RuleResult.persistent
          (tForms ++ (modalFourDiaNegProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
      | RuleResult.notApplicable =>
        if (modalFourDiaNegProp b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (modalFourDiaNegProp b acc ψ w)
      | other => other) := by
  have hk : (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      if ((acc.successorsOf w).filterMap fun u =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
            if b.any (· == sf') then none else some sf').isEmpty then
        RuleResult.notApplicable
      else
        RuleResult.persistent ((acc.successorsOf w).filterMap fun u =>
          let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
          if b.any (· == sf') then none else some sf') := by
    unfold modalApplyOne
    simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
      modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
    split_ifs <;> simp_all
  have htR : (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent kForms =>
          RuleResult.persistent
            (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalTDiaNegSelf b ψ w)
        | other => other) := by
    unfold modalApplyOneT
    obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases kResult <;> first | rfl | (simp only []; split <;> rfl)
  have htS4 : (modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
      (match (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
        | RuleResult.persistent tForms =>
          RuleResult.persistent
            (tForms ++ (modalFourDiaNegProp b acc ψ w).filter (fun x => !(tForms.any (· == x))))
        | RuleResult.notApplicable =>
          if (modalFourDiaNegProp b acc ψ w).isEmpty then RuleResult.notApplicable
          else RuleResult.persistent (modalFourDiaNegProp b acc ψ w)
        | other => other) := by
    unfold modalApplyOneS4Rules
    obtain ⟨tResult, tAcc⟩ := modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc
    cases tResult <;> first | rfl | (simp only []; split <;> rfl)
  have hshape : modalApplyOneS4 φ₀ (⟨.neg, .diamond ψ, w⟩ :
      SignedFormula (Proposition Atom) WorldIndex) b acc =
      modalApplyOneS4Rules (⟨.neg, .diamond ψ, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape, htS4, htR, hk]
  rfl

omit [Hashable Atom] in
/-- `modalApplyOne`'s (the underlying K-rule dispatch, no S4 guard) `.fst` component is
**entirely independent of `acc`** outside its own two acc-consulting shapes (`T(□φ)@w`, whose
`boxPropagation` reads `acc.successorsOf w`, and `F(◇φ)@w`, whose inline dual does the same):
the propositional rules and both minting arms (`F(□φ)`, `T(◇φ)`) never consult `acc` for their
`.fst` content, only for the accessibility they hand back as `.snd`. -/
lemma modalApplyOne_fst_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc1 acc2 : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∧
         ¬ (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)) :
    (modalApplyOne sf b acc1).fst = (modalApplyOne sf b acc2).fst := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOne
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp_all [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?,
      List.map, List.find?, RuleResult.isApplicable, Option.getD_none] <;>
    split_ifs <;> rfl

/-- `modalApplyOneS4`'s `.fst` component is **entirely independent of `acc`** outside the two
4-rule/T-rule-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`): the guard's own minting/blocking decision
(`blockingWorldS4`) never consults `acc`, and every other rule arm (K's mint rules, the
propositional rules, the T self-propagation arms) is likewise acc-free at these shapes.
Companion to `modalApplyOneS4_eq_of_not_boxNeg_diaPos` (which handles the *guard*-relevant
shapes `F(□φ)`/`T(◇φ)`), but for the complementary shape set and for the `.fst` projection
against two arbitrary accessibilities rather than one fixed reduction target. -/
lemma modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc1 acc2 : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∧
         ¬ (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)) :
    (modalApplyOneS4 φ₀ sf b acc1).fst = (modalApplyOneS4 φ₀ sf b acc2).fst := by
  obtain ⟨h1, h2⟩ := h
  by_cases hg1 : sf.sign = .neg ∧ ∃ ψ, sf.formula = .box ψ
  · obtain ⟨hs, ψ, hf⟩ := hg1
    have hsfeq : sf = (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
      rcases sf with ⟨s', f', w'⟩; simp_all
    rw [hsfeq]
    rcases hblk : blockingWorldS4 φ₀ b .neg ψ sf.label with _ | wBlock
    · rw [modalApplyOneS4_boxNeg_unblocked_eq φ₀ b acc1 ψ sf.label hblk,
        modalApplyOneS4_boxNeg_unblocked_eq φ₀ b acc2 ψ sf.label hblk]
      exact modalApplyOne_fst_eq_of_not_boxPos_diaNeg _ b acc1 acc2 ⟨by simp, by simp⟩
    · rw [modalApplyOneS4_boxNeg_blocked_eq φ₀ b acc1 ψ sf.label wBlock hblk,
        modalApplyOneS4_boxNeg_blocked_eq φ₀ b acc2 ψ sf.label wBlock hblk]
  · by_cases hg2 : sf.sign = .pos ∧ ∃ ψ, sf.formula = .diamond ψ
    · obtain ⟨hs, ψ, hf⟩ := hg2
      have hsfeq : sf = (⟨.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq]
      rcases hblk : blockingWorldS4 φ₀ b .pos ψ sf.label with _ | wBlock
      · rw [modalApplyOneS4_diaPos_unblocked_eq φ₀ b acc1 ψ sf.label hblk,
          modalApplyOneS4_diaPos_unblocked_eq φ₀ b acc2 ψ sf.label hblk]
        exact modalApplyOne_fst_eq_of_not_boxPos_diaNeg _ b acc1 acc2 ⟨by simp, by simp⟩
      · rw [modalApplyOneS4_diaPos_blocked_eq φ₀ b acc1 ψ sf.label wBlock hblk,
          modalApplyOneS4_diaPos_blocked_eq φ₀ b acc2 ψ sf.label wBlock hblk]
    · -- Neither guard shape (`F(□φ)`, `T(◇φ)`) nor either 4-rule shape (`T(□φ)`, `F(◇φ)`):
      -- `modalApplyOneS4` reduces all the way to `modalApplyOne`, whose `.fst` at the five
      -- remaining (non-modal) shapes never mentions `acc` at all.
      have hshape1 : modalApplyOneS4 φ₀ sf b acc1 = modalApplyOneS4Rules sf b acc1 :=
        modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc1 ⟨hg1, hg2⟩
      have hshape2 : modalApplyOneS4 φ₀ sf b acc2 = modalApplyOneS4Rules sf b acc2 :=
        modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc2 ⟨hg1, hg2⟩
      rw [hshape1, hshape2, modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc1 ⟨h1, h2⟩,
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc2 ⟨h1, h2⟩,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc1 ⟨h1, h2⟩,
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc2 ⟨h1, h2⟩]
      exact modalApplyOne_fst_eq_of_not_boxPos_diaNeg sf b acc1 acc2 ⟨h1, h2⟩

/-- `modalApplyOneS4`'s `.fst` component depends on `acc` ONLY through `acc.successorsOf
sf.label`: whenever two accessibilities agree there, the whole rule output agrees. Companion to
`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg`, covering the two shapes that lemma excludes
(`T(□φ)@w`, `F(◇φ)@w`) via `modalApplyOneS4_boxPos_fst_eq`/`_diaNeg_fst_eq`'s closed forms,
whose only `acc`-dependent subterms (`boxPropagation`/`modalFourBoxProp`/the inline
diamond-negative filterMap/`modalFourDiaNegProp`) all route through `acc.successorsOf sf.label`
alone and so rewrite directly under `hsucc`. -/
lemma modalApplyOneS4_fst_congr_successorsOf (φ₀ : Proposition Atom)
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc1 acc2 : Accessibility)
    (hsucc : acc1.successorsOf sf.label = acc2.successorsOf sf.label) :
    (modalApplyOneS4 φ₀ sf b acc1).fst = (modalApplyOneS4 φ₀ sf b acc2).fst := by
  by_cases hhard :
      (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∨
      (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)
  · rcases hhard with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨.pos, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq, modalApplyOneS4_boxPos_fst_eq φ₀ b acc1 ψ sf.label,
        modalApplyOneS4_boxPos_fst_eq φ₀ b acc2 ψ sf.label]
      unfold boxPropagation modalFourBoxProp
      rw [hsucc]
    · have hsfeq : sf = (⟨.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by
        rcases sf with ⟨s', f', w'⟩; simp_all
      rw [hsfeq, modalApplyOneS4_diaNeg_fst_eq φ₀ b acc1 ψ sf.label,
        modalApplyOneS4_diaNeg_fst_eq φ₀ b acc2 ψ sf.label]
      unfold modalFourDiaNegProp
      rw [hsucc]
  · exact modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg φ₀ sf b acc1 acc2 (not_or.mp hhard)

/-- **The hard content** (re-scoped Phase 3's remaining obligation, per the plan's
`#### Phase 3 Progress Record`): `modalS4Saturated` preservation under the specific `addEdge
src wBlock` the keyed minting guard's block performs. Combines `modalApplyOneS4_fst_congr_
successorsOf`/`modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg` (acc-dependence is confined to
`acc.successorsOf sf.label`, and only at the two 4-rule-relevant shapes) with the box-plus free
transfers `blockedRedirect_boxed_boxPos_mem`/`_diaNeg_mem` and the landed T-self bridges
`hintikkaS4_box_pos_self`/`hintikkaS4_dia_neg_self` (recovering the UNWRAPPED fact at `wBlock`
from the BOXED one, at the *original*, unextended `acc`, since the T self-propagation arm never
consults `acc` at all). Once both the boxed and unwrapped facts land at `wBlock`, the extended
accessibility's box-positive/diamond-negative persistent output at `src` is LITERALLY the same
list as the original's (the new `wBlock` entry in `acc.successorsOf src` is filtered out of
every propagation arm by those two facts), so the extended-acc saturation goal reduces exactly
to `hSat` applied at the unextended `acc`. -/
lemma modalS4Saturated_addEdge_of_blocked (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (s : Sign) (φ : Proposition Atom) (src wBlock : WorldIndex)
    (hSat : modalS4Saturated φ₀ b acc)
    (hUniv : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hkL : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hblock : blockingWorldS4Keyed φ₀ b keys s φ src = some wBlock) :
    modalS4Saturated φ₀ b (acc.addEdge src wBlock) := by
  intro sf hsfmem
  have hcond := hSat sf hsfmem
  by_cases hhard :
      (sf.sign = .pos ∧ ∃ ψ, sf.formula = .box ψ) ∨
      (sf.sign = .neg ∧ ∃ ψ, sf.formula = .diamond ψ)
  · by_cases hlabel : sf.label = src
    · -- The hard case: `sf` sits at the redirect's source and is one of the two
      -- 4-rule-relevant shapes. Establish literal `.fst` equality via the two free-transfer
      -- facts, then reduce to `hcond`.
      have hfst : (modalApplyOneS4 φ₀ sf b (acc.addEdge src wBlock)).fst =
          (modalApplyOneS4 φ₀ sf b acc).fst := by
        rcases hhard with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
        · -- box-positive at src: T(□ψ)@src ∈ b
          have hmemBox : (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
              b := by
            have : sf = (⟨.pos, .box ψ, src⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf with ⟨s', f', w'⟩
              simp_all
            rwa [this] at hsfmem
          have hsigsub : (Sign.pos, .box ψ) ∈ signedSubfmls φ₀ :=
            mem_signedSubfmls_of_formula_s4loop .pos (modalUniverseS4_mem_formula (hUniv _ hmemBox))
          have hboxedWB : (⟨.pos, .box ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            blockedRedirect_boxed_boxPos_mem φ₀ b keys s φ src wBlock hkL hblock ψ hsigsub hmemBox
          have hunwrappedWB : (⟨.pos, ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hintikkaS4_box_pos_self φ₀ b acc hSat ψ wBlock hboxedWB
          have hsfeq : sf = (⟨.pos, .box ψ, src⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          have hAddEq : boxPropagation b (acc.addEdge src wBlock) ψ src =
              boxPropagation b acc ψ src := by
            unfold boxPropagation
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.pos, ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hunwrappedWB, rfl⟩
            simp [hin]
          have hFourEq : modalFourBoxProp b (acc.addEdge src wBlock) ψ src =
              modalFourBoxProp b acc ψ src := by
            unfold modalFourBoxProp
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.pos, .box ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hboxedWB, rfl⟩
            simp [hin]
          rw [hsfeq, modalApplyOneS4_boxPos_fst_eq φ₀ b (acc.addEdge src wBlock) ψ src,
            modalApplyOneS4_boxPos_fst_eq φ₀ b acc ψ src, hAddEq, hFourEq]
        · -- diamond-negative at src: F(◇ψ)@src ∈ b
          have hmemDia : (⟨.neg, .diamond ψ, src⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
            have : sf = (⟨.neg, .diamond ψ, src⟩ :
                SignedFormula (Proposition Atom) WorldIndex) := by
              rcases sf with ⟨s', f', w'⟩
              simp_all
            rwa [this] at hsfmem
          have hsigsub : (Sign.neg, .diamond ψ) ∈ signedSubfmls φ₀ :=
            mem_signedSubfmls_of_formula_s4loop .neg
              (modalUniverseS4_mem_formula (hUniv _ hmemDia))
          have hboxedWB : (⟨.neg, .diamond ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            blockedRedirect_boxed_diaNeg_mem φ₀ b keys s φ src wBlock hkL hblock ψ hsigsub
              hmemDia
          have hunwrappedWB : (⟨.neg, ψ, wBlock⟩ :
              SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hintikkaS4_dia_neg_self φ₀ b acc hSat ψ wBlock hboxedWB
          have hsfeq : sf = (⟨.neg, .diamond ψ, src⟩ :
              SignedFormula (Proposition Atom) WorldIndex) := by
            rcases sf with ⟨s', f', w'⟩; simp_all
          have hAddEq : ((acc.addEdge src wBlock).successorsOf src).filterMap
              (fun u => let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
                if b.any (· == sf') then none else some sf') =
              (acc.successorsOf src).filterMap
              (fun u => let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
                if b.any (· == sf') then none else some sf') := by
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.neg, ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hunwrappedWB, rfl⟩
            simp [hin]
          have hFourEq : modalFourDiaNegProp b (acc.addEdge src wBlock) ψ src =
              modalFourDiaNegProp b acc ψ src := by
            unfold modalFourDiaNegProp
            rw [successorsOf_addEdge_self, List.filterMap_cons]
            have hin : (b.any fun x => x ==
                (⟨.neg, .diamond ψ, wBlock⟩ : SignedFormula (Proposition Atom) WorldIndex)) =
                true := by
              simp only [List.any_eq_true, beq_iff_eq]
              exact ⟨_, hboxedWB, rfl⟩
            simp [hin]
          rw [hsfeq, modalApplyOneS4_diaNeg_fst_eq φ₀ b (acc.addEdge src wBlock) ψ src,
            modalApplyOneS4_diaNeg_fst_eq φ₀ b acc ψ src, hAddEq, hFourEq]
      simpa only [hfst] using hcond
    · -- `sf.label ≠ src`: acc-dependence is confined to `acc.successorsOf sf.label`, invariant.
      have hsucc := successorsOf_addEdge_of_ne acc src wBlock sf.label hlabel
      have hfst := modalApplyOneS4_fst_congr_successorsOf φ₀ sf b (acc.addEdge src wBlock) acc
        hsucc
      simpa only [hfst] using hcond
  · -- Not one of the two 4-rule-relevant shapes: `.fst` is acc-independent absolutely.
    have hfst := modalApplyOneS4_fst_eq_of_not_boxPos_diaNeg φ₀ sf b (acc.addEdge src wBlock) acc
      (not_or.mp hhard)
    simpa only [hfst] using hcond

/-! ## Single-Step Invariant Preservation -/

/-- **Assembly helper**: given the OLD `e`'s bundle already transported to the post-step
`(b', acc')` at the OLD `keys` (`S4KeyedHintikkaInv_weaken`), plus the just-selected formula
`sf`'s own five per-field facts at the post-step `keys'`, assemble the full bundle at
`e ++ [sf]`. The old-`e` facts are lifted from `keys` to `keys'` via
`modalHintikkaClauseGen_S4Keyed_keys_indep` (only `hintikkaInv` mentions `keys`; the other four
fields do not reference `apply`/`keys` at all). -/
private lemma S4KeyedHintikkaInv_append (φ₀ : Proposition Atom)
    (b' e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc' : Accessibility)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hweak : S4KeyedHintikkaInv φ₀ b' e acc' keys)
    (hnew_hintikka : modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys') sf.sign sf.formula
      sf.label b' acc')
    (hnew_boxOnlyNeg : ∀ ψ, sf.formula = .box ψ → sf.sign = .neg)
    (hnew_diaOnlyPos : ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos)
    (hnew_boxNegWitness : ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc'.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b')
    (hnew_diaPosWitness : ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc'.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b') :
    S4KeyedHintikkaInv φ₀ b' (e ++ [sf]) acc' keys' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sf' hsf'
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · rw [← modalHintikkaClauseGen_S4Keyed_keys_indep φ₀ keys keys' sf'.sign sf'.formula
        sf'.label b' acc']
      exact hweak.hintikkaInv sf' hold
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_hintikka
  · intro sf' hsf' ψ hform
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eBoxOnlyNeg sf' hold ψ hform
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_boxOnlyNeg ψ hform
  · intro sf' hsf' ψ w hsfeq
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eBoxNegWitness sf' hold ψ w hsfeq
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_boxNegWitness ψ w hsfeq
  · intro sf' hsf' ψ hform
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eDiamondOnlyPos sf' hold ψ hform
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_diaOnlyPos ψ hform
  · intro sf' hsf' ψ w hsfeq
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eDiamondPosWitness sf' hold ψ w hsfeq
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_diaPosWitness ψ w hsfeq

/-- **Single-step preservation of `S4KeyedHintikkaInv`**: every
`modalStepBranchS4Keyed` step preserves the keys-threaded Hintikka-tracking invariant bundle,
given the ambient frozen `S4LoopInv` structure (defined above in this file, consumed for
`keyLowerBd`'s blocked-witness argument).
Mirrors `modalStepBranchS4_preserves_bClosure`'s case-split shape (mint-unblocked / mint-blocked
/ non-mint), composing `S4KeyedHintikkaInv_weaken` (old `e`'s facts lifted across
branch/`acc` growth) with `S4KeyedHintikkaInv_append`'s per-field assembly for the just-selected
formula: an unblocked mint discharges its witness via K's own `modalApplyOne_boxNeg_witness`/
`_diamondPos_witness`; a blocked redirect discharges it via
`modalStepBranchS4Keyed_blocked_witness_mem` (this file, above). -/
theorem modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hLoopInv : S4LoopInv φ₀ b e acc keys)
    (hHinv : S4KeyedHintikkaInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4KeyedHintikkaInv φ₀ b' e' newAcc keys' := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  have haccsub : ∀ w w', acc.hasEdge w w' = true → newAcc0.hasEdge w w' = true := by
    intro w w' h
    have hmono := modalApplyOneS4Keyed_hasEdge_mono φ₀ keys sf b acc h
    rwa [hpair] at hmono
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- neg + box: the boxNeg minting shape.
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: fresh witness world, standard K minting facts transfer.
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, -⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b
          (((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            rest) ++ b) e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label (modalNextWorld b) = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        refine S4KeyedHintikkaInv_append φ₀ _ e newAcc0 keys keys'
          (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' _; rfl
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.box.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨modalNextWorld b, hedge, List.mem_append_left _ List.mem_cons_self⟩
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
      · -- blocked: redirect to `wBlock`, witness already on the branch.
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        rw [hb', he']
        subst hnewAcc; subst hnewKeys
        have hbsub : ∀ x ∈ b, x ∈ b := fun x hx => hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b b e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label wBlock = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        have hwitmem := modalStepBranchS4Keyed_blocked_witness_mem φ₀ b keys .neg ψ sf.label
          wBlock hLoopInv.keyLowerBd hblock
        refine S4KeyedHintikkaInv_append φ₀ b e newAcc0 keys keys
          (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' _; rfl
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.box.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨wBlock, hedge, hwitmem⟩
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
    · -- pos + diamond: the diamondPos minting shape, symmetric to neg + box above.
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: fresh witness world.
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, -⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b
          (((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            rest) ++ b) e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label (modalNextWorld b) = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        refine S4KeyedHintikkaInv_append φ₀ _ e newAcc0 keys keys'
          (⟨.pos, .diamond ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' _; rfl
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.diamond.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨modalNextWorld b, hedge, List.mem_append_left _ List.mem_cons_self⟩
      · -- blocked: redirect to `wBlock`.
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        rw [hb', he']
        subst hnewAcc; subst hnewKeys
        have hbsub : ∀ x ∈ b, x ∈ b := fun x hx => hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b b e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label wBlock = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        have hwitmem := modalStepBranchS4Keyed_blocked_witness_mem φ₀ b keys .pos ψ sf.label
          wBlock hLoopInv.keyLowerBd hblock
        refine S4KeyedHintikkaInv_append φ₀ b e newAcc0 keys keys
          (⟨.pos, .diamond ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' _; rfl
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.diamond.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨wBlock, hedge, hwitmem⟩
  · -- non-mint: `sf` is neither the boxNeg nor the diaPos minting shape, so `keys' = keys`
    -- (the `keys'`-defining match falls to its `_, _` catch-all). `result` is
    -- `.persistent`/`.linear`/`.branching` for a purely propositional or T/4-persistent `sf`;
    -- `.notApplicable` is excluded since `findSome?` only returns `some` there.
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    rw [hpair] at hsf
    dsimp only at hsf
    by_cases hmint2 : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · -- pos-box / neg-diamond: always persistent/notApplicable (never linear/branching).
      have hne := modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding φ₀ keys sf b acc hsfmem
        hLoopInv.accKnown hmint2
      rw [hpair] at hne
      dsimp only at hne
      rcases hres : result with lf | brs | lf | _
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
    · -- genuinely propositional: `sf.formula` is neither box- nor diamond-shaped at all.
      have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => hmint2 (Or.inl hc), fun hc => hmint2 (Or.inr hc)⟩
      have hnb : ∀ ψ, sf.formula ≠ .box ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd2.1 ⟨hs, ψ, hform⟩
        · exact hnbd.1 ⟨hs, ψ, hform⟩
      have hnd : ∀ ψ, sf.formula ≠ .diamond ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd.2 ⟨hs, ψ, hform⟩
        · exact hnbd2.2 ⟨hs, ψ, hform⟩
      rcases hres : result with lf | brs | lf | _
      · -- linear (propositional rule, e.g. and/or/imp)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (lf ++ b) newAcc0).1 = RuleResult.linear lf := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (lf ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        refine S4KeyedHintikkaInv_append φ₀ (lf ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- branching (propositional or-rule)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'
        obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
        rw [← hnewExps] at he'
        obtain ⟨br', hbr'mem, he'eq⟩ := List.mem_map.mp he'
        subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ br ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (br ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (br ++ b) newAcc0).1 = RuleResult.branching brs := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (br ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        rw [← he'eq]
        refine S4KeyedHintikkaInv_append φ₀ (br ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- persistent (no change to `e`)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · -- notApplicable: impossible, `findSome?` only returns `some` when applicable.
        rw [hres] at hsf; simp at hsf

/-- **`S4KeyedHintikkaInv` preservation for the ordered driver.** Every
`modalStepBranchS4KeyedOrdered` step preserves the keys-threaded Hintikka-tracking invariant
bundle, given the ambient frozen `S4LoopInv` structure. Ports
`modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` (above) to the ordered driver via
`modalStepBranchS4KeyedOrdered_cases`: the settled-fallback branch reduces to a literal call of
`modalStepBranchS4Keyed`, so it is discharged by the unordered theorem directly with no new
content; the primary-scan-hit branch selects a NON-MINT candidate
(`modalMintShape sf = false`, `modalNonMintCandidates`'s own predicate), so it is confined to the
unordered proof's own "non-mint" case (its final `by_cases hmint2` branch), restated here against
the shared body `modalStepBranchS4KeyedBody` in place of the bare `findSome?` extraction -- the
SAME per-formula mechanics (`modalStepBranchS4Keyed_eq_findSome_body` confirms the two traversals
share this body verbatim), just reached via a different selection route. No mint case ever arises
in the primary-scan-hit branch, so it needs none of the unordered proof's mint-shape content. -/
theorem modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hLoopInv : S4LoopInv φ₀ b e acc keys)
    (hHinv : S4KeyedHintikkaInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4KeyedHintikkaInv φ₀ b' e' newAcc keys' := by
  rcases modalStepBranchS4KeyedOrdered_cases φ₀ b e acc keys newBs newExps newAcc keys' hstep with
    ⟨sf, hcand, hbody⟩ | ⟨-, hfallback⟩
  · -- Primary-scan hit: `sf` is non-mint-shaped (by `modalNonMintCandidates`'s own predicate).
    have hsfmemb := modalNonMintCandidates_subset φ₀ keys b e acc hcand
    have hsfnote := modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf hcand
    have hmintapp : modalMintShape sf = false ∧
        (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
      unfold modalNonMintCandidates at hcand
      have hpred := (List.mem_filter.mp hcand).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
      exact ⟨hpred.1.1, hpred.2⟩
    obtain ⟨hmshape, -⟩ := hmintapp
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨hs, φ, hf⟩
        exact absurd hmshape (by simp [modalMintShape, hs, hf])
      · rintro ⟨hs, φ, hf⟩
        exact absurd hmshape (by simp [modalMintShape, hs, hf])
    have hany : e.any (· == sf) = false := by
      rw [List.any_eq_false]
      intro x hx heq
      rw [beq_iff_eq] at heq
      subst heq
      exact hsfnote hx
    unfold modalStepBranchS4KeyedBody at hbody
    rw [if_neg (by simp [hany])] at hbody
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at hbody
    dsimp only at hbody
    have haccsub : ∀ w w', acc.hasEdge w w' = true → newAcc0.hasEdge w w' = true := by
      intro w w' h
      have hmono := modalApplyOneS4Keyed_hasEdge_mono φ₀ keys sf b acc h
      rwa [hpair] at hmono
    by_cases hmint2 : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · -- pos-box / neg-diamond: always persistent (never linear/branching).
      have hne := modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding φ₀ keys sf b acc hsfmemb
        hLoopInv.accKnown hmint2
      rw [hpair] at hne
      dsimp only at hne
      rcases hres : result with lf | brs | lf | _
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
    · -- genuinely propositional: `sf.formula` is neither box- nor diamond-shaped at all.
      have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => hmint2 (Or.inl hc), fun hc => hmint2 (Or.inr hc)⟩
      have hnb : ∀ ψ, sf.formula ≠ .box ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd2.1 ⟨hs, ψ, hform⟩
        · exact hnbd.1 ⟨hs, ψ, hform⟩
      have hnd : ∀ ψ, sf.formula ≠ .diamond ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd.2 ⟨hs, ψ, hform⟩
        · exact hnbd2.2 ⟨hs, ψ, hform⟩
      rcases hres : result with lf | brs | lf | _
      · -- linear (propositional rule, e.g. and/or/imp)
        rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (lf ++ b) newAcc0).1 = RuleResult.linear lf := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (lf ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        refine S4KeyedHintikkaInv_append φ₀ (lf ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- branching (propositional or-rule)
        rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'
        obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
        rw [← hnewExps] at he'
        obtain ⟨br', hbr'mem, he'eq⟩ := List.mem_map.mp he'
        subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ br ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (br ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (br ++ b) newAcc0).1 = RuleResult.branching brs := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (br ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        rw [← he'eq]
        refine S4KeyedHintikkaInv_append φ₀ (br ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- persistent (no change to `e`)
        rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · -- notApplicable: impossible, `findSome?` only returns `some` when applicable.
        rw [hres] at hbody; simp at hbody
  · exact modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv φ₀ b e acc keys newBs newExps
      newAcc keys' hLoopInv hHinv hfallback

/-- **The combined structural invariant bundle Phase 9's fuel induction threads.** Everything
`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` and
`modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv` jointly need as ambient state,
packaged as one `Prop` so a single `List.Forall₂`-style relation carries all of it through the
outer fuel induction, mirroring how `S5SoundInv` (`FrameSoundness.lean`) bundles
`accFreshInv ∧ accReachableInv ∧ accTargetsKnown` for the S5 assembly. -/
def S4OrderedFuelInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop :=
  S4LoopInv φ₀ b e acc keys ∧ S4KeyedHintikkaInv φ₀ b e acc keys ∧
  (∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b) ∧ worldsContiguousS4 b ∧
  keysOriginS4 b acc keys

/-- Every `modalStepBranchS4KeyedOrdered` step preserves the combined `S4OrderedFuelInv` bundle,
for every child branch/expanded-set pair. Direct assembly of
`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` (supplies four of the five conjuncts) and
`modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv` (the fifth) -- no independent proof
content of its own. -/
theorem modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4OrderedFuelInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4OrderedFuelInv φ₀ b' e' newAcc keys' := by
  obtain ⟨hLoop, hH, hKW, hWC, hKO⟩ := hinv
  have hL := modalStepBranchS4KeyedOrdered_preserves_S4LoopInv φ₀ b e acc keys newBs newExps
    newAcc keys' hLoop hKW hWC hKO hstep
  have hHi := modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv φ₀ b e acc keys newBs
    newExps newAcc keys' hLoop hH hstep
  intro b' hb' e' he'
  exact ⟨hL.1 b' hb' e' he', hHi b' hb' e' he', hL.2.1 b' hb', hL.2.2.1 b' hb', hL.2.2.2 b' hb'⟩

/-! ## 4-Tuple Stepper Projection Bridge + Local Measure-Split Helpers

The measure-decrease engine (`modalExpMeasure_step_lt_gen`, `FmpMeasure.lean:3227`) is phrased
against the generic 3-tuple driver `modalStepBranchGen` (`Saturation.lean:122`), whereas the
keyed S4 driver `modalStepBranchS4Keyed` returns a 4-tuple with `keys'` bolted on. This section
bridges the two: `modalStepBranchS4Keyed_proj_stepBranchGen` shows a keyed step implies the
corresponding generic step at `apply := modalApplyOneS4Keyed φ₀ keys`, dropping the `keys'`
component. Both drivers scan the same branch `b` via `List.findSome?` with the same
"already expanded" guard and the same four `RuleResult` arms, so this is a structural
`findSome?`-congruence argument, not a semantic one. -/

/-- **Generic `findSome?` projection helper**: if a list-scan via `g1` (into a 4-tuple type
`A × B × Accessibility × K`) succeeds pointwise-projecting to a scan via `g2` (into the
3-tuple `A × B × Accessibility`, dropping the last component whenever `g1` is `some`, and
agreeing with `g1` on which elements are skipped/`none`), then `g1`'s scan result projects to
`g2`'s scan result the same way. Purely structural: no reference to any tableau-specific type. -/
private lemma stepBranch_findSome?_proj4to3
    {α A B K : Type*}
    {g1 : α → Option (A × B × Accessibility × K)}
    {g2 : α → Option (A × B × Accessibility)}
    (hpt : ∀ (x : α) (a : A) (bb : B) (c : Accessibility) (k : K),
      g1 x = some (a, bb, c, k) → g2 x = some (a, bb, c))
    (hnone : ∀ x : α, g1 x = none → g2 x = none) :
    ∀ (l : List α) (a : A) (bb : B) (c : Accessibility) (k : K),
      l.findSome? g1 = some (a, bb, c, k) → l.findSome? g2 = some (a, bb, c) := by
  intro l
  induction l with
  | nil => intro a bb c k h; simp at h
  | cons x rest ih =>
    intro a bb c k h
    rw [List.findSome?_cons] at h
    rw [List.findSome?_cons]
    cases hg1 : g1 x with
    | none =>
      rw [hg1] at h
      rw [hnone x hg1]
      exact ih a bb c k h
    | some v =>
      rw [hg1] at h
      simp only [Option.some.injEq] at h
      have hg1' : g1 x = some (a, bb, c, k) := by rw [hg1, h]
      rw [hpt x a bb c k hg1']

/-- **The projection lemma**: a keyed step at `modalStepBranchS4Keyed φ₀ b e acc keys`
implies the corresponding step of the generic driver at `apply := modalApplyOneS4Keyed φ₀ keys`,
dropping the `keys'` component. Both sides select the SAME formula `sf` from `b` (same
"already expanded" guard `e.any (· == sf)`) and dispatch on the SAME `RuleResult` value
`(modalApplyOneS4Keyed φ₀ keys sf b acc).1`, since `modalStepBranchGen`'s `apply sf b acc` at
`apply := modalApplyOneS4Keyed φ₀ keys` computes literally the same pair the keyed stepper
computes internally. -/
lemma modalStepBranchS4Keyed_proj_stepBranchGen (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys) b e acc = some (newBs, newExps, newAcc) := by
  unfold modalStepBranchS4Keyed at hstep
  unfold modalStepBranchGen
  refine stepBranch_findSome?_proj4to3 ?_ ?_ b newBs newExps newAcc keys' hstep
  · -- hpt: pointwise, the keyed inner computation projects to the generic one.
    intro sf a bb c k h
    split_ifs at h ⊢ with hexp
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at h
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h; simp at h
  · -- hnone: pointwise, both drivers skip the same elements.
    intro sf h
    split_ifs at h ⊢ with hexp
    · rfl
    · rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
      rw [hpair] at h
      rcases hres : result with nf | brs | nf | -
      · rw [hres] at h; simp at h
      · rw [hres] at h; simp at h
      · rw [hres] at h; simp at h
      · rfl

/-! ## Keyed Per-Step Measure Decrease over `modalUniverseS4`

Transcription of `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3227`, public but hardwired to
K's `modalUniverse φ0`/`modalWorldBound φ0`) over `modalUniverseS4 φ₀`/`modalWorldBoundS4 φ₀`.
Direct instantiation does not typecheck (see the plan's "Measure-Decrease Lead"), so the proof
below is a line-by-line transcription consuming: four universe-generic combinatorial
primitives (`_S4`-suffixed above), three landed per-call obligations
(`modalApplyOneS4Keyed_branchingLength_S4`/`_persistentFresh_S4`/`_outputsSubsetUniverse_S4`),
and the projection bridge (`modalStepBranchS4Keyed_proj_stepBranchGen`) plus its local
`modalExpMeasure_split`/`_append_S4` helpers (and the `_const_exp_S4` helper just above).
`hstep` is phrased directly against the keyed 4-tuple stepper `modalStepBranchS4Keyed` (dropping
`keys'` via the projection bridge inside the proof), matching what the top-loop induction below
will have in hand at each call site. The `hOutputsSubsetUniverse` obligation's extra hypotheses
(`hknown`/`hWC`/`hKT`/`hKD`/`hKI`, in place of the generic template's `accFreshInv`/strict-world-
bound pair) are threaded as raw hypotheses here rather than derived; the top-loop induction
below supplies them from
the ambient `S4LoopInv`. -/

/-- **The keyed engine**: one `modalStepBranchS4Keyed` step strictly decreases the base-3 damped
worklist measure over `modalUniverseS4 φ₀` by at least one. -/
lemma modalExpMeasure_step_lt_S4Keyed
    (φ₀ : Proposition Atom) (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverseS4 φ₀)
    (hknown : accTargetsKnown bh acc)
    (hWC : worldsContiguousS4 bh)
    (hKT : ∀ w ∈ modalKnownWorlds bh, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4Keyed φ₀ bh e acc keys =
      some (newBs, newBs.map (fun _ => newExp), newAcc, keys')) :
    modalExpMeasure (modalUniverseS4 φ₀) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverseS4 φ₀) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  have hstepGen := modalStepBranchS4Keyed_proj_stepBranchGen φ₀ bh e acc keys
    newBs (newBs.map (fun _ => newExp)) newAcc keys' hstep
  set U := modalUniverseS4 φ₀ with hUdef
  have hrhs : modalExpMeasure U (done ++ bh :: bt) (doneExp ++ e :: es) =
      modalExpMeasure U done doneExp + 3 ^ modalWork U bh e + modalExpMeasure U bt es :=
    modalExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : modalExpMeasure U (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) =
      modalExpMeasure U done doneExp +
        (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum +
        modalExpMeasure U bt es := by
    have hlen1 : (done ++ newBs).length = (doneExp ++ newBs.map (fun _ => newExp)).length := by
      simp [List.length_append, hdlen]
    rw [modalExpMeasure_append U (done ++ newBs) bt
          (doneExp ++ newBs.map (fun _ => newExp)) es hlen1,
        modalExpMeasure_append U done newBs doneExp (newBs.map (fun _ => newExp)) hdlen,
        modalExpMeasure_const_exp U newBs newExp]
  rw [hrhs, hlhs]
  suffices h : (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum + 1 ≤
      3 ^ modalWork U bh e by omega
  simp only [modalStepBranchGen] at hstepGen
  obtain ⟨sf, hsfmem, hfound⟩ := List.exists_of_findSome?_eq_some hstepGen
  split_ifs at hfound with hany
  simp only [Bool.not_eq_true] at hany
  have hsfU : sf ∈ U := hb sf hsfmem
  rcases hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 with nf | brs | nf | -
  · -- linear
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    have hdrop : modalWork U (nf ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (nf ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (nf ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · -- branching
    have hlen2 : brs.length = 2 :=
      modalApplyOneS4Keyed_branchingLength_S4 φ₀ keys sf bh acc brs hca
    obtain ⟨b0, b1, hbrs⟩ : ∃ b0 b1, brs = [b0, b1] := by
      match brs, hlen2 with
      | [b0, b1], _ => exact ⟨b0, b1, rfl⟩
    subst hbrs
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hdrop0 : modalWork U (b0 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b0 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b0 hz)
    have hdrop1 : modalWork U (b1 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b1 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b1 hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (b0 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    have h1 : modalWork U (b1 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    exact pow3_two_add_one_le hC h0 h1
  · -- persistent
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    obtain ⟨hnfne, hnffresh⟩ :=
      modalApplyOneS4Keyed_persistentFresh_S4 φ₀ keys sf bh acc nf hca
    obtain ⟨x0, hx0mem⟩ := List.exists_mem_of_ne_nil nf hnfne
    have hclosure := modalApplyOneS4Keyed_outputsSubsetUniverse_S4 φ₀ keys sf bh acc hb hsfmem
      hknown hWC hKT hKD hKI
    rw [hca] at hclosure
    have hx0U : x0 ∈ U := hclosure x0 hx0mem
    have hx0b : x0 ∉ bh := hnffresh x0 hx0mem
    have hx0b' : x0 ∈ nf ++ bh := List.mem_append_left bh hx0mem
    have hdrop : modalWork U (nf ++ bh) newExp + 1 ≤ modalWork U bh newExp :=
      modalWork_drop_persistent U bh (nf ++ bh) newExp x0 hx0U hx0b hx0b'
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh newExp := by omega
    have h0 : modalWork U (nf ++ bh) newExp ≤ modalWork U bh newExp - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · rw [hca] at hfound; simp at hfound

/-! ## Ordered Stepper: Termination Measure Re-Verification

Re-establishes the strict per-step measure decrease just proved against
`modalStepBranchS4Keyed` above, this time for the ordered stepper. The projection bridge
`modalStepBranchS4Keyed_proj_stepBranchGen` is replaced by a selection-agnostic form,
`modalStepBranchS4KeyedOrdered_proj`: rather than asserting the ordered stepper's result equals
the UNordered generic driver's own whole-branch `b.findSome?` traversal (false in general -- a
different formula may genuinely be selected first, that being the entire point of reordering),
it extracts the weaker existential fact `modalExpMeasure_step_lt_S4Keyed`'s proof actually
consumes: SOME formula `sf ∈ b`, `sf ∉ e`, whose rule application produces exactly the result
the ordered stepper returned. That proof never uses more than this existential (it never needs
`sf` to be the FIRST such formula in `b`), so the measure argument below transcribes unchanged
once fed this replacement bridge -- every other ingredient (the four combinatorial measure
primitives, the three per-call rule-application obligations) is selection-independent and reused
exactly as is. -/

/-- **The projection lemma, ordered form.** Selection-agnostic replacement for
`modalStepBranchS4Keyed_proj_stepBranchGen`, built directly from
`modalStepBranchS4KeyedOrdered_selected_mem` rather than from `modalStepBranchGen`'s own
`findSome?`. The conclusion drops the `keys'` component of `modalStepBranchS4KeyedBody`'s output
via `Option.map`, matching the 3-tuple shape `modalStepBranchGen` itself would have produced. -/
lemma modalStepBranchS4KeyedOrdered_proj (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∃ sf ∈ b, sf ∉ e ∧
      (modalStepBranchS4KeyedBody φ₀ b e acc keys sf).map (fun p => (p.1, p.2.1, p.2.2.1)) =
        some (newBs, newExps, newAcc) := by
  obtain ⟨sf, hsf_mem, hsf_ne, hsf_body⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  exact ⟨sf, hsf_mem, hsf_ne, by rw [hsf_body]; rfl⟩

/-- **The keyed engine, ordered form.** One `modalStepBranchS4KeyedOrdered` step strictly
decreases the base-3 damped worklist measure over `modalUniverseS4 φ₀` by at least one.
Line-by-line transcription of `modalExpMeasure_step_lt_S4Keyed` above, substituting
`modalStepBranchS4KeyedOrdered_proj` for `modalStepBranchS4Keyed_proj_stepBranchGen`. -/
lemma modalExpMeasure_step_lt_S4KeyedOrdered
    (φ₀ : Proposition Atom) (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverseS4 φ₀)
    (hknown : accTargetsKnown bh acc)
    (hWC : worldsContiguousS4 bh)
    (hKT : ∀ w ∈ modalKnownWorlds bh, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ bh e acc keys =
      some (newBs, newBs.map (fun _ => newExp), newAcc, keys')) :
    modalExpMeasure (modalUniverseS4 φ₀) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverseS4 φ₀) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  obtain ⟨sf, hsfmem, hsf_ne, hfound⟩ :=
    modalStepBranchS4KeyedOrdered_proj φ₀ bh e acc keys newBs (newBs.map (fun _ => newExp))
      newAcc keys' hstep
  set U := modalUniverseS4 φ₀ with hUdef
  have hrhs : modalExpMeasure U (done ++ bh :: bt) (doneExp ++ e :: es) =
      modalExpMeasure U done doneExp + 3 ^ modalWork U bh e + modalExpMeasure U bt es :=
    modalExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : modalExpMeasure U (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) =
      modalExpMeasure U done doneExp +
        (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum +
        modalExpMeasure U bt es := by
    have hlen1 : (done ++ newBs).length = (doneExp ++ newBs.map (fun _ => newExp)).length := by
      simp [List.length_append, hdlen]
    rw [modalExpMeasure_append U (done ++ newBs) bt
          (doneExp ++ newBs.map (fun _ => newExp)) es hlen1,
        modalExpMeasure_append U done newBs doneExp (newBs.map (fun _ => newExp)) hdlen,
        modalExpMeasure_const_exp U newBs newExp]
  rw [hrhs, hlhs]
  suffices h : (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum + 1 ≤
      3 ^ modalWork U bh e by omega
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  have hsfU : sf ∈ U := hb sf hsfmem
  unfold modalStepBranchS4KeyedBody at hfound
  rw [if_neg (by simp [hany])] at hfound
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf bh acc with ⟨result, newAcc0⟩
  rw [hpair] at hfound
  rcases hres : result with nf | brs | nf | -
  · -- linear
    rw [hres] at hfound
    simp only [Option.map_some] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    have hdrop : modalWork U (nf ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (nf ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (nf ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · -- branching
    have hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 = RuleResult.branching brs := by
      rw [hpair, hres]
    have hlen2 : brs.length = 2 :=
      modalApplyOneS4Keyed_branchingLength_S4 φ₀ keys sf bh acc brs hca
    obtain ⟨b0, b1, hbrs⟩ : ∃ b0 b1, brs = [b0, b1] := by
      match brs, hlen2 with
      | [b0, b1], _ => exact ⟨b0, b1, rfl⟩
    subst hbrs
    rw [hres] at hfound
    simp only [Option.map_some] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hdrop0 : modalWork U (b0 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b0 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b0 hz)
    have hdrop1 : modalWork U (b1 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b1 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b1 hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (b0 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    have h1 : modalWork U (b1 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    exact pow3_two_add_one_le hC h0 h1
  · -- persistent
    have hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 = RuleResult.persistent nf := by
      rw [hpair, hres]
    rw [hres] at hfound
    simp only [Option.map_some] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    obtain ⟨hnfne, hnffresh⟩ :=
      modalApplyOneS4Keyed_persistentFresh_S4 φ₀ keys sf bh acc nf hca
    obtain ⟨x0, hx0mem⟩ := List.exists_mem_of_ne_nil nf hnfne
    have hclosure := modalApplyOneS4Keyed_outputsSubsetUniverse_S4 φ₀ keys sf bh acc hb hsfmem
      hknown hWC hKT hKD hKI
    rw [hca] at hclosure
    have hx0U : x0 ∈ U := hclosure x0 hx0mem
    have hx0b : x0 ∉ bh := hnffresh x0 hx0mem
    have hx0b' : x0 ∈ nf ++ bh := List.mem_append_left bh hx0mem
    have hdrop : modalWork U (nf ++ bh) newExp + 1 ≤ modalWork U bh newExp :=
      modalWork_drop_persistent U bh (nf ++ bh) newExp x0 hx0U hx0b hx0b'
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh newExp := by omega
    have h0 : modalWork U (nf ++ bh) newExp ≤ modalWork U bh newExp - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · rw [hres] at hfound; simp at hfound

/-! ## Top-Loop Induction — `modalExpandBranchesS4Keyed_hintikka`

Assembles the termination top-loop: an open branch produced by the keyed driver is a Hintikka
set for the live S4 rule. Structural port of `modalExpandBranchesHintikka`
(`CompletenessLoop.lean:1430-1740`) with the per-index invariant taken as the CONJUNCTION
`S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4` (there is no single
bundled structure playing `ModalLoopInvHintikka`'s role for the keyed driver, per this file's
deliberate non-bundling), and threading the extra `keys` worklist column throughout. -/

/-- **Local re-derivation** of `CompletenessLoop.lean`'s `private modalStepBranchGen_newExps_const`
(`:515`), specialized to the keyed 4-tuple stepper (dropping the `keys'` component from the
conclusion, which plays no role in the constant-expanded-set fact). Identical case-split proof. -/
private lemma modalStepBranchS4Keyed_newExps_const (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∃ newExp, newExps = newBs.map (fun _ => newExp) := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -, -⟩ := hsf
    exact ⟨e ++ [sf], rfl⟩
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -, -⟩ := hsf
    exact ⟨e ++ [sf], by simp [List.map_map, Function.comp_def]⟩
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -, -⟩ := hsf
    exact ⟨e, rfl⟩
  · rw [hres] at hsf; simp at hsf

/-- **Local re-derivation** of the saturated-leaf characterisation
(`modalStepBranchGen_none_saturated`, `Completeness.lean:809`, public but phrased against the
generic 3-tuple driver, hence not directly applicable to the keyed 4-tuple stepper), mirroring
this file's own `findSome?_eq_none_iff` + case-split idiom rather than routing through a
generic-driver projection for the `none` direction. -/
private lemma modalStepBranchS4Keyed_none_saturated (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable := by
  unfold modalStepBranchS4Keyed at hstep
  rw [List.findSome?_eq_none_iff] at hstep
  have hbody := hstep sf hsfb
  by_cases hany : e.any (· == sf) = true
  · left
    simp only [List.any_eq_true] at hany
    obtain ⟨sf', hme, heq⟩ := hany
    simp only [beq_iff_eq] at heq
    exact heq ▸ hme
  · right
    simp only [Bool.not_eq_true] at hany
    simp only [hany] at hbody
    rcases hca : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨res, newAcc0⟩
    simp only [hca] at hbody
    rcases res with out | brs | out | _
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · rfl

/-- **The keyed top-loop Hintikka lemma**: an open branch produced by
`modalExpandBranchesS4Keyed` is a Hintikka set for the LIVE S4 rule `modalApplyOneS4 φ₀`
(bridged from the keyed rule via `hintikka_congr_S4`/`modalHintikkaSetS4_eq` at the very end).
Per-index hypothesis is the conjunction `S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧
worldsContiguousS4` (no single bundled structure plays `ModalLoopInvHintikka`'s role here, per
the same deliberate non-bundling); an extra `keyss` worklist column is threaded alongside
`branches`/`expandedSets`/`accs` throughout, mirroring `modalExpandBranchesS4Keyed`'s own
`keyss`/`pendingKeys`/`doneKeys` bookkeeping. Structural port of `modalExpandBranchesHintikka`
(`CompletenessLoop.lean:1430-1740`). -/
theorem modalExpandBranchesS4Keyed_hintikka (φ₀ : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      keyss.length = branches.length →
      modalExpMeasure (modalUniverseS4 φ₀) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility) (keysi : List (WorldIndex × Finset (Sign × Proposition Atom))),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        keyss[i]? = some keysi →
        S4LoopInv φ₀ bi ei ai keysi ∧ S4KeyedHintikkaInv φ₀ bi ei ai keysi ∧
          (∀ w k, (w, k) ∈ keysi → w ∈ modalKnownWorlds bi) ∧ worldsContiguousS4 bi) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesS4Keyed φ₀ branches expandedSets accs keyss fuel = .openBranch bR aR →
        modalHintikkaSetS4 φ₀ bR aR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hfuel _hInv bR aR h
    have hm : modalExpMeasure (modalUniverseS4 φ₀) branches expandedSets = 0 :=
      Nat.le_zero.mp hfuel
    have hbranches : branches = [] := by
      rcases branches with _ | ⟨bh, bt⟩
      · rfl
      · exfalso
        rcases expandedSets with _ | ⟨e, es⟩
        · simp only [List.length_nil, List.length_cons] at hlen; omega
        · simp only [modalExpMeasure, List.zip_cons_cons, List.map_cons, List.sum_cons] at hm
          have h3 := Nat.one_le_pow (modalWork (modalUniverseS4 φ₀) bh e) 3 (by omega)
          omega
    subst hbranches
    simp [modalExpandBranchesS4Keyed] at h
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hfuel hInv bR aR h
    simp only [modalExpandBranchesS4Keyed] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        pendingKeys.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        doneKeys.length = done.length →
        (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
            (ai : Accessibility) (keysi : List (WorldIndex × Finset (Sign × Proposition Atom))),
          (done ++ pending)[i]? = some bi → (doneExp ++ pendingExp)[i]? = some ei →
          (doneAccs ++ pendingAccs)[i]? = some ai → (doneKeys ++ pendingKeys)[i]? = some keysi →
          S4LoopInv φ₀ bi ei ai keysi ∧ S4KeyedHintikkaInv φ₀ bi ei ai keysi ∧
            (∀ w k, (w, k) ∈ keysi → w ∈ modalKnownWorlds bi) ∧ worldsContiguousS4 bi) →
        modalExpMeasure (modalUniverseS4 φ₀) (done ++ pending) (doneExp ++ pendingExp) ≤
          fuel' + 1 →
        modalExpandBranchesS4Keyed.processNext φ₀ fuel' pending pendingExp pendingAccs pendingKeys
            done doneExp doneAccs doneKeys = .openBranch bR aR →
        modalHintikkaSetS4 φ₀ bR aR from
      key branches expandedSets accs keyss [] [] [] [] hlen hlenA hlenK rfl rfl rfl hInv hfuel
        (by simpa [modalExpandBranchesS4Keyed] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        _ _ _ _ _ _ _ _ hinner
      simp [modalExpandBranchesS4Keyed.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hlength_p hlenP_accs hlenP_keys hdlength hdAccs hdKeys hInv_all hmeas hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          cases pendingKeys with
          | nil => simp at hlenP_keys
          | cons k restKs =>
            simp only [List.length_cons, Nat.add_right_cancel_iff]
              at hlength_p hlenP_accs hlenP_keys
            simp only [modalExpandBranchesS4Keyed.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · -- Closed branch: skip and recurse on the inner induction
              rw [if_pos hcl] at hinner
              apply ih_inner es restAs restKs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                (doneKeys ++ [k])
              · simpa using hlength_p
              · simpa using hlenP_accs
              · simpa using hlenP_keys
              · simp [hdlength]
              · simp [hdAccs]
              · simp [hdKeys]
              · intro i bi ei ai keysi hib hie hia hik
                apply hInv_all i bi ei ai keysi
                · convert hib using 2; simp
                · convert hie using 2; simp
                · convert hia using 2; simp
                · convert hik using 2; simp
              · convert hmeas using 2 <;> simp
              · exact hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep : modalStepBranchS4Keyed φ₀ bh e a k with
              | none =>
                -- Saturated open branch: bh/a are the returned bR/aR.
                rw [hstep] at hinner
                obtain ⟨hbeq, haeq⟩ : bh = bR ∧ a = aR := by
                  cases hinner; exact ⟨rfl, rfl⟩
                have hbeq' : bR = bh := hbeq.symm
                have haeq' : aR = a := haeq.symm
                subst hbeq'; subst haeq'
                have hbh_idx : (done ++ bR :: bt)[done.length]? = some bR := by
                  rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp
                have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdlength]
                have ha_idx : (doneAccs ++ aR :: restAs)[done.length]? = some aR := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdAccs]
                have hk_idx : (doneKeys ++ k :: restKs)[done.length]? = some k := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdKeys]
                obtain ⟨hLoopInv, hHinv, -, -⟩ :=
                  hInv_all done.length bR e aR k hbh_idx he_idx ha_idx hk_idx
                rw [modalHintikkaSetS4_eq, ← hintikka_congr_S4 φ₀ k]
                refine ⟨hcl, ?_, ?_, ?_⟩
                · -- Conjunct 2: rule-application clause for every sf ∈ bR
                  intro sf hsfmem
                  obtain ⟨s, φ, l⟩ := sf
                  cases φ with
                  | atom p =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .atom p, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .atom p, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | bot =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .bot, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .bot, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | imp a c =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .imp a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .imp a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | and a c =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .and a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .and a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | or a c =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .or a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .or a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | box ψ' =>
                    cases s with
                    | pos =>
                      rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                          ⟨.pos, .box ψ', l⟩ hsfmem with hine | hna
                      · exact absurd (hHinv.eBoxOnlyNeg ⟨.pos, .box ψ', l⟩ hine ψ' rfl) (by simp)
                      · simp [hna]
                    | neg => trivial
                  | diamond ψ' =>
                    cases s with
                    | pos => trivial
                    | neg =>
                      rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                          ⟨.neg, .diamond ψ', l⟩ hsfmem with hine | hna
                      · exact absurd (hHinv.eDiamondOnlyPos ⟨.neg, .diamond ψ', l⟩ hine ψ' rfl)
                          (by simp)
                      · simp [hna]
                · -- Conjunct 3: box-negative witness existence
                  intro ψ' w hmem
                  rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep _ hmem
                      with hine | hna
                  · exact hHinv.eBoxNegWitness _ hine ψ' w rfl
                  · exact absurd hna (modalApplyOneS4Keyed_boxNeg_ne_notApplicable φ₀ k bR aR ψ' w)
                · -- Conjunct 4: diamond-positive witness existence (symmetric to Conjunct 3)
                  intro ψ' w hmem
                  rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep _ hmem
                      with hine | hna
                  · exact hHinv.eDiamondPosWitness _ hine ψ' w rfl
                  · exact
                      absurd hna (modalApplyOneS4Keyed_diaPos_ne_notApplicable φ₀ k bR aR ψ' w)
              | some step =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := step
                rw [hstep] at hinner
                have hstepEq :
                    modalStepBranchS4Keyed φ₀ bh e a k = some (newBs, newExps, newAcc, keys') :=
                  hstep
                have hbh_idx : (done ++ bh :: bt)[done.length]? = some bh := by
                  rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp
                have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdlength]
                have ha_idx : (doneAccs ++ a :: restAs)[done.length]? = some a := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdAccs]
                have hk_idx : (doneKeys ++ k :: restKs)[done.length]? = some k := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdKeys]
                obtain ⟨hLoopInv, hHinv, hKW, hWC⟩ :=
                  hInv_all done.length bh e a k hbh_idx he_idx ha_idx hk_idx
                obtain ⟨newExp, hNewExpEq⟩ :=
                  modalStepBranchS4Keyed_newExps_const φ₀ bh e a k newBs newExps newAcc keys'
                    hstepEq
                subst hNewExpEq
                have hstepEq' : modalStepBranchS4Keyed φ₀ bh e a k =
                    some (newBs, newBs.map (fun _ => newExp), newAcc, keys') := hstepEq
                obtain ⟨hLoopInvAll, hKWAll, hWCAll⟩ :=
                  modalStepBranchS4_preserves_S4LoopInv φ₀ bh e a k newBs
                    (newBs.map (fun _ => newExp)) newAcc keys' hLoopInv hKW hWC hstepEq'
                have hHinvAll :=
                  modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv φ₀ bh e a k newBs
                    (newBs.map (fun _ => newExp)) newAcc keys' hLoopInv hHinv hstepEq'
                have hstep_lt := modalExpMeasure_step_lt_S4Keyed φ₀ k keys' done bt newBs
                  doneExp es newExp bh e a newAcc hdlength.symm hLoopInv.bClosure
                  hLoopInv.accKnown hWC hLoopInv.keysTotal hLoopInv.keysDistinct
                  hLoopInv.keysInUniverse hstepEq'
                apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
                · simp only [List.length_append, List.length_map, hdlength]
                  omega
                · simp only [List.length_append, List.length_replicate, hdAccs]
                  omega
                · simp only [List.length_append, List.length_replicate, hdKeys]
                  omega
                · omega
                · intro i bi ei ai keysi hib hie hia hik
                  rcases Nat.lt_or_ge i done.length with hlt1 | hge1
                  · apply hInv_all i bi ei ai keysi
                    · rw [List.append_assoc, List.getElem?_append_left hlt1] at hib
                      rwa [List.getElem?_append_left hlt1]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hie
                      rwa [List.getElem?_append_left (by omega)]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hia
                      rwa [List.getElem?_append_left (by omega)]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hik
                      rwa [List.getElem?_append_left (by omega)]
                  · rcases Nat.lt_or_ge i (done.length + newBs.length) with hlt2 | hge2
                    · -- Region: newBs (all sharing newExp/newAcc/keys')
                      have hj : i - done.length < newBs.length := by omega
                      have hbi_newBs : newBs[i - done.length]? = some bi := by
                        rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                        rwa [List.getElem?_append_left hj] at hib
                      have hbi_mem : bi ∈ newBs := List.mem_of_getElem? hbi_newBs
                      have hei_eq : ei = newExp := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                        rw [List.getElem?_append_left
                              (by simp only [List.length_map]; omega)] at hie
                        rw [List.getElem?_map,
                            show newBs[i - doneExp.length]? = some bi from by
                              rw [show i - doneExp.length = i - done.length from by omega]
                              exact hbi_newBs] at hie
                        simp only [Option.map_some, Option.some.injEq] at hie
                        exact hie.symm
                      have hei_eq' : newExp = ei := hei_eq.symm
                      subst hei_eq'
                      have hai_eq : ai = newAcc := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneAccs.length ≤ i)] at hia
                        rw [List.getElem?_append_left
                              (by simp only [List.length_replicate]; omega)] at hia
                        exact List.eq_of_mem_replicate (List.mem_of_getElem? hia)
                      subst hai_eq
                      have hkeysi_eq : keysi = keys' := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneKeys.length ≤ i)] at hik
                        rw [List.getElem?_append_left
                              (by simp only [List.length_replicate]; omega)] at hik
                        exact List.eq_of_mem_replicate (List.mem_of_getElem? hik)
                      subst hkeysi_eq
                      have hnewExp_mem : newExp ∈ newBs.map (fun _ => newExp) :=
                        List.mem_map.mpr ⟨bi, hbi_mem, rfl⟩
                      exact ⟨hLoopInvAll bi hbi_mem newExp hnewExp_mem,
                        hHinvAll bi hbi_mem newExp hnewExp_mem, hKWAll bi hbi_mem,
                        hWCAll bi hbi_mem⟩
                    · -- Region: bt (shifted index)
                      have hbi_bt : bt[i - done.length - newBs.length]? = some bi := by
                        rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                        rw [List.getElem?_append_right
                              (by omega : newBs.length ≤ i - done.length)] at hib
                        exact hib
                      have hei_es : es[i - done.length - newBs.length]? = some ei := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                        rw [List.getElem?_append_right
                              (by simp only [List.length_map]; omega :
                                (newBs.map (fun _ => newExp)).length ≤ i - doneExp.length)] at hie
                        rwa [show i - doneExp.length - (newBs.map (fun _ => newExp)).length =
                              i - done.length - newBs.length from by
                            simp only [List.length_map]; omega] at hie
                      have hai_restAs : restAs[i - done.length - newBs.length]? = some ai := by
                        rw [List.append_assoc, List.getElem?_append_right (by omega :
                              doneAccs.length ≤ i)] at hia
                        rw [List.getElem?_append_right
                              (by simp only [List.length_replicate]; omega :
                                (List.replicate newBs.length newAcc).length ≤
                                  i - doneAccs.length)] at hia
                        rwa [show i - doneAccs.length -
                              (List.replicate newBs.length newAcc).length =
                              i - done.length - newBs.length from by
                            simp only [List.length_replicate]; omega] at hia
                      have hki_restKs : restKs[i - done.length - newBs.length]? = some keysi := by
                        rw [List.append_assoc, List.getElem?_append_right (by omega :
                              doneKeys.length ≤ i)] at hik
                        rw [List.getElem?_append_right
                              (by simp only [List.length_replicate]; omega :
                                (List.replicate newBs.length keys').length ≤
                                  i - doneKeys.length)] at hik
                        rwa [show i - doneKeys.length -
                              (List.replicate newBs.length keys').length =
                              i - done.length - newBs.length from by
                            simp only [List.length_replicate]; omega] at hik
                      apply hInv_all (done.length + 1 + (i - done.length - newBs.length)) bi ei ai
                        keysi
                      · rw [List.getElem?_append_right
                              (by omega : done.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) - done.length
                              = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hbi_bt
                      · rw [List.getElem?_append_right
                              (by omega : doneExp.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneExp.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hei_es
                      · rw [List.getElem?_append_right
                              (by omega : doneAccs.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneAccs.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hai_restAs
                      · rw [List.getElem?_append_right
                              (by omega : doneKeys.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneKeys.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hki_restKs
                · exact hinner

/-! ## Groundwork: Keyed-Driver Initial-Branch Membership Persistence -/

/-- **Keyed-driver initial-branch membership persistence**: mirrors
`modalExpandBranchesGen_openBranch_initial_mem` (`CompletenessLoop.lean`) for the bespoke
`modalExpandBranchesS4Keyed` driver -- needed since that driver is not an instance of
`modalExpandBranchesGen`, so the generic lemma does not apply directly. Consumed by
`modalTableauS4Keyed_complete` (`FrameCompleteness.lean`) to recover `F(φ0)@0 ∈ b` from the
final open branch. Uses `modalStepBranchS4Keyed_branch_superset` (old branch content survives
into every child) in place of the generic `modalStepBranchGen_mem_preserved`, and the
territory-local `modalStepBranchS4Keyed_newExps_const` for the length-matching step. -/
theorem modalExpandBranchesS4Keyed_openBranch_initial_mem
    (φ₀ : Proposition Atom) (fuel : Nat)
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      keyss.length = branches.length →
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesS4Keyed φ₀ branches expandedSets accs keyss fuel = .openBranch bR aR →
        sf ∈ bR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss _hlen _hlenA _hlenK hAll bR aR h
    simp only [modalExpandBranchesS4Keyed] at h
    cases hfs : (branches.zip accs).findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | none => simp only [hfs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨pb, pa⟩ := p
      simp only [hfs] at h
      injection h with hp1 hp2
      obtain ⟨q, hqmem, hf⟩ := List.exists_of_findSome?_eq_some hfs
      obtain ⟨qb, qa⟩ := q
      simp only [] at hf
      by_cases hcl : isModalClosed qb = true
      · rw [if_pos hcl] at hf
        exact absurd hf (by simp)
      · rw [if_neg hcl] at hf
        have hq0mem : qb ∈ branches := (List.of_mem_zip hqmem).1
        have hqp : (qb, qa) = (pb, pa) := Option.some.inj hf
        have hqfst : qb = bR := by
          have : qb = pb := congrArg Prod.fst hqp
          rw [this]; exact hp1
        rw [hqfst] at hq0mem
        exact hAll bR hq0mem
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hAll bR aR h
    simp only [modalExpandBranchesS4Keyed] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        pendingKeys.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        doneKeys.length = done.length →
        (∀ bp ∈ pending, sf ∈ bp) →
        (∀ bd ∈ done, sf ∈ bd) →
        modalExpandBranchesS4Keyed.processNext φ₀ fuel' pending pendingExp pendingAccs pendingKeys
            done doneExp doneAccs doneKeys = .openBranch bR aR →
        sf ∈ bR from
      key branches expandedSets accs keyss [] [] [] [] hlen hlenA hlenK rfl rfl rfl hAll (by simp)
        (by simpa [modalExpandBranchesS4Keyed] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        _ _ _ _ _ _ _ _ hinner
      simp [modalExpandBranchesS4Keyed.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hlength_p hlenP_accs hlenP_keys hdlength hdAccs hdKeys hAll_p hAll_d hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          cases pendingKeys with
          | nil => simp at hlenP_keys
          | cons k restKs =>
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenP_accs
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenP_keys
            simp only [modalExpandBranchesS4Keyed.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              have hAll_bt : ∀ bp ∈ bt, sf ∈ bp := fun bp hbp => hAll_p bp (by simp [hbp])
              have hAll_done_bh : ∀ bd ∈ done ++ [bh], sf ∈ bd := by
                intro bd hbd
                simp only [List.mem_append, List.mem_singleton] at hbd
                rcases hbd with hd | heq
                · exact hAll_d bd hd
                · subst heq; exact hAll_p bd (by simp)
              exact ih_inner es restAs restKs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                (doneKeys ++ [k]) hlength_p hlenP_accs hlenP_keys
                (by simp [hdlength]) (by simp [hdAccs]) (by simp [hdKeys])
                hAll_bt hAll_done_bh hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep : modalStepBranchS4Keyed φ₀ bh e a k with
              | none =>
                rw [hstep] at hinner
                have hbeq : bh = bR ∧ a = aR := by cases hinner; exact ⟨rfl, rfl⟩
                exact hbeq.1 ▸ hAll_p bh (by simp)
              | some step =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := step
                rw [hstep] at hinner
                have hbh_sf : sf ∈ bh := hAll_p bh (by simp)
                have hNewBs_sf : ∀ b' ∈ newBs, sf ∈ b' :=
                  fun b' hb' => modalStepBranchS4Keyed_branch_superset φ₀ bh e a k newBs newExps
                    newAcc keys' hstep b' hb' sf hbh_sf
                have hLenNBE : newExps.length = newBs.length := by
                  obtain ⟨newExp, hEq⟩ :=
                    modalStepBranchS4Keyed_newExps_const φ₀ bh e a k newBs newExps newAcc keys'
                      hstep
                  simp [hEq]
                exact ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
                  (by simp [hdlength, hlength_p, hLenNBE])
                  (by simp [hdAccs, hlenP_accs])
                  (by simp [hdKeys, hlenP_keys])
                  (fun b' hb'_mem => by
                    simp only [List.mem_append] at hb'_mem
                    rcases hb'_mem with (hd | hn) | hbt
                    · exact hAll_d b' hd
                    · exact hNewBs_sf b' hn
                    · exact hAll_p b' (by simp [hbt]))
                  bR aR hinner

end Cslib.Logic.Modal.Tableau

end
