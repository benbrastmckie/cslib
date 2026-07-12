# Research Report — Task 486: Rework PR #662 into a ~300 LOC Modal Soundness Package on #607

- **Task**: 486
- **Type**: cslib (research only — no Lean files edited)
- **Session**: sess_1783891828_7982f5_research
- **Date**: 2026-07-12
- **Base PR**: #607 (`fmontesi/connectives`), local mirror branch `pr607` (tip `c2ec2962`)
- **Fork source**: #662 (`feat/modal-formula-primitives` = `backup/662-pre-stack-jul12`, tip `8d7a061e`)

---

## 0. Executive Summary (read this first — the task premise needs a correction)

The task brief assumes the modal‑cube **satisfaction lemmas + frame‑condition soundness/canonicity**
must be *ported from the fork onto a bare #607*, to the tune of ~300 new LOC. **That premise is
factually wrong against the current repository state.** Verified findings:

1. **#607 already owns the entire cube soundness/canonicity development.** `pr607`'s
   `Cslib/Logics/Modal/Basic.lean` and `Cslib/Logics/Modal/Cube.lean` already contain the full
   theorem set: `Satisfies.k`, `.dual`, `.t`, `.t_refl`, `.t_box_diamond`, `.b`, `.b_symm`,
   `.four`, `.four_trans`, `.five`, `.five_rightEuclidean`, `.d`, `.d_serial`, plus `Proposition.valid`,
   `logic`, all 15 cube logic definitions, the `Order` inclusion lemmas, and `K.k_valid`/`T.t_valid`.
   This is **verified identical** (modulo docstrings) between `pr607`, the fork `8d7a061e`, and local
   `main`. It is also present in the true upstream `upstream/fmontesi/connectives` (`Modal/Basic.lean`
   differs from `pr607` by only 22 lines; `Cube.lean`/`Denotation.lean`/`LogicalEquivalence.lean` are
   byte‑identical). The authorship header on #607's version is *Fabrizio Montesi, Marianna Girlando* —
   this is fmontesi's own work, not #662's.

2. **Therefore a "port the cube soundness onto #607" package would DUPLICATE content #607 already
   ships** — a direct violation of CSLib's reuse‑first policy. A stacked PR #662 measured as a diff
   against #607 *cannot* re‑add these lemmas as new lines.

3. **The only genuinely non‑duplicative delta #662 has over #607 is the primitive‑basis change**
   (the both‑primitive `{atom, not, and, diamond, box}` design). That is exactly what **task 477
   already implemented** as a **+66/−17 (net +49) diff**, and its worktree/branch
   (`task-477-pr662-stack-607` / `/home/benjamin/Projects/cslib-task-477-pr662-stack-607`) has since
   been **deleted** (confirmed: branch absent from `git branch -a`, worktree dir gone). That work is
   lost and must be reconstructed.

4. **A ~300 LOC self‑contained, non‑duplicative package IS still achievable**, but its composition is
   different from the brief. It is: **(A) reconstruct task 477's both‑primitive refactor** (~80 LOC
   diff) **+ (B) complete the `Cube.lean` Validity section and add a new Canonicity section** — because
   #607 shipped Cube‑level validity wrappers for *only* K and T (`K.k_valid`, `T.t_valid`) and **zero**
   Cube‑level canonicity (frame‑determination) theorems. Adding the missing B/4/5/D validity wrappers
   and the six frame‑determination wrappers is genuinely new, self‑contained, excludes Metalogic, and
   naturally reaches ~200–300 LOC.

The Basic.lean per‑world soundness (`Satisfies.b/.four/.five/.d`) and canonicity
(`Satisfies.*_refl/_symm/_trans/_rightEuclidean/_serial`) proofs are **already done and green in #607**;
the new content is the thin `∈ logic` **Cube‑level wrappers** plus the both‑primitive base change. This
must be flagged to the planner and to fmontesi/Waring (design decision back 23 July) because it changes
the shape of the PR from what the brief describes.

---

## 1. Ground‑truth branch map (verified)

| Branch / ref | Tip | Modal primitives | Operators layer | Cube soundness present? | Notes |
|---|---|---|---|---|---|
| `pr607` (= #607 mirror) | `c2ec2962` | `{atom, not, and, diamond}`; box/or/impl/iff derived | split `Operators/{And,Or,Impl,Not,Box,Diamond,Iff,Tensor}.lean` (`HasBox`/`HasDiamond`/…) | **YES — full set** | No `Connectives.lean`. `references.bib` has `Blackburn2001` only. |
| `upstream/fmontesi/connectives` (true #607) | `ddc2c9b8` | same as pr607 | monolithic `Operators.lean` | **YES** | pr607 is fmontesi/connectives + a local split of Operators + minor drift; Modal is materially identical. |
| `feat/modal-formula-primitives` = `backup/662-pre-stack-jul12` (#662 fork) | `8d7a061e` | `{atom, bot, imp, box}`; neg/and/or/diamond derived (Łukasiewicz) | fork‑local `ModalConnectives` in `Cslib/Foundations/Logic/Connectives.lean` | **YES — same set** | ~522 commits behind upstream. This is the PORT‑FROM source. **Not** a +39/−17 stub — the brief's claim is stale. |
| `main` (local) | diverged | `{atom, bot, imp, box}` (= fork) + deep `Metalogic/`, `ProofSystem`?, `Tableau`, `FromPropositional`, `InterSystem` | fork‑style | **YES — identical to fork** | Wrong base (unrelated local Tableau/Metalogic dev). Its `Cube.lean` is theorem‑identical to pr607 (still only K/T validity). |

Key corrections to the task brief:
- The "live #662 = tiny +39/−17 diff on fmontesi/connectives" description does **not** match any current
  ref. `feat/modal-formula-primitives` currently points at the fork's pre‑stack `{atom,bot,imp,box}`
  version (`8d7a061e`), which is a large diff, not a stub. The task‑477 stub branch is gone.
- The fork's richer files are **not** richer in cube content than #607 — they carry the *same* cube
  theorems on a *different primitive basis*.

---

## 2. What #607 already contains vs. what is genuinely new (the reuse audit)

### Already in #607 (`pr607`) — DO NOT re‑add (would duplicate):

`Cslib/Logics/Modal/Basic.lean` (diamond‑primitive, box derived `□φ := ¬◇¬φ`):
- Satisfaction chars: `neg`/`Satisfies.not_iff_not`, `.and_iff_and`, `.or_iff_or`, `.impl_iff_impl`,
  `.iff_iff_iff`, `.box_iff_forall`, `.diamond_iff_exists`.
- Soundness: `Satisfies.k`, `.dual`, `.t`, `.b`, `.four`, `.five`, `.d`.
- Canonicity (converse frame correspondence): `Satisfies.t_refl`, `.b_symm`, `.four_trans`,
  `.five_rightEuclidean`, `.d_serial`, plus `Satisfies.t_box_diamond`.
- `Proposition.valid`, `logic`.

`Cslib/Logics/Modal/Cube.lean`:
- All 15 logic defs (`K,T,B,Four,Five,D,K45,D4,D5,D45,DB,TB,KB5,S4,S5`).
- `Order` inclusions (`k_subset_d/_b/_four/_five`, `d_subset_t`, `k_subset_t`).
- `Validity`: **only** `K.k_valid`, `T.t_valid`.

### Genuinely NEW (non‑duplicative) content available to #662:

| New item | Where | ~LOC | Why non‑duplicative |
|---|---|---|---|
| Both‑primitive `Proposition` (`box` as 5th constructor) + primitive `.box` Satisfies clause | Basic.lean | rewrite | Changes the *type*, not re‑stating a lemma |
| `box_iff_forall` collapses to `Iff.rfl`; `dual` reworked to genuine classical proof; add `box_iff_not_diamond_not` | Basic.lean | ~25 | Proof shape changes under both‑primitive |
| `box` denotation clause | Denotation.lean | ~1 | New constructor case |
| `box` `Context`/`fill`/`Congruence` arm | LogicalEquivalence.lean | ~9 | New constructor case |
| `ChagrovZakharyaschev1997` bib entry | references.bib | ~10 | Not on pr607 |
| **`B.b_valid`, `Four.four_valid`, `Five.five_valid`, `D.d_valid`** (Cube‑level soundness wrappers) | Cube.lean | ~35 | #607 ships only K,T wrappers |
| **New `Canonicity` section**: `T.t_canonical`/`B.b_canonical`/`Four.four_canonical`/`Five.five_canonical`/`D.d_canonical` (Cube‑level frame‑determination wrappers over `Satisfies.*_refl/_symm/…`) | Cube.lean | ~70–110 | #607 has **zero** Cube‑level canonicity |
| Optional: `S4`/`S5` combined‑axiom validity demos | Cube.lean | ~30 | Not present |

**Net genuinely‑new footprint: ~180–290 LOC** → lands in the ~300 target (hard max 500) without
duplicating a single #607 lemma. This is the "most natural self‑contained package."

---

## 3. File‑by‑file inventory of the ~300 LOC package (source → ported form)

The package is **PORTED onto #607's split `Operators` typeclasses**, NOT rebased from the fork. The
fork‑local `ModalConnectives`/`Connectives.lean` layer is **dropped entirely** (resolves former task
469; `pr607` has no `Connectives.lean`). The both‑primitive base is #607's `{atom,not,and,diamond}` +
a new `box` constructor (NOT the fork's `{atom,bot,imp,box}`).

### 3.1 `Cslib/Logics/Modal/Basic.lean` (reconstruct task 477; ~ +66/−17)

| Element | #607 (diamond‑prim) baseline | Ported both‑primitive form | Source of proof |
|---|---|---|---|
| `Proposition` | `{atom, not, and, diamond}` | add `\| box (φ)` → `{atom, not, and, diamond, box}` | task 477 |
| `HasBox` instance | `{box := Proposition.box}` where `box := ¬◇¬φ` (a `def`) | `{box := Proposition.box}` where `box` is the constructor; **remove** the derived `def Proposition.box` | task 477 |
| `Proposition.box_def` | `φ.box = □φ := rfl` | keep as `rfl` (constructor) | task 477 |
| `Satisfies` | 4 clauses (`.diamond => ∃ w', m.r w w' ∧ …`) | add `\| .box φ => ∀ w', m.r w w' → Satisfies m w' φ` | fork `Satisfies` `.box` clause |
| `Satisfies.box_iff_forall` | `by grind [=_ box_def, box]` | `Iff.rfl` (now definitional) | fork (box‑prim) |
| `Satisfies.diamond_iff_exists` | `by rfl` | `by rfl` (unchanged) | pr607 |
| `Satisfies.dual` (`◇φ ↔ ¬□¬φ`) | genuine proof (box derived) | **genuine classical proof** — neither direction definitional; `simp only [iff_iff_iff, diamond_iff_exists, not_iff_not, box_iff_forall]` then `constructor`/`by_contra`/`push Not` | task 477 (see §5) |
| `Satisfies.box_iff_not_diamond_not` (new) | — | add `□φ ↔ ¬◇¬φ` companion | task 477 |
| `.not_iff_not/.and_iff_and/.or_iff_or/.impl_iff_impl/.iff_iff_iff` | present | **unchanged** (not/and stay primitive; or/impl/iff stay derived on #607's `Operators`) | pr607 |
| Soundness `.k/.t/.b/.four/.five/.d` + canonicity `.t_refl/.b_symm/.four_trans/.five_rightEuclidean/.d_serial/.t_box_diamond` | present, green | **unchanged** — they already type‑check against the both‑primitive box because they are stated via `box_iff_forall`/`diamond_iff_exists`, both still available | pr607 (verify green after box change) |

> Note: #607's `.k` and several canonicity converses are proved by bare `grind`. After box becomes
> primitive, `grind` still closes them because `box_iff_forall`/`diamond_iff_exists` remain
> `@[scoped grind =]`. Task 477 confirmed this empirically for the Modal module in isolation. The
> planner must re‑verify each with `lake build` after the constructor change.

### 3.2 `Cslib/Logics/Modal/Denotation.lean` (~ +1)
Add `box` case to `Proposition.denotation`: `{w | ∀ w', m.r w w' → w' ∈ φ.denotation m}`. Existing
`induction … <;> grind` proofs (`satisfies_mem_denotation`, `not_denotation`, `theoryEq_denotation_eq`)
close unchanged. (task 477)

### 3.3 `Cslib/Logics/Modal/LogicalEquivalence.lean` (~ +9)
Add `box` `Proposition.Context` constructor, its `fill` clause, and a `Congruence` induction arm
mirroring `diamond`'s arm with `∀`/`intro` in place of `∃`/`rintro`. The `HasLogicalEquivalence`
instance is **already present on pr607** — no framework migration needed (task 477 correction to the
original research report). (task 477)

### 3.4 `Cslib/Logics/Modal/Cube.lean` (~ +100–140 — the NEW substance)

Complete the `Validity` section and add a `Canonicity` section. Pattern to follow is #607's existing
`K.k_valid`/`T.t_valid`. Each theorem is a thin `∈ logic`/frame‑class wrapper over the already‑green
`Satisfies.*` lemmas:

```lean
section Validity
open scoped Proposition
/-- Axiom B is valid in logic B. -/
theorem B.b_valid : (φ → □◇φ : Proposition Atom) ∈ B World Atom := by
  intro _ h; grind [Satisfies.b (instSymm := (by assumption))]
/-- Axiom 4 is valid in logic 4. -/
theorem Four.four_valid : (◇◇φ → ◇φ : Proposition Atom) ∈ Four World Atom := by
  intro _ h; grind [Satisfies.four]
/-- Axiom 5 is valid in logic 5. -/
theorem Five.five_valid : (◇φ → □◇φ : Proposition Atom) ∈ Five World Atom := by
  intro _ h; grind [Satisfies.five]
/-- Axiom D is valid in logic D. -/
theorem D.d_valid : (□φ → ◇φ : Proposition Atom) ∈ D World Atom := by
  intro _ h; grind [Satisfies.d]
end Validity

section Canonicity
/-! Frame‑determination direction: the axiom's global validity forces the frame condition.
    Cube‑level wrappers over the Basic.lean converse lemmas; #607 ships none of these. -/
/-- Any frame validating T is reflexive. -/
theorem T.t_canonical [Nonempty Atom] {r : World → World → Prop}
    (h : ∀ {v} {w} {φ : Proposition Atom}, ⇓Modal[⟨r,v⟩,w ⊨ φ → ◇φ]) : Std.Refl r :=
  Satisfies.t_refl h
-- similarly B.b_canonical (Std.Symm) via Satisfies.b_symm,
--            Four.four_canonical (IsTrans) via Satisfies.four_trans,
--            Five.five_canonical (Relation.RightEuclidean) via Satisfies.five_rightEuclidean,
--            D.d_canonical (Relation.Serial) via Satisfies.d_serial.
end Canonicity
```

The exact `grind`/`instSymm := by assumption` invocations for the validity wrappers should be tested
with `lean_multi_attempt`; the `T.t_valid` precedent (`grind [Satisfies.t (instRefl := (by assumption))]`)
is the template.

### 3.5 `references.bib` (~ +10)
Add `ChagrovZakharyaschev1997` (present on the fork, absent on pr607). Do **not** add `Avigad2022`
(the fork needs it for the Łukasiewicz encoding note, which does **not** apply to the both‑primitive
base that keeps not/and primitive). (task 477)

---

## 4. Base branch / worktree strategy (confirmed — reuse task 477's pattern)

**Do NOT work on `main`** (diverged with unrelated `Tableau/`, `Metalogic/`, `ProofSystem`, `InterSystem`
local dev) and **do NOT build on `feat/modal-formula-primitives`** (fork `{atom,bot,imp,box}` base, ~522
commits behind, wrong primitive basis and wrong Operators layer).

Recommended (mirrors task 477, whose worktree was deleted):

```bash
# Fresh branch off the #607 base:
git branch task-486-pr662-modal-package pr607
git worktree add /home/benjamin/Projects/cslib-task-486-pr662-modal-package task-486-pr662-modal-package
# All edits + `lake build`/`lake test` happen inside that worktree.
```

Deliver a **clean single‑commit diff on base `fmontesi/connectives`**. Because #607 already contains
the cube, the #662 diff is a **refactor + Cube extension**, not an additive port. The final PR branch
that actually goes to `leanprover/cslib` is prepared by `/pr` by rebasing this work onto
`fmontesi/connectives` (not `main`).

> Caveat inherited from task 477: whole‑library `lake build`/`checkInitImports`/`shake`/`test` on
> `pr607` is **blocked by a pre‑existing #607 defect** in `Cslib/Logics/HML/LogicalEquivalence.lean`
> (still instantiates the old 3‑arg `LogicalEquivalence` against #607's own 4‑arg signature). This is
> #607's bug, out of scope for #662. Module‑scoped `lake build Cslib.Logics.Modal.*` is the practical
> green gate; full‑library CI must wait on fmontesi fixing HML. Flag this to the planner as a known
> non‑#662 blocker.

---

## 5. Proof sketches for the harder both‑primitive directions

The proof shape changes **only** where box/diamond duality is invoked, because under both‑primitive
neither `□φ ↔ ¬◇¬φ` nor `◇φ ↔ ¬□¬φ` is definitional (on the fork, box‑prim makes `dual` `Iff.rfl`; on
#607, diamond‑prim makes it a one‑direction proof; both‑primitive makes **both** directions need
classical reasoning).

### 5.1 `Satisfies.dual : ◇φ ↔ ¬□¬φ` (both‑primitive)
```lean
theorem Satisfies.dual : ⇓Modal[m,w ⊨ ◇φ ↔ ¬□¬φ] := by
  simp only [iff_iff_iff, diamond_iff_exists, not_iff_not, box_iff_forall]
  constructor
  · rintro ⟨w', hr, hs⟩ hbox      -- ◇ → ¬□¬ : direct
    exact (hbox w' hr) hs
  · intro h                        -- ¬□¬ → ◇ : classical
    by_contra hc
    push Not at hc                 -- codebase‑preferred non‑deprecated push (NOT push_neg)
    exact h (fun w' hr => hc w' hr)
```
The forward direction is intuitionistic; the backward direction needs `by_contra`/`push Not`
(excluded middle). This is exactly the fork's `Satisfies.diamond_iff` argument, re‑landed as `dual`.

### 5.2 `Satisfies.five` (5 = right‑Euclidean), both‑primitive box
```lean
theorem Satisfies.five [Relation.RightEuclidean m.r] (φ) : ⇓Modal[m,w ⊨ ◇φ → □◇φ] := by
  intro h                                   -- h : ◇φ at w
  obtain ⟨u, hwu, hu⟩ := diamond_iff_exists.mp h
  refine box_iff_forall.mpr (fun v hwv => diamond_iff_exists.mpr ?_)
  exact ⟨u, Relation.RightEuclidean.rightEuclidean hwv hwu, hu⟩
```
Because box is now a *primitive* whose satisfaction clause is `∀ w', r w w' → …`, the `□◇φ` goal is
introduced via `box_iff_forall.mpr` and a `∀ v, r w v → …` intro; with a *derived* box you would instead
unfold `¬◇¬` and push negations. The Euclidean step: from `r w v` and `r w u` conclude `r v u`
(`rightEuclidean : r a b → r a c → r b c`). #607's existing proof does this via `grind` +
`Relation.RightEuclidean.rightEuclidean`; the explicit version above is a drop‑in if `grind` regresses.

### 5.3 `Satisfies.b_symm` (canonicity of B), both‑primitive box
```lean
theorem Satisfies.b_symm {r} [Nonempty Atom]
    (h : ∀ {v w} {φ : Proposition Atom}, ⇓Modal[⟨r,v⟩,w ⊨ φ → □◇φ]) : Std.Symm r where
  symm {w₁ w₂} hr := by
    have a := Classical.arbitrary Atom
    let v : World → Atom → Prop := fun w' _ => w' = w₁     -- valuation true only at w₁
    have h₁ := @h v w₁ (.atom a)                            -- ⊨ atom a → □◇ atom a at w₁
    -- atom a holds at w₁; so □◇(atom a) at w₁; instantiate box at w₂ (via hr : r w₁ w₂),
    -- giving ◇(atom a) at w₂, i.e. ∃ u, r w₂ u ∧ u = w₁ ⇒ r w₂ w₁.
    grind
```
The `let v := fun w' _ => w' = w₁` "spy" valuation is the standard canonicity gadget: it makes
`atom a` true at exactly `w₁`, so any `◇(atom a)` witness *must* be `w₁`, extracting the relational
fact. With primitive box, the `□◇` elimination is `box_iff_forall.mp … hr` then
`diamond_iff_exists.mp`; #607 discharges this with `simp [impl_iff_impl] at h₁; grind`. Keep the
`grind` first; fall back to the explicit `box_iff_forall.mp`/`diamond_iff_exists.mp` chain if needed.

**General note for the planner:** every Basic.lean soundness/canonicity proof on #607 is written
against `box_iff_forall`/`diamond_iff_exists` (both `@[scoped grind =]`), *not* against the box/diamond
`def`s. That is precisely why they survive the constructor swap with at most a `grind` retune. The risk
surface is confined to `dual`, `box_iff_forall` (→ `Iff.rfl`), and any lemma that unfolded the old
derived `box` `def` — audit for `Proposition.box`/`box_def` unfolds.

---

## 6. Mathlib / infrastructure lemmas for the frame‑correspondence proofs (verified real)

All of these are **already used in the green proofs on `pr607`/fork** (hence verified by compilation),
so no speculative lemma names are introduced. Relation typeclasses live in CSLib, not Mathlib:

| Symbol | Location | Used for |
|---|---|---|
| `Std.Refl` / `Std.Refl.refl` | Std/Mathlib | T soundness/canonicity |
| `Std.Symm` / `Std.Symm.symm` | Std/Mathlib | B soundness/canonicity |
| `IsTrans` / `IsTrans.trans` | Mathlib.Order | 4 soundness/canonicity |
| `Relation.Serial` / `.serial` | **CSLib** `Cslib/Foundations/Relation/Defs.lean:74` | D soundness/canonicity |
| `Relation.RightEuclidean` / `.rightEuclidean` | **CSLib** `Cslib/Foundations/Relation/Defs.lean:49` | 5 soundness/canonicity |
| `Cslib/Foundations/Relation/Euclidean.lean` | CSLib | `refl_serial`, `[Std.Refl r] → Serial r` instance, Euclidean↔symm/trans bridges (`d_subset_t` uses `refl_serial`) |
| `Classical.arbitrary`, `Classical.em` | Mathlib.Logic | canonicity "spy‑valuation" gadget + classical `dual`/`or_iff` |
| `Set.ext_iff`, `Set.mem_setOf_eq`, `subset_def` | Mathlib.Data.Set.Basic | `TheoryEq.ext_iff`, Cube `Order` lemmas |

No new Mathlib lemma discovery is required; the frame‑correspondence infrastructure is complete on
#607. (Search tools were intentionally not spent on rate‑limited queries because every needed name is
already present in compiling source — confirmed via `git grep` against `pr607`.)

---

## 7. EXCLUDED from the package (keeps the diff self‑contained & reviewable)

Explicitly **NOT** part of task 486 (each is a separate downstream PR — cf. tasks 478–484):

- `Cslib/Logics/Modal/FromPropositional.lean` — entangled with the #648 primitive‑`bot`
  propositional decision (mutually exclusive with #607's `Propositional/Defs.lean`; deferred to
  fmontesi/Waring, back 23 July). **Exclude.**
- `Cslib/Logics/Modal/Metalogic/` in full — MCS, `GenericMCSBridge`, canonical‑model `Completeness`,
  `DeductionTheorem`, `DerivationTree`, `Soundness` (proof‑theoretic), `Systems/*`. **Exclude.**
- `Cslib/Logics/Modal/Metalogic/InterSystem/` — `Conservativity`, `AxiomSubsumption`,
  `LiftViaMorphism`, `Lifting`. **Exclude.**
- Any `ProofSystem/` / `Tableau/` development on `main`. **Exclude.**
- The fork‑local `Cslib/Foundations/Logic/Connectives.lean` (`ModalConnectives`) — **dropped**; reuse
  #607's split `Operators/*` typeclasses. **Exclude / delete from scope.**
- Do **not** touch `Cslib/Logics/HML/LogicalEquivalence.lean` (the pre‑existing #607 blocker) — out of
  #662 scope.

The included set is confined to `Modal/{Basic,Cube,Denotation,LogicalEquivalence}.lean` +
`references.bib` — four Modal files plus a bib entry, all under `Cslib.Logics.Modal`, no Foundations
churn beyond reusing existing typeclasses.

---

## 8. Recommendation to planner / orchestrator

1. **Accept the corrected package composition** (§2–§3): reconstruct task 477's both‑primitive refactor
   **and** extend `Cube.lean` with the missing B/4/5/D validity wrappers + a new Canonicity section.
   This is the only ~300 LOC framing that is non‑duplicative and self‑contained. Do **not** re‑port the
   Basic.lean soundness/canonicity lemmas — #607 owns them.
2. **Reconstruct, don't recover** task 477's diff — its branch/worktree are deleted; the summary at
   `specs/477_refactor_pr_662_stack_on_607/summaries/01_refactor-pr-662-stack-607-summary.md` is the
   authoritative reconstruction spec for §3.1–§3.3/§3.5.
3. **Zero‑debt gate**: the whole package is proof‑complete with zero `sorry`/axioms — every hard
   direction has a green precedent on #607 or the fork. No sorry deferral is needed or permitted.
4. **Flag the premise correction to the human/fmontesi**: whether #662 should *also* re‑own the cube
   (e.g. #607 dropping its Modal cube so #662 contributes it both‑primitive as ~300 new LOC) is a PR‑
   boundary/ownership decision for fmontesi (back 23 July), not something research can settle. If that
   ownership transfer is chosen, the "~300 new LOC" target is met literally; if not, the honest net
   size is ~180–290 LOC of new Cube wrappers + refactor.
5. **CI reality**: gate on module‑scoped `lake build Cslib.Logics.Modal.Basic/.Cube/.Denotation/
   .LogicalEquivalence` + Modal‑scoped tests; full‑library CI is blocked by #607's own HML defect
   (not #662's).

---

## 9. Verification log

- `git ls-tree` / `git show` on `pr607`, `upstream/fmontesi/connectives`, `feat/modal-formula-primitives`
  (`8d7a061e`), `backup/662-pre-stack-jul12`, `main` — branch/primitive/soundness map (§1).
- `git diff --stat upstream/fmontesi/connectives pr607` — confirmed pr607 = fmontesi/connectives +
  Operators split; Modal materially identical.
- `git grep` on `pr607` — `Relation.Serial` (Defs.lean:74), `Relation.RightEuclidean` (Defs.lean:49),
  Euclidean.lean bridges; `references.bib` has `Blackburn2001`, lacks `ChagrovZakharyaschev1997`;
  `Connectives.lean` absent from `pr607`.
- Task‑477 branch/worktree confirmed **deleted** (`git branch --list`, `ls` on worktree dir).
- Lean LSP search tools intentionally not spent (all lemma names verified via compiling source);
  blocked tools `lean_diagnostic_messages`/`lean_file_outline` not used.
