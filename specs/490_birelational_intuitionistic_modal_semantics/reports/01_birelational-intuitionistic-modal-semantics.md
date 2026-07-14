# Research Report: Task 490 — Birelational (Intuitionistic Kripke) Modal Semantics

**Task type**: cslib | **Session**: sess_1784011298_752245_490 | **Date**: 2026-07-14

## Objective

Define the semantic foundation for intuitionistic and minimal modal metalogic: intuitionistic
Kripke frames with **two** relations — the intuitionistic preorder `≤` and the modal
accessibility `R` — plus the heredity/monotonicity condition and the F1/F2 (up/down) confluence
conditions relating `≤` and `R`. Define a forcing relation (`Satisfies`) for the fully-primitive
modal `Proposition {atom, bot, imp, and, or, box, diamond}` (PR #662, task 487) over these
frames. This is the layer that intuitionistic completeness (tasks 492/493/494) and minimal
completeness (task 495) build on.

## Executive Summary (actionable)

- **Both hard prerequisites already exist in the tree** and require no new work:
  1. The fully-primitive modal `Proposition` + classical `Satisfies` live in
     `Cslib/Logics/Modal/Basic.lean` (task 487 / PR #662), namespace `Cslib.Logic.Modal`. Box
     and diamond are **independent primitive constructors** (`.box`, `.diamond`), and `∨`/`⊥`
     are primitive — exactly what intuitionistic semantics needs (◇ ≠ ¬□¬, ∨ not definable).
  2. The intuitionistic/minimal **propositional** Kripke pattern to mirror lives in
     `Cslib/Logics/Propositional/Semantics/Kripke.lean` (`KripkeModel`, `IForces`,
     `iforces_persistence`, `IValid`, `MValid`). The new modal file is a direct extension of
     this file's design.
- **Recommended approach**: add one new file `Cslib/Logics/Modal/Semantics/Birelational.lean`
  (new `Semantics/` subdir, paralleling `Propositional/Semantics/`), reusing the primitive modal
  `Proposition` from `Modal/Basic.lean` and the `Preorder`/upward-closure machinery from the PL
  Kripke file. **No new `Proposition` datatype, no new connective typeclasses** — the reuse-first
  gate is satisfied by `Modal.Proposition` + `HasBox`/`HasDia`/`HasAnd`/`HasOr`/`HasBot` already
  in `Foundations/Logic/Connectives.lean`.
- **Zero-debt feasibility**: HIGH. Persistence/monotonicity is a routine structural induction
  (the PL file already proves the `atom/bot/imp/and/or` cases; only `box`/`diamond` cases are
  new, and each is a short argument from the frame conditions). No `sorry`, no new axiom needed.

## Literature Proof Structure (Simpson 1994, birelational / Fischer-Servi semantics)

Ground-truth source: **[Simpson1994]** *The Proof Theory and Semantics of Intuitionistic Modal
Logic* (PhD, Edinburgh, LFCS ECS-LFCS-94-308), Chapter 3. Global corpus:
`~/Projects/Literature/simpson_1994_intuitionisticmodallogic/` (chunks 0193–0214). Corroborating:
**[Wijesekera1990]** *Constructive Modal Logics I* (CK-style, non-distributive ◇) and
**[BiermanDePaiva2000]** *On an Intuitionistic Modal Logic* (CK).

The frames Simpson settles on ("Fischer Servi / Plotkin–Stirling / Ewald" birelational models,
chunks 0211–0214) carry a set `W` with **two** relations: a preorder `≤` and a modal relation
`R`. Simpson's problem statement (chunk 0193): the naïve modal clauses break the **monotonicity
lemma** (his Lemma 2.2.1 = persistence of forcing under `≤`). He applies **both** remedies:

1. **Modify the □ clause** to build monotonicity in (clause 3.2), and
2. **Impose frame conditions** F1/F2 on the `≤`/`R` interaction so the standard ◇ clause (3.5)
   also stays monotone and the IK axioms are validated.

### Satisfaction/forcing clauses (Simpson, chunk 0214; modalities only — non-modal clauses are the standard intuitionistic ones)

Let `w ⊩ A` denote forcing. Non-modal connectives use the ordinary intuitionistic Kripke clauses
(atom = valuation; `∧` local; `∨` local; `⊥` = `botForces`; `→` universally quantified over
`≥`-worlds) — these are *identical* to `PL.IForces` in the existing PL Kripke file.

- **Box** (clause **3.2**, "for all `w' ≥ w`, for all `v` with `w' R v`, `v ⊩ A`"):
  ```
  w ⊩ □A   iff   ∀ w', w ≤ w' → ∀ v, R w' v → v ⊩ A
  ```
  i.e. □ quantifies over the composition **`≤ ∘ R`**. (Task brief: "□ quantifying over ≤∘R".)

- **Diamond** (clause **3.5**, the standard existential clause):
  ```
  w ⊩ ◇A   iff   ∃ v, R w v ∧ v ⊩ A
  ```
  i.e. ◇ quantifies over **`R`** alone. (Task brief: "◇ over R".) Monotonicity of ◇ is *not*
  automatic here; it is delivered by frame condition **F1**.

- **Implication** (intuitionistic, chunk cross-ref page 22):
  ```
  w ⊩ A → B   iff   ∀ w', w ≤ w' → w' ⊩ A → w' ⊩ B
  ```

### Frame conditions (Simpson, chunk 0213 — the two commuting-square conditions)

Given `≤` a preorder and `R` the modal relation on `W`:

- **(F1) up-confluence** (`≤ ; R ⊆ R ; ≤`):
  ```
  ∀ w w' v, w ≤ w' → R w v → ∃ v', R w' v' ∧ v ≤ v'
  ```
  *Diagram*: `w ≤ w'`, `w R v` ⟹ exists `v' ≥ v` with `w' R v'`. **This is exactly what makes
  the standard ◇ clause (3.5) monotone** (see monotonicity proof below).

- **(F2) down-confluence** (`R ; ≤ ⊆ ≤ ; R`):
  ```
  ∀ w v v', R w v → v ≤ v' → ∃ w', w ≤ w' ∧ R w' v'
  ```
  *Diagram*: `w R v`, `v ≤ v'` ⟹ exists `w' ≥ w` with `w' R v'`. Needed to validate the IK
  interaction axioms (e.g. `◇(A→B) → (□A → ◇B)`, `□(A→B) → (◇A → ◇B)`) and for the □ clause's
  correspondence in the completeness argument (tasks 492–495).

### Heredity / monotonicity lemma (the persistence result to reproduce)

Simpson's monotonicity lemma (persistence): `w ⊩ A` and `w ≤ w'` ⟹ `w' ⊩ A`, by induction on `A`.
- atom/bot: upward-closure of the valuation / `botForces` (heredity built into the model);
- imp/and/or: as in `PL.iforces_persistence` (already proven in-tree);
- **box** (clause 3.2): *no frame condition needed* — the `∀ w' ≥ w` prefix plus transitivity of
  `≤` gives persistence directly (mirrors the `imp` case);
- **diamond** (clause 3.5): uses **F1**. From `w ⊩ ◇A` get `v` with `R w v`, `v ⊩ A`. Given
  `w ≤ w'`, F1 yields `v'` with `R w' v'` and `v ≤ v'`; by the IH (persistence at `v`), `v' ⊩ A`;
  hence `w' ⊩ ◇A`.

### IK vs CK (design note for downstream tasks)

- **IK (Fischer-Servi / Simpson)** = the birelational frames with **both F1 and F2**, `botForces
  = fun _ => False` for the intuitionistic case. This is what tasks 492/493/494 (intuitionistic
  completeness) target. Validates ◇⊥ ↔ ⊥ and ◇(A∨B) ↔ ◇A ∨ ◇B.
- **CK (Wijesekera / Bierman-de Paiva)** is *weaker*: ◇ need not distribute over ∨ or ⊥ (◇⊥ is
  not forced to be equivalent to ⊥). Achieved by a different (fallible-world / non-normal) ◇
  clause. Task 490 as written targets the **IK birelational** clauses (F1/F2 + clause 3.2/3.5),
  which is the correct base for both the intuitionistic (492–494) and minimal (495) siblings
  when `botForces` is generalized (minimal = arbitrary upward-closed `botForces`, exactly as PL's
  `MValid` generalizes `IValid`).

## Reuse Check Protocol Results (CSLib reuse-first)

| Concept | Existing CSLib/Mathlib asset | Reuse verdict |
|---------|------------------------------|---------------|
| Modal formula datatype | `Cslib.Logic.Modal.Proposition` (`Modal/Basic.lean`, primitive box/diamond/and/or/bot) | **REUSE as-is**; do not redefine |
| Box/diamond operators | `HasBox`, `HasDia` (`Foundations/Logic/Connectives.lean:100,112`) | Already instantiated for `Modal.Proposition` |
| `∧`/`∨`/`⊥`/`→` | `HasAnd`/`HasOr`/`Bot`/`ModalConnectives` instances in `Modal/Basic.lean` | REUSE; scoped notation already provided |
| Intuitionistic preorder frame + heredity | `PL.KripkeModel` (`Propositional/Semantics/Kripke.lean`): `Preorder World`, `v_upward_closed`, `bf_upward_closed` | **REUSE the pattern**; extend with the `R` field + F1/F2 |
| Forcing recursion + persistence | `PL.IForces` / `PL.iforces_persistence` (same file) | **REUSE the pattern**; non-modal cases transcribe verbatim |
| Intuitionistic vs minimal validity | `PL.IValid` / `PL.MValid` / `mvalid_implies_ivalid` | REUSE the pattern for `Modal` `IValid`/`MValid` |
| Relation composition (to phrase F1/F2 tersely) | `Cslib.Foundations.Relation.Comp` / `UpTo` (`Foundations/Relation/Defs.lean`) | Optional. `DiamondCommute`/`Commute` (same file) are **NOT** a match — they branch from a common origin, whereas F1/F2 are *sequential-composition inclusions* (`≤;R ⊆ R;≤`). State F1/F2 directly as `∀…∃…`, optionally documenting the `Comp` phrasing. |
| Reflexive/transitive/serial/Euclidean classes | `Std.Refl`, `IsTrans`, `Relation.Serial`, `Relation.RightEuclidean` (used throughout `Modal/Basic.lean`) | REUSE for later frame-class variants (S4-style intuitionistic modal), not needed for the base IK frame |

**Conclusion**: No new abstraction is warranted beyond the birelational `Frame`/`Model` structure
and its forcing relation. Everything else is instantiation/transcription of existing patterns.

## Concrete Lean 4 Definitional Sketches

Namespace note: the Modal namespace is **`Cslib.Logic.Modal`** (singular `Logic`), even though
the directory is `Logics/Modal/`. Follow `Modal/Basic.lean`.

### File placement
`Cslib/Logics/Modal/Semantics/Birelational.lean` (new `Semantics/` subdirectory, paralleling
`Propositional/Semantics/Kripke.lean`). Alternative: put it directly at
`Cslib/Logics/Modal/Birelational.lean` to match Basic.lean's flat layout — either is acceptable;
`Semantics/` is preferred for discoverability given 492–495 will add sibling files. Remember to
add the file to the `Cslib.lean` barrel via `lake exe mk_all --module`.

### Header / imports
```lean
module
public import Cslib.Init
public import Cslib.Logics.Modal.Basic          -- reuse Proposition + connective instances
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Defs.Unbundled
```

### Birelational frame (heredity + F1/F2)
```lean
@[expose] public section
namespace Cslib.Logic.Modal

/-- A birelational (intuitionistic Kripke) frame: a preordered set of worlds carrying a modal
accessibility relation `r`, subject to the up/down confluence conditions relating `≤` and `r`. -/
structure BFrame (World : Type*) [Preorder World] where
  /-- Modal accessibility relation. -/
  r : World → World → Prop
  /-- (F1) up-confluence `≤ ; r ⊆ r ; ≤`: if `w ≤ w'` and `r w v` then some `v' ≥ v` has `r w' v'`. -/
  f1 : ∀ {w w' v : World}, w ≤ w' → r w v → ∃ v', r w' v' ∧ v ≤ v'
  /-- (F2) down-confluence `r ; ≤ ⊆ ≤ ; r`: if `r w v` and `v ≤ v'` then some `w' ≥ w` has `r w' v'`. -/
  f2 : ∀ {w v v' : World}, r w v → v ≤ v' → ∃ w', w ≤ w' ∧ r w' v'

/-- A birelational model adds a heredity (upward-closed) valuation and a `botForces` predicate
(`fun _ => False` for intuitionistic; arbitrary upward-closed for minimal), mirroring
`PL.KripkeModel`. -/
structure BModel (World : Type*) (Atom : Type*) [Preorder World] extends BFrame World where
  /-- Valuation of atoms at each world. -/
  v : World → Atom → Prop
  /-- Falsum-forcing predicate (`fun _ => False` intuitionistically). -/
  botForces : World → Prop
  /-- Heredity: the valuation is upward-closed. -/
  v_upward_closed : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p
  /-- `botForces` is upward-closed. -/
  bf_upward_closed : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w'
```
(You may keep `Frame`/`Model` unbundled — separate `v`/`botForces` args as the PL `IForces` does —
if you prefer to avoid the `extends`; the PL file passes `v`/`bot_forces` as explicit parameters
to `IForces` rather than bundling. Match whichever the planner picks; bundling is cleaner for the
`IValid`/`MValid` statements.)

### Forcing relation (reuses `Modal.Proposition`)
```lean
/-- Birelational forcing for the primitive modal `Proposition`. Non-modal cases match the
intuitionistic PL clauses; `box` quantifies over `≤ ∘ r`; `diamond` over `r`. -/
def BForces [Preorder World] (r : World → World → Prop)
    (v : World → Atom → Prop) (botForces : World → Prop)
    (w : World) : Proposition Atom → Prop
  | .atom p      => v w p
  | .bot         => botForces w
  | .imp φ ψ     => ∀ w', w ≤ w' → BForces r v botForces w' φ → BForces r v botForces w' ψ
  | .and φ ψ     => BForces r v botForces w φ ∧ BForces r v botForces w ψ
  | .or φ ψ      => BForces r v botForces w φ ∨ BForces r v botForces w ψ
  | .box φ       => ∀ w', w ≤ w' → ∀ u, r w' u → BForces r v botForces u φ   -- ≤ ∘ r  (clause 3.2)
  | .diamond φ   => ∃ u, r w u ∧ BForces r v botForces u φ                    -- r      (clause 3.5)
```
Add `@[simp]` reduction lemmas per constructor (`BForces_atom`, `BForces_box`, `BForces_diamond`,
…), exactly as the PL file does for `IForces`.

### Persistence / monotonicity (the key lemma; zero-debt, structural induction)
```lean
/-- Persistence (Simpson's monotonicity lemma): forcing is upward-closed under `≤`. Uses F1 for
the `diamond` case; all other cases are frame-condition-free. -/
theorem bforces_persistence [Preorder World] {F : BFrame World}
    {v : World → Atom → Prop} {botForces : World → Prop}
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → v w p → v w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → botForces w → botForces w')
    {w w' : World} (hww' : w ≤ w') {φ : Proposition Atom}
    (hf : BForces F.r v botForces w φ) : BForces F.r v botForces w' φ := by
  induction φ generalizing w w' with
  | atom p    => exact v_uc p hww' hf
  | bot       => exact bf_uc hww' hf
  | imp φ ψ _ _  => intro u hu hfu; exact hf u (le_trans hww' hu) hfu
  | and _ _ ihφ ihψ => exact ⟨ihφ hww' hf.1, ihψ hww' hf.2⟩
  | or _ _ ihφ ihψ  => exact hf.elim (fun h => Or.inl (ihφ hww' h)) (fun h => Or.inr (ihψ hww' h))
  | box φ _   => intro u hu w'' hruw''; exact hf u (le_trans hww' hu) w'' hruw''
  | diamond φ ih =>
      obtain ⟨u, hru, hfu⟩ := hf
      obtain ⟨u', hru', huu'⟩ := F.f1 hww' hru   -- F1 supplies the ≥-successor
      exact ⟨u', hru', ih huu' hfu⟩
```
(Exact tactic text is indicative; verify goal shapes with `lean_goal`/`lean_multi_attempt` during
implementation. The `generalizing w w'` and per-constructor IH arity should be double-checked —
the PL file does not generalize because its IH is not needed under the modalities, but the modal
`diamond` case here needs the IH at a *different* world `u`, so `generalizing` is required.)

### Intuitionistic / minimal validity (mirror `IValid`/`MValid`)
```lean
/-- Intuitionistic modal validity: forced at every world of every birelational model with
`botForces = fun _ => False`. -/
def IValid (φ : Proposition Atom) : Prop := ...
/-- Minimal modal validity: forced at every world with arbitrary upward-closed `botForces`. -/
def MValid (φ : Proposition Atom) : Prop := ...
/-- `MValid φ → IValid φ` (transcribe `PL.mvalid_implies_ivalid`). -/
theorem mvalid_implies_ivalid ... := ...
```

## Tactic Survey Results (advisory)

- **Persistence induction**: plain term/`intro`/`obtain` as sketched; `grind`-annotated `@[simp]`
  reduction lemmas (as in `Modal/Basic.lean`'s `Satisfies.*_iff`) make downstream soundness go
  through with `simp`/`grind`. No heavy automation needed for the base file.
- **F1/F2 usage**: `obtain ⟨…⟩ := F.f1 …` / `F.f2 …` — these are existential eliminations, no
  search tactic required.
- The classical `Modal/Basic.lean` proves the K/T/B/4/5/D axioms semantically; the *intuitionistic*
  axiom validations (IK's `K□`, `K◇`, `◇⊥→⊥`, distribution) belong to the completeness/soundness
  tasks (492–495), not to this base semantics file. Keep task 490 scoped to frame + forcing +
  persistence + validity defs.

## Risks / Open Questions for the Planner

1. **Bundled vs unbundled forcing signature**: PL passes `v`/`bot_forces` as loose parameters to
   `IForces`; bundling them into `BModel` is cleaner for `IValid`/`MValid` but changes lemma
   signatures. Pick one and be consistent (recommend: `BForces` takes loose `r`/`v`/`botForces`
   like PL, and `BModel` is used only for the validity defs).
2. **F1 sufficiency vs F2 necessity for this file**: persistence needs only **F1**. **F2** is not
   used by any lemma *in task 490* — it is required by the completeness/soundness siblings. Decide
   whether to include F2 in `BFrame` now (recommended, so the frame class is the correct IK class
   from the start and 492–495 need not redefine it) or defer it. Recommendation: **include both
   F1 and F2 now**; the task brief explicitly requires them.
3. **Naming/lint**: use lowerCamelCase, no underscores in *declaration* names (`BForces`,
   `bforces_persistence` is acceptable Mathlib snake_case for theorems; check CSLib convention —
   `Modal/Basic.lean` uses `Satisfies` + `Satisfies.box_iff_forall`, PL uses `IForces` +
   `iforces_persistence`, so theorem-level snake_case is fine). Every new decl needs a docstring
   (docBlame). Prop-valued defs (`IValid`) are `def` in PL — keep consistent.
4. **`Preorder` vs `PartialOrder`**: follow PL — use `Preorder World` (antisymmetry never needed).
5. **Naming collision**: `Modal/Basic.lean` already defines `Modal.Satisfies`, `Modal.IValid`? No
   — `Modal` has `Proposition.valid`/`logic` but no `IValid`/`MValid`; PL owns those in `Cslib.
   Logic.PL`. Since the new file is also `Cslib.Logic.Modal`, its `IValid`/`MValid`/`Satisfies`
   would collide with nothing in `Modal` **except** the existing classical `Modal.Satisfies`.
   **Recommend naming the forcing relation `BForces` (not `Satisfies`)** to avoid shadowing the
   classical `Satisfies` in the same namespace, or place the birelational content in a nested
   namespace `Cslib.Logic.Modal.Birelational`.

## Key References

- **[Simpson1994]** Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*, PhD
  thesis, Edinburgh 1994 (LFCS ECS-LFCS-94-308). Ch. 3, clauses 3.1/3.2/3.5, conditions F1/F2.
  BibKey verified in `references.bib`. Corpus chunks 0193–0214.
- **[Wijesekera1990]** Wijesekera, *Constructive Modal Logics I*, APAL 50(3):271–301 (CK, non-
  distributive ◇). Global corpus `wijesekera_1990_constructivemodallogicsi`.
- **[BiermanDePaiva2000]** Bierman & de Paiva, *On an Intuitionistic Modal Logic*, Studia Logica
  65(3):383–416 (CK, both modalities primitive). Global corpus.
- **[ChagrovZakharyaschev1997]** cited by the PL Kripke file (persistence = Proposition 2.1).
- In-tree: `Cslib/Logics/Modal/Basic.lean` (task 487 base), `Cslib/Logics/Propositional/Semantics/
  Kripke.lean` (pattern to mirror), `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` (bundled
  two-relation frame precedent), `Cslib/Foundations/Logic/Connectives.lean` (HasBox/HasDia),
  `Cslib/Foundations/Relation/Defs.lean` (`Comp`, confluence notions).
```
