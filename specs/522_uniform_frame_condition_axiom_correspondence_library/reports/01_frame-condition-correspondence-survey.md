# Research Report: Uniform Frame-Condition-to-Axiom Correspondence Library

**Task type:** cslib (Lean 4, research-first / design-only)
**Scope:** `Cslib/Logics/Modal/` — Hilbert `Systems/*/Soundness.lean`, birelational
(`Minimal/`, `Intuitionistic/`), constructive (`Constructive/`), and the existing
Tableau `FrameCondition` abstraction.
**Verdict:** A shared *classical* correspondence library is highly feasible, low-risk, and
already half-built elsewhere in the tree. A single typeclass layer unifying classical +
birelational + constructive conditions is **not** recommended — the three semantics are
genuinely different and only the *predicate shapes* (not the soundness proofs) overlap.

---

## 1. Inventory (file:line locations)

### 1.1 Classical Hilbert soundness — inline raw frame hypotheses

Every `Systems/<Sys>/Soundness.lean` proves `<sys>_axiom_sound` by `cases h_ax` and threads
raw `∀`-quantified frame hypotheses through as ordinary arguments (NOT a named predicate).
The shared propositional / K / and-or-diaduality cases are already factored into
`Metalogic/Soundness.lean` as `Satisfies.*_axiom` lemmas (lines 48–145); only the five
**modal** frame-axiom cases remain inlined and duplicated per system.

Frame-property hypothesis forms as currently written:

| Property | Inline form used in `Systems/*/Soundness.lean` | Uses a library class? |
|---|---|---|
| Reflexivity | `(h_refl : ∀ w, m.r w w)` | No (raw ∀) |
| Transitivity | `(h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)` | No (raw ∀) |
| Symmetry | `(h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)` | No (raw ∀) |
| Seriality | `(h_serial : Relation.Serial m.r)` | **Yes** — Mathlib `Relation.Serial` |
| Euclidean | `(h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)` | No (raw ∀; = `RightEuclidean` unfolded) |

Per-system files (15 classical systems), each with `<sys>_axiom_sound` + `<sys>_soundness`:

- `Systems/K/Soundness.lean` — no frame axiom (all-frames)
- `Systems/T/Soundness.lean:39` `t_axiom_sound` — `h_refl`
- `Systems/S4/Soundness.lean:48` `s4_axiom_sound` — `h_refl`, `h_trans`
- `Systems/S5/Soundness.lean:38` `s5_axiom_sound` — `h_refl`, `h_trans`, `h_eucl` (derives symmetry inline at line 58)
- `Systems/B/Soundness.lean:38` `b_axiom_sound` — `h_symm`
- `Systems/D/Soundness.lean:38` `d_axiom_sound` — `h_serial`
- `Systems/K4/Soundness.lean:46` `k4_axiom_sound` — `h_trans`
- `Systems/K5/Soundness.lean:39` `k5_axiom_sound` — `h_eucl`
- `Systems/K45/Soundness.lean:49` `k45_axiom_sound` — `h_trans`, `h_eucl`
- `Systems/KB5/Soundness.lean:49` `kb5_axiom_sound` — `h_symm`, `h_eucl`
- `Systems/D4/Soundness.lean:43` `d4_axiom_sound` — `h_serial`, `h_trans`
- `Systems/D5/Soundness.lean:43` `d5_axiom_sound` — `h_serial`, `h_eucl`
- `Systems/D45/Soundness.lean:45` `d45_axiom_sound` — `h_serial`, `h_trans`, `h_eucl`
- `Systems/DB/Soundness.lean:43` `db_axiom_sound` — `h_serial`, `h_symm`
- `Systems/TB/Soundness.lean:49` `tb_axiom_sound` — `h_refl`, `h_symm`

**Duplication:** each modal-axiom case body is byte-for-byte identical across every system
that includes it. Approximate multiplicity of the five inlined proof bodies:
`modalT` ×4 (T, S4, S5, TB), `modalFour` ×5 (S4, K4, D4, D45, K45), `modalB` ×4
(B, TB, KB5, DB), `modalD` ×5 (D, D4, D5, D45, DB), `modalFive` ×5 (K5, D5, K45, KB5, D45)
≈ **23 duplicated modal case bodies** across the 15 files.

### 1.2 Classical completeness — named `Model → Prop` FC predicates

A *second, incompatible* family of FC predicates exists, one per system, shaped
`∀ {World}, Model World Atom → Prop` and consumed by the parametric
`strong_soundness`/`strong_completeness`/`compactness` infrastructure in
`Metalogic/Completeness.lean:659,685,724`:

- `Systems/T/Completeness.lean:52` `tFC`, `S4/Completeness.lean:48` `s4FC`,
  `S5/Completeness.lean:47` `s5FC`, `B/Completeness.lean:48` `bFC`,
  `D/Completeness.lean:417` `dFC`, `K4/Completeness.lean:45` `k4FC`,
  `K5/Completeness.lean:44` `k5FC`, `K45/Completeness.lean:46` `k45FC`,
  `KB5/Completeness.lean:48` `kb5FC`, `D4/Completeness.lean:50` `d4FC`,
  `D5/Completeness.lean:50` `d5FC`, `D45/Completeness.lean:50` `d45FC`,
  `DB/Completeness.lean:50` `dbFC`, `TB/Completeness.lean:58` `tbFC`.

Each unfolds to the same raw-∀ conjunction as §1.1 (e.g. `s4FC m = (∀ w, m.r w w) ∧ (∀ w₁ w₂ w₃, …)`),
and each has a `<sys>_sound_cb` adapter (e.g. `S4/Completeness.lean:87`) that destructures the
conjunction and forwards to `<sys>_soundness`.

### 1.3 Birelational FC predicates (raw relation `r`, named per file)

- `Minimal/MT.lean:119` `mtFC := ∀ w, r w w`
- `Minimal/MS4.lean:122` `ms4FC := (∀ w, r w w) ∧ (∀ {w x y}, r w x → r x y → r w y)`
- `Minimal/MS5.lean:139` `ms5FC := refl ∧ trans ∧ (∀ {w x}, r w x → r x w)`
- `Intuitionistic/IT.lean:128` `itFC := ∀ w, r w w`
- `Intuitionistic/IS4.lean:136` `is4FC := refl ∧ trans` (identical shape to `ms4FC`)
- `Intuitionistic/IS5.lean:155` `is5FC := refl ∧ trans ∧ symm` (identical shape to `ms5FC`)

These use **implicit** binders `{w x y}` (vs classical explicit `w₁ w₂ w₃`) and raw
`r : World → World → Prop` (vs `Model.r`). Consumed by `IValidFC`
(`Intuitionistic/Extension.lean:74`) and `MValidFC` (`Minimal/MinExtension.lean:87`).
The soundness proofs (`ms4_axiom_sound`, `is5_axiom_sound`, …) are birelational forcing
arguments with persistence — **structurally unrelated** to the classical `Satisfies` proofs.

### 1.4 Constructive FC predicates (≤-composed / order-saturated)

`Constructive/CKExtension.lean`: `ctFC:116`, `cs4FC:124`, `cs4FC':137`, `cs5FC:159`,
`cs5FC'':184`; `Constructive/CS5Canonical.lean:255` `cs5FCIncest`. These are **not** plain
frame properties: they interleave the modal relation `r` with the preorder `≤`
(e.g. `cs4FC := (∀ w, r w w) ∧ (∀ {w u u' t}, r w u → u ≤ u' → r u' t → r w t)`), plus
weakened existential-rebasing variants. Consumed by `CKValidFC` (`CKExtension.lean:86`,
whose FC shape carries an extra `[Preorder World]`). These **cannot** be unified with the
classical/birelational conditions and are out of scope for a plain correspondence library.

### 1.5 Existing shared abstraction (the reuse target — Tableau side)

**The correspondence abstraction already exists on the Tableau side and uses library
classes**, which is the single most important finding for design:

- `Tableau/FrameSoundness.lean:73` `abbrev FrameCondition := ∀ {World : Type}, (World → World → Prop) → Prop`
- Named instances built from **Std / Mathlib / Foundations** classes:
  `trivialFC:77`, `reflFC:956 (Std.Refl r)`, `s4FC:1047 (Std.Refl r ∧ IsTrans World r)`,
  `symmFC:1169 (Std.Symm r)`, `s5FC:1275 (Std.Refl r ∧ Relation.RightEuclidean r)`,
  `fiveFC:1284 (Relation.RightEuclidean r)`, `kb5FC:1293 (Std.Symm r ∧ Relation.RightEuclidean r)`
- Consumed by `frameValid` (`FrameSoundness.lean:83`).

- `Foundations/Relation/Euclidean.lean` provides `Relation.RightEuclidean` /
  `LeftEuclidean` classes **with the correspondence theorems already proved**:
  `symm_rightEuclidean_iff_trans:273`, `RightEuclidean` + `Std.Refl` ⇒ `Std.Symm`
  instance (line 53), `refl_serial:35` / `Serial` instance (line 38),
  `rooted_cluster_universal`, S5/KB5 cluster analysis.
- Mathlib/Std supply `Std.Refl` (`.refl`), `Std.Symm` (`.symm`), `IsTrans` (`.trans`),
  `Relation.Serial` (`.serial`) — the last **already used** at `Systems/D/Soundness.lean:40,50`.

**Conclusion for §1:** the library already speaks two dialects — Tableau uses
`Std.Refl/IsTrans/Std.Symm/RightEuclidean`; Hilbert `Systems/*/Soundness.lean` uses raw ∀
forms. The correspondence library should adopt the Tableau/Foundations dialect and retire the
raw forms in the Hilbert soundness path.

---

## 2. Common structure — axiom ⇔ frame-property map

| Axiom (constructor) | Schema | Frame property | Canonical library predicate |
|---|---|---|---|
| `modalT` | `□φ → φ` | reflexivity | `Std.Refl m.r` (`.refl : ∀ a, r a a`) |
| `modalFour` | `□φ → □□φ` | transitivity | `IsTrans _ m.r` (`.trans : r a b → r b c → r a c`) |
| `modalB` | `φ → □◇φ` (`Axioms.AxiomB`) | symmetry | `Std.Symm m.r` (`.symm : r a b → r b a`) |
| `modalD` | `□φ → ◇φ` | seriality | `Relation.Serial m.r` (`.serial : ∀ a, ∃ b, r a b`) |
| `modalFive` | `◇φ → □◇φ` | right-euclidean | `Relation.RightEuclidean m.r` (`.rightEuclidean : r a b → r a c → r b c`) |

Semantics grounding (`Basic.lean:247-248`): `Satisfies m w (□φ) = ∀ w', m.r w w' → Satisfies m w' φ`;
`Satisfies m w (◇φ) = ∃ w', m.r w w' ∧ Satisfies m w' φ`. The current inline case bodies
(e.g. `S4/Soundness.lean:59-64`, `K5/Soundness.lean:47-52`, `B/Soundness.lean:48-50`,
`D/Soundness.lean:49-51`) are exactly the five one-liner proofs that map each schema to its
property; they are what the library will name once and reuse.

`modalFive`'s inline hypothesis `∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃` is
**definitionally `Relation.RightEuclidean.rightEuclidean` re-argumented** (a=w₁,b=w₂,c=w₃), so
the migration is a mechanical rewrite, not a re-proof.

---

## 3. Feasibility and blast radius

### 3.1 Shared classical correspondence library — FEASIBLE (recommended)

- **Pattern already sanctioned:** `Metalogic/Soundness.lean:48-145` already factors 13
  axiom-soundness lemmas as `Satisfies.*_axiom`. Adding five more (`modalT_axiom`,
  `modalFour_axiom`, `modalB_axiom`, `modalD_axiom`, `modalFive_axiom`) is the identical move.
- **Zero new proof obligations:** each body is a copy of an existing inline case; no `sorry`
  risk (satisfies the zero-debt gate).
- **Reuse-first satisfied:** consume `Std.Refl / IsTrans / Std.Symm / Relation.Serial /
  Relation.RightEuclidean` (already in the dependency graph via `Foundations/Relation/Euclidean.lean`
  and Mathlib), matching the Tableau `FrameCondition` dialect. No new frame-property definitions.
- **Blast radius:**
  - *Additive core:* 1 file — append 5 lemmas to `Metalogic/Soundness.lean` (or a new
    sibling `Metalogic/FrameCorrespondence.lean`). Touches no existing proof.
  - *Optional consumer refactor:* 15 `Systems/*/Soundness.lean` files rewrite their
    `<sys>_axiom_sound` cases to `exact Satisfies.modalX_axiom …`. Each change is ~2–4 lines.
    Signatures of `<sys>_axiom_sound` / `<sys>_soundness` can be **kept stable** (still accept
    raw `h_refl`/`h_trans`/… and internally build the `Std.Refl`/`IsTrans` witnesses), so
    downstream `Completeness.lean` adapters (`<sys>_sound_cb`) need **no** change. This bounds
    the blast radius to the 15 soundness files even in the full-refactor case.

### 3.2 Single typeclass layer unifying classical + birelational + constructive — NOT recommended

- The three `…ValidFC` wrappers have **three different FC shapes**: classical soundness takes
  raw hypotheses (no FC type at all); `IValidFC`/`MValidFC` take `{World} → (World→World→Prop) → Prop`;
  `CKValidFC` takes `{World} → [Preorder World] → (World→World→Prop) → Prop`. No single
  typeclass subsumes all three without introducing the `[Preorder]` everywhere it is unwanted.
- The **soundness proofs differ fundamentally**: `Satisfies` (single relation, classical) vs
  birelational forcing with persistence (`bforces_persistence`, `f1`/`f2` confluence) vs
  ≤-composed constructive forcing. A shared `modalFour_axiom` lemma cannot serve both the
  classical `Satisfies` goal and the birelational forcing goal — only the *predicate name*
  would be shared, not the theorem.
- The birelational predicate *shapes* (`ms4FC` ≡ `is4FC`, `ms5FC` ≡ `is5FC`) **could** be
  de-duplicated into one shared `plainReflTransFC`/`plainEquivFC` definition, but that is a
  small, separable cleanup (2–3 files) distinct from the axiom-correspondence goal and should
  be tracked separately to keep this task's blast radius contained.

### 3.3 Optional deeper unification (classical completeness FC family)

The 14 `Model → Prop` predicates in §1.2 could each be re-expressed as
`fun m => <StdClasses on m.r>` and their `<sys>_sound_cb` adapters could forward to the new
`Satisfies.*_axiom` lemmas. This is a natural follow-on but multiplies the touch count
(14 more files) — recommend deferring to a second phase.

---

## 4. Recommended design (design-only; signatures)

Place in `Metalogic/Soundness.lean` (imports already present; keeps all `Satisfies.*_axiom`
lemmas colocated) or a new `Metalogic/FrameCorrespondence.lean` imported by it. Use the
**library classes** as the frame-property interface, matching Tableau/Foundations.

```lean
namespace Cslib.Logic.Modal
variable {Atom : Type*}

/-- T corresponds to reflexivity: `□φ → φ` is valid at every world of a reflexive frame. -/
lemma Satisfies.modalT_axiom {World : Type*} (m : Model World Atom) [Std.Refl m.r]
    (w : World) (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ) φ) := by
  intro h_box; exact h_box w (Std.Refl.refl w)

/-- 4 corresponds to transitivity: `□φ → □□φ`. -/
lemma Satisfies.modalFour_axiom {World : Type*} (m : Model World Atom) [IsTrans World m.r]
    (w : World) (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ) (Proposition.box (Proposition.box φ))) := by
  intro h_box w₁ hr₁ w₂ hr₂; exact h_box w₂ (trans_of _ hr₁ hr₂)

/-- B corresponds to symmetry: `φ → □◇φ` (`Axioms.AxiomB φ`). -/
lemma Satisfies.modalB_axiom {World : Type*} (m : Model World Atom) [Std.Symm m.r]
    (w : World) (φ : Proposition Atom) :
    Satisfies m w (Axioms.AxiomB φ) := by
  intro hφ w' hr h_box_neg; exact h_box_neg w (Std.Symm.symm _ _ hr) hφ

/-- D corresponds to seriality: `□φ → ◇φ` (box-neg-bot encoding). -/
lemma Satisfies.modalD_axiom {World : Type*} (m : Model World Atom) [Relation.Serial m.r]
    (w : World) (φ : Proposition Atom) :
    Satisfies m w (Proposition.imp (Proposition.box φ)
      (Proposition.imp (Proposition.box (Proposition.imp φ Proposition.bot))
        Proposition.bot)) := by
  intro h_box h_box_neg
  obtain ⟨w', hr⟩ := Relation.Serial.serial w
  exact h_box_neg w' hr (h_box w' hr)

/-- 5 corresponds to right-euclideanness: `◇φ → □◇φ` (box-neg-bot encoding). -/
lemma Satisfies.modalFive_axiom {World : Type*} (m : Model World Atom)
    [Relation.RightEuclidean m.r] (w : World) (φ : Proposition Atom) :
    Satisfies m w (((Proposition.box (φ.imp .bot)).imp .bot).imp
      (Proposition.box ((Proposition.box (φ.imp .bot)).imp .bot))) := by
  intro h_diam w' hr h_box_neg_w'
  exact h_diam (fun w'' hr' h_phi =>
    h_box_neg_w' w'' (Relation.RightEuclidean.rightEuclidean hr hr') h_phi)
```

**Interface choice — instance-arg `[Std.Refl m.r]` vs explicit `(h_refl : ∀ w, m.r w w)`:**
either works. Recommendation: expose the **explicit-hypothesis** variant as the primary public
signature (so `<sys>_axiom_sound` callers pass their existing `h_refl`/`h_trans`/… unchanged and
downstream files need zero edits), and additionally provide the instance-backed forms above for
new systems that prefer to `haveI : Std.Refl m.r := ⟨h_refl⟩`. Concretely the explicit form is:

```lean
lemma Satisfies.modalT_axiom' {World} (m : Model World Atom) (h_refl : ∀ w, m.r w w)
    (w : World) (φ) : Satisfies m w ((Proposition.box φ).imp φ) :=
  fun h_box => h_box w (h_refl w)
```

Each `<sys>_axiom_sound` then reduces its modal case to
`| modalT φ => exact Satisfies.modalT_axiom' m h_refl w φ` etc. — turning ~23 duplicated proof
bodies into single-line `exact`s and giving "assemble a system by choosing frame properties"
for free: a new system's `axiom_sound` is just a `cases` dispatching each schema to its
correspondence lemma.

**Naming/lint notes (must-pass for PR):** `Satisfies.modalT_axiom` etc. are `Prop`-valued ⇒
`lemma`/`theorem` (defLemma); lowerCamelCase, no underscores in the *identifier* segment
(existing `Satisfies.implyK_axiom` uses a trailing `_axiom` suffix — follow that established
sibling convention exactly, it already passes lint); every new lemma needs a docstring
(docBlame); wrap in `namespace Cslib.Logic.Modal` (topNamespace). Do **not** add `@[simp]`.

---

## 5. Zulip coordination assessment

`CONTRIBUTING.md:149`: *"for any major development, it is strongly recommended to discuss first
on Zulip … so that scope, dependencies, and placement in the library are aligned."*
`CONTRIBUTING.md:169-175` describes working-group coordination for sustained modal-logic work.

- **Additive core only (§3.1 additive):** 1 file, no behavior change → a straightforward PR;
  Zulip courtesy note optional.
- **Full consumer refactor (15 `Systems/*/Soundness.lean`):** touches many files in a shared,
  actively-developed subtree (the modal metalogic has heavy in-flight work — see the
  Constructive/Tableau task history). **Zulip coordination is warranted**: post the axiom⇔property
  map (§2), the placement decision (extend `Soundness.lean` vs new `FrameCorrespondence.lean`),
  and whether to also migrate the §1.2 completeness FC family and §3.2 birelational predicate
  de-duplication, so the working group aligns before a 15–29-file PR lands.

**Recommendation:** split into (a) additive correspondence lemmas + wiring the 15 soundness
files (single coherent PR, Zulip heads-up), and defer (b) completeness-FC re-expression and
(c) birelational predicate de-duplication to separate, individually-scoped follow-ups.

---

## 6. Reuse-first checklist (outcome)

| Check | Result |
|---|---|
| Existing Foundations abstraction for the properties? | **Yes** — `Foundations/Relation/Euclidean.lean` (`RightEuclidean`, correspondence theorems); Mathlib `Std.Refl/Std.Symm/IsTrans/Relation.Serial`. Do not define new property predicates. |
| Existing `FrameCondition` layer? | **Yes** — `Tableau/FrameSoundness.lean:73` `FrameCondition` + named instances using the Std classes. New library should match this dialect. |
| Existing shared axiom-soundness pattern? | **Yes** — `Metalogic/Soundness.lean` `Satisfies.*_axiom` (13 lemmas). Extend it with 5 modal lemmas. |
| New notation/typeclass needed? | **No.** No new typeclass; reuse Std/Foundations classes. |
| Unify classical + birelational + constructive? | **No** — different semantics; only predicate shapes overlap. Keep classical library separate. |

---

## 7. Downstream handoff (for the planner)

1. Decide placement: append to `Metalogic/Soundness.lean` vs new
   `Metalogic/FrameCorrespondence.lean` (recommend the latter for discoverability, imported by
   `Soundness.lean`).
2. Add 5 correspondence lemmas (§4), explicit-hypothesis primary form + optional instance form.
3. Rewire 15 `Systems/*/Soundness.lean` `<sys>_axiom_sound` modal cases to `exact` the new
   lemmas; keep `<sys>_axiom_sound`/`<sys>_soundness` public signatures stable (no completeness
   or downstream edits).
4. Verify with scoped `lake build Cslib.Logics.Modal.Metalogic.Systems.<Sys>.Soundness` per file,
   then full `lake build`; `lake lint` for the new lemmas.
5. Post Zulip scope note before the multi-file PR (§5).
6. Track as separate follow-ups: §1.2 completeness-FC re-expression; §3.2 birelational
   `ms*FC`/`is*FC` predicate de-duplication.
