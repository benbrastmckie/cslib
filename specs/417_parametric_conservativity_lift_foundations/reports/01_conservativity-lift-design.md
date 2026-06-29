# Task 417 — Research: Parametric Conservativity Lift into Foundations

**Task type**: cslib (Foundations abstraction + proof refactor)
**Status**: research complete — no Lean source modified
**Date**: 2026-06-29
**Source**: specs/415_audit_propositional_lifting_structure_first/reports/01_lifting-audit.md §4, Rank 2
**Closes**: Finding 2 (Conservativity Asymmetry) of task 415

---

## 1. Summary / Verdict

**A single parametric interface unifies all three modal-family conservativity proofs.** The
three semantic-bridge lemmas (`modal_satisfies_toModal_iff_evaluate`,
`temporal_satisfies_toTemporal_iff_evaluate`, `bimodal_truthAt_toBimodal_iff_evaluate`) have
**byte-identical** `imp`/`and`/`or` proof bodies and differ only in (a) the satisfaction symbol
(`Modal.Satisfies` / `Temporal.Satisfies` / `Bimodal.truthAt`) and (b) the `atom`/`bot` base
cases. The `and`/`or` Łukasiewicz encodings are uniform across all three embeddings
(`toModal`/`toTemporal`/`toBimodal`). The whole copy-paste collapses behind **two** generic
declarations:

1. `evaluate_iff_of_classicalBridge` — the generic classical truth-functional bridge lemma
   (`sat (emb φ) ↔ PL.Evaluate v φ`), parameterized over an abstract satisfaction predicate
   `sat : Tgt → Prop` plus five per-connective compatibility `Iff`s.
2. `conservative_over_cpl` — the generic conservativity wrapper, a 3-line `prop_completeness`
   composition that takes the bridge and a per-logic satisfaction callback.

Each of the three logics then supplies one thin instance (5 small `Iff.rfl`-after-`simp` terms
for the bridge + its existing soundness/model construction for the satisfaction callback). This
is a **faithful transcription** of the existing proof bodies behind an interface, so it is
**zero new sorry / zero new axiom** by construction (the proof scripts already exist and are
copy-equal).

**One architectural caveat (must be confirmed, not blocking):** the requested placement
`Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean` requires a **Foundations → Logics**
import (the content is intrinsically about `PL.Proposition`, `PL.Evaluate`, and `prop_completeness`,
all in `Cslib/Logics/Propositional/`). This inverts CSLib's normal `Logics → Foundations`
layering. It is **mechanically safe** (verified: no import cycle), and there is **one existing
precedent** (`Cslib/Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean` imports
`Cslib.Logics.Propositional.Semantics.Algebra.*`). The task explicitly requests Foundations
placement and notes task 419 depends on it, so the recommendation is: **proceed with Foundations
placement, document the layering exception in the module docstring**, with `Logics/Propositional/
Metalogic/ConservativityLift.lean` as the fallback if a reviewer objects to the import direction.

---

## 2. Verified Semantics Shapes (the three relations to unify)

All line:col anchors verified by reading source.

| Logic | Satisfaction | atom arm | bot arm | imp arm |
|-------|--------------|----------|---------|---------|
| Modal | `Modal.Satisfies m w` (`Modal/Basic.lean:145-149`) | `m.v w p` | `False` | `Sat φ₁ → Sat φ₂` |
| Temporal | `Temporal.Satisfies M t` (`Temporal/Semantics/Satisfies.lean:57-60`) | `M.valuation t p` | `False` | `Sat φ → Sat ψ` |
| Bimodal | `Bimodal.truthAt M Ω τ t` (`Bimodal/Semantics/Truth.lean:54-60`) | **`∃ (ht : τ.domain t), M.valuation (τ.states t ht) p`** | `False` | `truthAt φ → truthAt ψ` |

**Target valuation type**: `PL.Evaluate (v : Atom → Prop)` (`Propositional/Semantics/Bool.lean:57-62`):
`atom x => v x`, `bot => False`, `imp a b => Ev a → Ev b`, `and a b => Ev a ∧ Ev b`, `or a b => Ev a ∨ Ev b`.

**Critical shape difference** (the only real obstacle to a naive unification): Modal/Temporal map
`atom p` *definitionally* to `v p` (so their atom bridge case is `rfl`), but **Bimodal wraps the
atom in an existential** `∃ (ht : τ.domain t), v p`. In the trivial model the domain proof is
inhabited (`WorldHistory.trivial`, domain = `univ`), so Bimodal's atom case is the explicit term
`⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩` (`PropositionalConservativity.lean:73`), **not**
`rfl`. **Design consequence**: the generic interface must take the atom-compatibility as an `Iff`
hypothesis (`sat (emb (.atom p)) ↔ v p`), never bake in `sat (emb (.atom p)) = v p`.

**Embedding uniformity** (the reason `and`/`or` need no per-logic content):
- `toModal` (`Modal/FromPropositional.lean`): `and ↦ (emb φ).and (emb ψ)` where
  `Modal.Proposition.and a b := .imp (.imp a (.imp b .bot)) .bot` (`Modal/Basic.lean:113-114`,
  verified Łukasiewicz). `or` analogous.
- `toTemporal` (`Temporal/FromPropositional.lean:57-62`): `and ↦ .imp (.imp φ (.imp ψ .bot)) .bot`,
  `or ↦ .imp (.imp φ .bot) ψ` (Łukasiewicz inlined).
- `toBimodal` (`Bimodal/Embedding/PropositionalEmbedding.lean:63-64`): identical inline.

All three therefore present the **same satisfaction shape** for `and`/`or` once the `imp`/`bot`
arms are unfolded:
- `sat (emb (.and a b)) ↔ ((sat (emb a) → sat (emb b) → False) → False)`
- `sat (emb (.or a b))  ↔ ((sat (emb a) → False) → sat (emb b))`

The `and`/`or` proof scripts in all three bridge lemmas are copy-equal (verified:
`Modal/FromPropositional.lean:118-142`, `Temporal/ConservativeExtension.lean:57-78`,
`Bimodal/.../PropositionalConservativity.lean:81-102`).

---

## 3. The unifying interface (answer to the core research question)

**Yes — one parametric interface unifies `Modal.Satisfies` / `Temporal.Satisfies` /
`Bimodal.truthAt`.** The unifying abstraction is **not** the satisfaction *relation* (whose arities
differ: Modal has `(m, w)`, Temporal has `(M, t)`, Bimodal has `(M, Ω, τ, t)`) but a **fully
applied satisfaction predicate** `sat : Tgt → Prop` obtained by fixing the model and point. Every
per-logic difference (world/point/history arguments, frame conditions, the existential atom wrap)
is discharged when the instance *constructs* its `sat` and proves the five compatibility `Iff`s.
This is the same move the Modal param lemma already makes (it fixes `⟨fun _ _ => True, fun _ => v⟩`
and world `()`), generalized one notch further.

No `Satisfies`-shaped typeclass over the three relations is needed (and would be awkward given the
arity mismatch). The `sat : Tgt → Prop` + five-`Iff` bundle is strictly simpler and admits all three.

---

## 4. Proposed signatures (exact)

### 4.1 Generic classical truth-functional bridge lemma

```lean
/-- **Generic classical truth-functional bridge.** A target satisfaction predicate `sat`
that is classically truth-functional on the image of a propositional embedding `emb`
agrees, formula-by-formula, with two-valued propositional evaluation under `v`.

The five hypotheses are the per-connective compatibility facts; `and`/`or` are stated in
their Łukasiewicz-unfolded form, which is exactly what `toModal`/`toTemporal`/`toBimodal`
produce after unfolding the target `imp`/`bot` arms. -/
theorem evaluate_iff_of_classicalBridge
    {Atom : Type*} {Tgt : Type*}
    (emb : PL.Proposition Atom → Tgt) (sat : Tgt → Prop) (v : Atom → Prop)
    (h_atom : ∀ p, sat (emb (.atom p)) ↔ v p)
    (h_bot  : ¬ sat (emb .bot))
    (h_imp  : ∀ a b, sat (emb (.imp a b)) ↔ (sat (emb a) → sat (emb b)))
    (h_and  : ∀ a b, sat (emb (.and a b)) ↔ ((sat (emb a) → sat (emb b) → False) → False))
    (h_or   : ∀ a b, sat (emb (.or a b))  ↔ ((sat (emb a) → False) → sat (emb b))) :
    ∀ ψ, sat (emb ψ) ↔ PL.Evaluate v ψ := by
  intro ψ
  induction ψ with
  | atom p => exact h_atom p
  | bot => simp only [PL.Evaluate]; exact iff_of_false h_bot (fun h => h)  -- sat(emb bot) ↔ False
  | imp a b ih1 ih2 =>
      rw [h_imp]; simp only [PL.Evaluate]
      exact ⟨fun h he => (ih2).mp (h ((ih1).mpr he)),
             fun h hm => (ih2).mpr (h ((ih1).mp hm))⟩
  | and a b ih1 ih2 =>
      rw [h_and]; simp only [PL.Evaluate]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · by_contra hna; exact h (fun ha _ => hna (ih1.mp ha))
        · by_contra hnb; exact h (fun _ hb => hnb (ih2.mp hb))
      · intro ⟨ha, hb⟩ h; exact h (ih1.mpr ha) (ih2.mpr hb)
  | or a b ih1 ih2 =>
      rw [h_or]; simp only [PL.Evaluate]
      constructor
      · intro h
        by_cases ha : PL.Evaluate v a
        · exact Or.inl ha
        · exact Or.inr (ih2.mp (h (fun hma => ha (ih1.mp hma))))
      · intro h hna
        cases h with
        | inl ha => exact absurd (ih1.mpr ha) hna
        | inr hb => exact ih2.mpr hb
```

Notes:
- The `imp`/`and`/`or` tactic bodies are **transcribed verbatim** from the three existing bridge
  lemmas (the only edit: `simp only [toX, SatX]` is replaced by `rw [h_imp/h_and/h_or]` + the
  `h_*` Iffs do the unfolding). This is the literal source of the zero-sorry guarantee.
- `bot` case: `iff_of_false` may need `PL.Evaluate v .bot` reducing to `False` (it does, by `rfl`);
  implementer should confirm the exact closing term during build — a `simp [h_bot]` likely suffices.

### 4.2 Generic conservativity wrapper

```lean
/-- **Generic conservativity over CPL.** If a target embedding's image is satisfied at a
per-valuation model (the `h_sat` callback) and a bridge identifies that satisfaction with
propositional evaluation, then the source formula is CPL-derivable. -/
theorem conservative_over_cpl
    {Atom : Type*} {Tgt : Type*} {φ : PL.Proposition Atom}
    {emb : PL.Proposition Atom → Tgt} {sat : (Atom → Prop) → Tgt → Prop}
    (bridge : ∀ v, sat v (emb φ) ↔ PL.Evaluate v φ)
    (h_sat  : ∀ v, sat v (emb φ)) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness
  intro v
  exact (bridge v).mp (h_sat v)
```

**Why a satisfaction callback, not a derivability hypothesis**: the three derivability predicates
have *different types* (`Derivable Axioms _`, `Temporal.ThDerivable _`, `Bimodal.ThDerivable _`),
so they cannot be unified. The existing Modal param lemma already encodes this insight: its
derivability argument is `_` (unused); the real content is the `h_sat` satisfaction callback,
produced per-instance via soundness. `conservative_over_cpl` keeps soundness at the instance site.
This is a faithful generalization of `modal_conservative_extension_param`
(`Modal/Metalogic/ConservativeExtension.lean:54-62`), which is already 90% of this abstraction.

**Relation to the §4 sketch in the 415 report**: the audit's sketch folded the bridge and
soundness into a single `bridge : TgtValid (emb φ) → PL.Evaluate v φ` callback. The two-callback
form above is preferred because it lets `evaluate_iff_of_classicalBridge` supply the `bridge`
*generically* (one proof for all three logics) while leaving only the genuinely per-logic soundness
step to the instance. Both are sorry-free; the two-callback form maximizes reuse.

---

## 5. The three thin instances (re-expression plan)

### 5.1 Temporal (`Temporal/ConservativeExtension.lean`)

- Replace the body of `temporal_satisfies_toTemporal_iff_evaluate` with a call to
  `evaluate_iff_of_classicalBridge` supplying:
  - `emb := PL.Proposition.toTemporal`, `sat := Temporal.Satisfies M t`, `v := M.valuation t`
  - `h_atom := fun _ => Iff.rfl`, `h_bot := id` (or `fun h => h`), `h_imp/h_and/h_or := fun _ _ => Iff.rfl`
    (each provable by `Iff.rfl` after `simp only [PL.Proposition.toTemporal, Satisfies]`, since the
    arms are definitional).
- `temporal_conservative_extension` becomes
  `conservative_over_cpl (bridge := fun v => temporal_..._iff_evaluate (TemporalModel.constant v) 0 φ)
   (h_sat := fun v => soundness_thderivable h (TemporalModel.constant v) 0)`.
  (Keep `TemporalModel.constant`, `soundness_thderivable` — they are the per-logic content.)

### 5.2 Bimodal (`Bimodal/.../PropositionalConservativity.lean`)

- Replace `bimodal_truthAt_toBimodal_iff_evaluate` body with `evaluate_iff_of_classicalBridge`,
  `sat := fun t' => truthAt M Omega τ t'`-style fixed predicate (model/Ω/τ fixed to the trivial
  frame). **The one non-`rfl` term is `h_atom`**: supply the existing
  `⟨fun ⟨_, h⟩ => h, fun h => ⟨True.intro, h⟩⟩` (collapses the `∃ (ht : τ.domain t)` wrap).
  `h_bot/h_imp/h_and/h_or := Iff.rfl`-after-`simp only [toBimodal, truthAt]`.
- `bimodal_conservative_extension` becomes `conservative_over_cpl` with `h_sat` built from the
  existing `soundness [] φ.toBimodal d ℤ ℱ M Omega h_sc τ h_mem 0 (by simp)` per valuation.

### 5.3 Modal (optional re-home, `Modal/Metalogic/ConservativeExtension.lean`)

- `modal_satisfies_toModal_iff_evaluate` (`Modal/FromPropositional.lean:106`) becomes a thin
  instance with all five `h_*` as `Iff.rfl`-after-`simp` (`h_atom := fun _ => Iff.rfl`).
- `modal_conservative_extension_param` re-expressed as `conservative_over_cpl` with
  `sat v := Modal.Satisfies ⟨fun _ _ => True, fun _ => v⟩ ()`. **Recommendation: re-home but keep
  the 15 per-system instantiations untouched** — they call `modal_conservative_extension_param` by
  name, so preserve that name (or provide a one-line `abbrev`/wrapper delegating to
  `conservative_over_cpl`) to avoid editing 15 system files. Mark Modal re-home **optional/low
  priority**; the Temporal + Bimodal instances are the load-bearing wins.

---

## 6. Placement & layering analysis (Foundations decision)

- **Requested**: `Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean`.
- **Required imports**: `Cslib.Logics.Propositional.Semantics.Bool` (`PL.Evaluate`),
  `Cslib.Logics.Propositional.Metalogic.StrongCompleteness` (`prop_completeness`,
  `PropositionalAxiom`, `PL.Derivable`), `Cslib.Init`.
- **Layering**: this is a **Foundations → Logics.Propositional** dependency. CSLib's dominant
  direction is the reverse (`Logics → Foundations`; verified: dozens of `Logics/*` files import
  `Cslib.Foundations.Logic.*`). **Precedent exists**: `Foundations/Order/HilbertAlgebra/
  DiegoEmbedding.lean:15-16` imports `Cslib.Logics.Propositional.Semantics.Algebra.*`. So the
  exception is established, though it lives under `Foundations/Order`, not `Foundations/Logic`.
- **Cycle check**: **no import cycle** — `ConservativityLift.lean` is a *new* file imported only by
  the three downstream conservativity files; nothing in `Logics/Propositional` that it imports will
  import it back. Verified `StrongCompleteness.lean` imports (`Bool`, `SemanticConsequence`, `MCS`,
  `Soundness`) — none reference Foundations Metalogic conservativity.
- **Module conventions** (from `Foundations/Logic/Metalogic/GenericMCS.lean`): start with `module`,
  then `public import …`, wrap in `@[expose] public section … end`. Namespace: the generic lemmas
  are logic-agnostic; recommend a neutral namespace such as `Cslib.Logic` (matches the three
  instance files, which all `namespace Cslib.Logic`) or a dedicated `Cslib.Logic.Conservativity`.
  **Avoid** `defsWithUnderscore`-tripping names — `evaluate_iff_of_classicalBridge` and
  `conservative_over_cpl` use underscores; CSLib convention is lowerCamelCase **for `def`s**, but
  these are **`theorem`s**, where snake_case is the Mathlib/CSLib norm (cf.
  `modal_conservative_extension_param`, `prop_completeness`). So snake_case names are correct here.
- **Recommendation**: **proceed with the requested Foundations placement** (task 419 depends on it),
  and add a one-paragraph docstring note acknowledging the Foundations→Logics import as a deliberate
  shared-substrate exception, citing the DiegoEmbedding precedent. If a CSLib reviewer objects on
  layering grounds, the drop-in fallback is `Cslib/Logics/Propositional/Metalogic/
  ConservativityLift.lean` (no signature change; only the three instance imports differ). Flag this
  as a **confirm-with-user / confirm-in-PR** decision, not a blocker.

---

## 7. Tactic Survey Results

- The proof is a **transcription**, not a search — no tactic discovery needed. The existing
  `by_contra`/`by_cases`/`cases`/explicit-term scripts in the three bridge lemmas are reused
  verbatim inside `evaluate_iff_of_classicalBridge`. Do **not** attempt to replace them with
  `simp`/`aesop`/`tauto`: literature/source-fidelity (the existing proofs) is the safer path and the
  `and`/`or` arms rely on classical `by_contra`/`by_cases` that a blind `tauto` may or may not match.
- `conservative_over_cpl` is a 3-line `apply prop_completeness; intro v; exact (bridge v).mp (h_sat v)`
  — identical skeleton to the verified `modal_conservative_extension_param`.
- One small open point for the implementer: the `bot` case closing term in
  `evaluate_iff_of_classicalBridge` (`iff_of_false h_bot _` vs `simp [h_bot]`) — resolve at build
  time with `lean_goal`; both are sorry-free.

---

## 8. Reuse Check (CSLib reuse-first protocol)

- **Does CSLib already have this?** Partially — `modal_conservative_extension_param`
  (`Modal/Metalogic/ConservativeExtension.lean:54`) is the Modal-only version; this task hoists it.
  No existing Foundations-level generic conservativity lemma (searched `Foundations/Logic/Metalogic/`:
  `GenericMCS`, `SetDeduction`, `Consistency`, `DeductionHelpers`, `MCSProperties`, `ListDeduction`,
  `PrimeExclusion`, `ListImplication`, `DeductionCharacterization` — none cover embedding-conservativity).
- **Mathlib instantiable version?** No — this is CSLib-specific (`PL.Proposition`, `PL.Evaluate`,
  `prop_completeness` are CSLib declarations).
- **Existing typeclass to reuse?** No `Satisfies`-shaped typeclass spans the three relations; the
  `sat : Tgt → Prop` + 5-`Iff` bundle is the right (minimal) interface and needs no new typeclass.
- **Conclusion**: net-new generic lemmas justified; they consolidate, not duplicate.

---

## 9. Risks & open questions

1. **Foundations→Logics layering** (Section 6) — confirm placement in PR/with user. Non-blocking;
   fallback placement available with no signature change.
2. **Bimodal `sat` fixing** — Bimodal's `truthAt` takes `(M, Ω, τ, t)`; the instance must fix all
   four to form `sat : Tgt → Prop`. The trivial-frame choices already in
   `PropositionalConservativity.lean:126-129` provide them; transcription is mechanical.
3. **Modal 15-system fan-out** — re-homing `modal_conservative_extension_param` must preserve the
   name (or provide a delegating wrapper) to avoid touching 15 `Systems/*/ConservativeExtension.lean`
   files. Recommend keeping the Modal param lemma as a thin wrapper over `conservative_over_cpl`.
4. **`bot`-case closing term** — minor; resolve at build (Section 7).

**No blockers.** Zero new sorry / zero new axioms is achievable by construction (the proof bodies
already exist and are copy-equal across the three logics).

---

## Appendix — Verification method

All file:line citations obtained by direct `Read` and `grep`/`sed`. Semantics arms
(`Modal.Satisfies:145`, `Temporal.Satisfies:57`, `Bimodal.truthAt:54`, `PL.Evaluate:57`),
embeddings (`toModal`, `toTemporal:57`, `toBimodal:63`), `Modal.Proposition.and:113`,
`prop_completeness:548`, and the import graph (Foundations↔Logics direction, single DiegoEmbedding
precedent, no cycle) were all confirmed against source. No Lean source was modified; no build was
run (no code change). No `lean_diagnostic_messages` / `lean_file_outline` calls (blocked tools).
