# Research Report: Parametric Modal Conservative Extension (Task 337)

## Objective

Extract a single parametric conservative-extension theorem (taking frame-condition
hypotheses and a universal model constructor implicitly) to replace 15 near-identical
`Systems/*/ConservativeExtension.lean` files (896 lines total), so each system instantiates
in ~5 lines. Target: ~400 lines reduced.

## Summary of Findings

- All 15 `ConservativeExtension.lean` files are structurally identical except for: (a) the
  axiom predicate, (b) the named `*_soundness` wrapper, and (c) the list of frame-condition
  discharge terms passed to that wrapper.
- A single parametric theorem `modal_conservative_extension_param` was drafted and
  **verified to compile** (`lake build`), and **verified to be instantiable** by S5 (3 frame
  conditions), D (Serial instance argument), and K (no frame conditions) — each in ~5 lines.
- **No new abstractions or Mathlib lemmas are needed.** The existing bridge lemma
  `modal_satisfies_toModal_iff_evaluate` and `prop_completeness` already do all the work.
- This is a pure refactor with zero new proof obligations and zero risk of `sorry`. It is
  the direct analogue of the landed task 335 Soundness refactor.

## Reuse Check (CSLib reuse-first)

| Candidate | Result |
|-----------|--------|
| Existing parametric conservative-extension helper in `Metalogic/` | None. `lean_local_search "conservative_extension"` returned no declarations; the 15 theorems are named `<sys>_conservative_extension` and live only in `Systems/*/`. |
| `InterSystem/Conservativity.lean` | Unrelated — it proves modal-cube *derivability monotonicity* (`Derivable_mono` edges), not CPL conservative extension. Do **not** reuse or place the new theorem there. |
| Bridge lemma | `modal_satisfies_toModal_iff_evaluate` (in `Cslib/Logics/Modal/FromPropositional.lean:106`) already converts `Satisfies m w φ.toModal ↔ Evaluate (m.v w) φ`. Reused directly. |
| `toModal_valid_implies_tautology` | `FromPropositional.lean:152`. Used by the *current K file* but **not needed** by the parametric version, which uses the Unit-model path uniformly. |
| CPL completeness | `prop_completeness` (`Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean:548`): `Tautology φ → Derivable PropositionalAxiom φ`. Reused directly. |

## Shared Composition Structure

Every file (except K, see below) is exactly:

```lean
theorem <sys>_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@<Sys>Axiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v
  let m : Modal.Model Unit Atom := ⟨fun _ _ => True, fun _ => v⟩
  obtain ⟨d⟩ := h
  exact (modal_satisfies_toModal_iff_evaluate m () φ).mp
    (<sys>_soundness d m <FRAME-CONDITIONS> () (fun _ h => nomatch h))
```

The universal model is **identical in all 14 files**: `⟨fun _ _ => True, fun _ => v⟩ :
Modal.Model Unit Atom` (relation always-true on `Unit`, valuation the CPL valuation `v`).

**K is the exception** (`Systems/K/ConservativeExtension.lean`): it uses the older
`toModal_valid_implies_tautology` + `k_soundness_derivable` composition rather than building
the Unit model. It still fits the parametric theorem — verified by the `k_test` instantiation
using `k_soundness d _ () (...)`.

## Frame-Condition Discharge Table (the only variation)

Each system's `*_soundness` wrapper takes a heterogeneous list of frame-condition arguments.
This table is the complete specification for the 15 instantiations:

| System | Axiom | `*_soundness` frame-condition args (in order) |
|--------|-------|------------------------------------------------|
| K | `KAxiom` | *(none)* — `k_soundness d m () h_ctx` |
| T | `TAxiom` | refl: `fun _ => trivial` |
| D | `DAxiom` | serial (instance): `⟨fun w => ⟨w, trivial⟩⟩` |
| B | `BAxiom` | symm: `fun _ _ _ => trivial` |
| D4 | `D4Axiom` | serial `⟨fun w => ⟨w, trivial⟩⟩`, trans `fun _ _ _ _ _ => trivial` |
| D5 | `D5Axiom` | serial `⟨fun w => ⟨w, trivial⟩⟩`, eucl `fun _ _ _ _ _ => trivial` |
| K4 | `K4Axiom` | trans: `fun _ _ _ _ _ => trivial` |
| K5 | `K5Axiom` | eucl: `fun _ _ _ _ _ => trivial` |
| K45 | `K45Axiom` | trans `fun _ _ _ _ _ => trivial`, eucl `fun _ _ _ _ _ => trivial` |
| D45 | `D45Axiom` | serial `⟨fun w => ⟨w, trivial⟩⟩`, trans `…`, eucl `…` |
| DB | `DBAxiom` | serial `⟨fun w => ⟨w, trivial⟩⟩`, symm `fun _ _ _ => trivial` |
| TB | `TBAxiom` | refl `fun _ => trivial`, symm `fun _ _ _ => trivial` |
| S4 | `S4Axiom` | refl `fun _ => trivial`, trans `fun _ _ _ _ _ => trivial` |
| S5 | `ModalAxiom` | refl `fun _ => trivial`, trans `…`, eucl `…` |
| KB5 | `KB5Axiom` | symm `fun _ _ _ => trivial`, eucl `fun _ _ _ _ _ => trivial` |

Frame-condition argument shapes (note the heterogeneity — this is why the soundness wrappers
cannot share a single signature, and why the parameterization must take an opaque callback):
- reflexivity: `∀ w, m.r w w` → `fun _ => trivial`
- transitivity: `∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃` → `fun _ _ _ _ _ => trivial`
- symmetry: `∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁` → `fun _ _ _ => trivial`
- euclideanness: `∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃` → `fun _ _ _ _ _ => trivial`
- seriality: passed as a `Relation.Serial m.r` **instance** `⟨fun w => ⟨w, trivial⟩⟩`

All discharge terms are vacuous (`trivial`) because the universal relation `fun _ _ => True`
makes every frame condition hold trivially; seriality holds because each world relates to
itself.

## Concrete Parameterization Strategy (verified to compile)

Place a new theorem in `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean`:

```lean
/-- Parametric conservative extension of CPL: if `φ.toModal` is derivable in any modal
system whose axioms are sound at the universal `Unit` model, then `φ` is CPL-derivable. -/
theorem modal_conservative_extension_param {Atom : Type*}
    {Axioms : Modal.Proposition Atom → Prop} {φ : PL.Proposition Atom}
    (h : Derivable Axioms φ.toModal)
    (h_sat : ∀ (v : Atom → Prop),
      Modal.Satisfies (⟨fun _ _ => True, fun _ => v⟩ : Modal.Model Unit Atom) () φ.toModal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v
  exact (modal_satisfies_toModal_iff_evaluate _ () φ).mp (h_sat v)
```

The callback `h_sat` is the per-valuation satisfaction of `φ.toModal` at the universal model
— exactly the term each current file builds with `<sys>_soundness d m <frame> () (...)`.

### Why a callback (not direct frame-condition parameters)

The 15 `*_soundness` wrappers have *different signatures* (0–3 frame conditions; seriality is
an instance, not a hypothesis). A single theorem cannot abstract over that heterogeneity by
naming the conditions. Taking the already-discharged satisfaction term as a callback cleanly
sidesteps this — the model construction (`⟨fun _ _ => True, fun _ => v⟩`), the
`prop_completeness`/`intro v`/`obtain ⟨d⟩` boilerplate, and the bridge-lemma application are
all factored into the parametric theorem; only the system-specific `*_soundness …` call
remains per-file.

### Each system instantiation (~5 lines, verified for S5/D/K)

```lean
theorem s5_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@ModalAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact s5_soundness d _ (fun _ => trivial) (fun _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ => trivial) () (fun _ h => nomatch h)
```

(D: `d_soundness d _ ⟨fun w => ⟨w, trivial⟩⟩ () (...)`; K: `k_soundness d _ () (...)`.)

### Verification performed

A scratch file `Cslib/Logics/Modal/Metalogic/ConservativeExtensionScratch.lean` was created
with the parametric theorem and S5/D/K instantiations. `lake build` succeeded
(`Built …Scratch`) with **zero errors**. The only warning is an unused binder-name `h` in the
`h_sat` callback type — fixed by renaming the existing `h : Derivable …` or the binder. The
scratch file was deleted after verification.

## Lint / Standards Considerations

- New file must begin with `module` then `public import …` (the `import Cslib.Init` is implied
  by the `module` header convention used in sibling files — confirmed by building against the
  existing module headers).
- Theorem is `Prop`-valued → use `theorem` (not `def`). Already done.
- Docstring required (docBlame) → include the `/-- … -/` block shown above.
- Name `modal_conservative_extension_param` is lowerCamelCase-compatible (snake_case is the
  established convention for these theorems, matching `modal_conservative_extension`,
  `*_conservative_extension`, `*_soundness`). Match the surrounding file convention.
- Namespace: `Cslib.Logic` with `open PL Cslib.Logic.Modal` (matches all 15 current files).
- One benign linter warning (`unused binder name`) appeared in the draft — resolve by naming
  the callback's bound valuation `_` (already shown) and ensuring no shadowed `h`.

## Recommended File Plan

1. **New**: `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` containing
   `modal_conservative_extension_param`. Imports:
   `Cslib.Logics.Modal.FromPropositional`,
   `Cslib.Logics.Propositional.Metalogic.StrongCompleteness`,
   `Cslib.Logics.Modal.Metalogic.DerivationTree`.
2. **Rewrite** each of the 15 `Systems/*/ConservativeExtension.lean` to a ~5-line
   instantiation calling `modal_conservative_extension_param` with that system's
   `*_soundness` term (per the Frame-Condition Discharge Table). Each file additionally
   imports the new `Metalogic/ConservativeExtension.lean` (and keeps its existing
   `Systems/<sys>/Soundness.lean` + `FromPropositional` + `StrongCompleteness` imports).
3. **Barrel import**: run `lake exe mk_all --module` since a new file is added.
4. Preserve each public theorem name `<sys>_conservative_extension` (downstream/`InterSystem`
   may reference them — verify with `grep` before finalizing).

### Estimated reduction

Header/docstring (~33 lines) shrinks to ~5-line proof bodies per file. Current 896 lines →
roughly 15 × (12-line header+stub) + ~40-line shared theorem ≈ 220 lines. Net reduction
**~400+ lines**, plus removal of 15 copies of the model-construction boilerplate. Meets the
~400-line target.

## Tactic Survey

No tactic search needed — this is a transcription/refactor with an existing complete proof.
The parametric proof body is two lines (`apply prop_completeness; intro v` then `exact`),
verified by build. No `aesop`/`simp`/`omega` exploration was required.

## Risks / Notes for Planner

- **Zero sorry risk**: all sub-proofs already exist and compile; this is mechanical extraction.
- **Heterogeneous soundness signatures** are the only real design constraint — addressed by the
  callback design (do NOT attempt to parameterize over the frame conditions by name).
- **K's distinct current proof style** is absorbed cleanly (verified via `k_test`).
- Before rewriting, `grep -rn "_conservative_extension" Cslib/` to confirm no other module
  depends on the concrete proof *terms* (only the statements matter; statements are preserved).
- Recommend a single implementation phase: add the parametric theorem + rewrite all 15 files +
  `mk_all` + `lake build`. The change is uniform and low-risk enough not to need phase splits.
```
