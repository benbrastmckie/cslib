# Research Report: Conservative Extension of Modal Systems over CPL

**Task**: 273 -- all_modal_systems_conservative_over_cpl
**Date**: 2026-06-22
**Session**: sess_1782161605_f646ec_273

## Summary

Prove that all 14 remaining modal systems (T, B, D, K4, K5, K45, D4, D5, D45, DB, TB, KB5,
S4, S5) are conservative extensions of Classical Propositional Logic (CPL) for propositional
formulas. The K proof already exists; each new system needs a `ConservativeExtension.lean`
file following the same structure. All 14 proofs have been verified to compile via
`lean_run_code`.

## Existing K Pattern

**File**: `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`

The K proof composes three results:
1. **K Soundness** (`k_soundness_derivable`): K-derivable formulas are valid on ALL Kripke frames (no frame conditions).
2. **Semantic bridge** (`toModal_valid_implies_tautology`): validity of `phi.toModal` implies propositional tautologyhood.
3. **CPL Completeness** (`prop_completeness`): propositional tautologies are CPL-derivable.

```lean
theorem modal_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@KAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  prop_completeness (toModal_valid_implies_tautology
    (fun _ m w => k_soundness_derivable h m w))
```

K is special: it has no frame conditions, so `k_soundness_derivable` gives validity on ALL
models, making it directly compatible with `toModal_valid_implies_tautology` (which quantifies
over all models).

## Key Insight for Systems with Frame Conditions

Systems like T (reflexive), D (serial), S5 (reflexive + transitive + Euclidean), etc.
have soundness only relative to their frame class. The `toModal_valid_implies_tautology`
approach from K does NOT directly generalize because it requires validity on ALL models.

**Solution**: Construct a specific model satisfying ALL possible frame conditions. The
universal model `(Unit, fun _ _ => True, fun _ => v)` is:

| Property | Proof term |
|----------|-----------|
| Reflexive | `fun _ => trivial` |
| Symmetric | `fun _ _ _ => trivial` |
| Transitive | `fun _ _ _ _ _ => trivial` |
| Euclidean | `fun _ _ _ _ _ => trivial` |
| Serial | `⟨fun w => ⟨w, trivial⟩⟩` |

Since `phi.toModal` contains no `box` operators, the accessibility relation plays no role
in satisfaction (the bridge lemma `modal_satisfies_toModal_iff_evaluate` confirms this).
The valuation `fun _ => v` ensures `Evaluate v phi` follows.

## Proof Pattern for All 14 Systems

Each system follows this template (verified to compile for all 14):

```lean
theorem {sys}_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@{SysAxiom} Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v
  let m : Modal.Model Unit Atom := ⟨fun _ _ => True, fun _ => v⟩
  obtain ⟨d⟩ := h
  exact (modal_satisfies_toModal_iff_evaluate m () φ).mp
    ({sys}_soundness d m {frame_condition_proofs} () (fun _ h => nomatch h))
```

**No `_soundness_derivable` wrapper is needed.** The task description mentions adding
`_soundness_derivable` wrappers, but analysis shows they are unnecessary: the proof works
directly with `_soundness` (the `Gamma |- phi` version) by destructuring `Derivable` into
its `DerivationTree` and discharging the empty context. This avoids 14 intermediate lemmas
in the Soundness.lean files.

## Per-System Specification

Each file needs: copyright header, `module` keyword, imports, docstring, `@[expose] public
section`, namespace `Cslib.Logic`, one theorem, end namespace, end section.

### Group A: No Seriality (vacuous frame conditions via `fun _ _ ... => trivial`)

| System | Axiom Type | Frame Conditions | Soundness Args |
|--------|-----------|-----------------|----------------|
| T | `TAxiom` | refl | `(fun _ => trivial)` |
| B | `BAxiom` | symm | `(fun _ _ _ => trivial)` |
| K4 | `K4Axiom` | trans | `(fun _ _ _ _ _ => trivial)` |
| K5 | `K5Axiom` | eucl | `(fun _ _ _ _ _ => trivial)` |
| K45 | `K45Axiom` | trans, eucl | `(fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)` |
| TB | `TBAxiom` | refl, symm | `(fun _ => trivial) (fun _ _ _ => trivial)` |
| KB5 | `KB5Axiom` | symm, eucl | `(fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)` |
| S4 | `S4Axiom` | refl, trans | `(fun _ => trivial) (fun _ _ _ _ _ => trivial)` |
| S5 | `ModalAxiom` | refl, trans, eucl | `(fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)` |

### Group B: Requires Seriality (need `⟨fun w => ⟨w, trivial⟩⟩` for `Relation.Serial`)

| System | Axiom Type | Frame Conditions | Soundness Args |
|--------|-----------|-----------------|----------------|
| D | `DAxiom` | serial | `⟨fun w => ⟨w, trivial⟩⟩` |
| D4 | `D4Axiom` | serial, trans | `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial)` |
| D5 | `D5Axiom` | serial, eucl | `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial)` |
| D45 | `D45Axiom` | serial, trans, eucl | `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)` |
| DB | `DBAxiom` | serial, symm | `⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ => trivial)` |

## Imports Required

Each `ConservativeExtension.lean` needs exactly three imports:
1. `Cslib.Logics.Modal.FromPropositional` (for `toModal`, bridge lemma)
2. `Cslib.Logics.Modal.Metalogic.Systems.{System}.Soundness` (for `{sys}_soundness`)
3. `Cslib.Logics.Propositional.Metalogic.StrongCompleteness` (for `prop_completeness`)

## File Structure

Each file creates:
- `Cslib/Logics/Modal/Metalogic/Systems/{System}/ConservativeExtension.lean`

Estimated 55-60 lines per file (header + imports + docstring + theorem + closing).
Total: 14 files, approximately 800 lines.

After file creation, run:
- `lake exe mk_all --module` to update `Cslib.lean` barrel imports

## Verification Status

All 14 proofs verified via `lean_run_code`:
- Group A (9 systems): T, B, K4, K5, K45, TB, KB5, S4, S5 -- all compile
- Group B (5 systems): D, D4, D5, D45, DB -- all compile

## Theorem Naming Convention

Following the existing pattern in each system's namespace:
- `t_conservative_extension`
- `b_conservative_extension`
- `d_conservative_extension`
- `k4_conservative_extension`
- `k5_conservative_extension`
- `k45_conservative_extension`
- `d4_conservative_extension`
- `d5_conservative_extension`
- `d45_conservative_extension`
- `db_conservative_extension`
- `tb_conservative_extension`
- `kb5_conservative_extension`
- `s4_conservative_extension`
- `s5_conservative_extension`

All theorems live in namespace `Cslib.Logic` (matching the K version's `modal_conservative_extension`).

## Potential Obstacles

None identified. All proofs are mechanical and have been verified to compile. The only
operational considerations are:
1. Line length: S5's soundness call with 3 frame condition proofs may need line-breaking
   to stay within 100-character limit.
2. Barrel file update: `lake exe mk_all --module` after creating all 14 files.
3. Init import: Each file must include the `module` keyword (which handles `Cslib.Init` import
   via the module system).
