# Teammate B Findings: Downstream Impacts and Alternative Strategies

**Task 254**: Revise LTL conventions on main to conform to feat/temporal-formula-propositional  
**Scope**: Downstream impact analysis, breakage map, phasing strategy

---

## Key Findings

### 1. Connective Typeclass Hierarchy: What the Feature Branch Removes

The current `main` branch `Cslib/Foundations/Logic/Connectives.lean` defines eight typeclasses:

| Typeclass | Status in Feature Branch |
|---|---|
| `HasBot` | Kept |
| `HasImp` | Kept |
| `HasUntil` | Kept |
| `HasNext` | Kept |
| `HasBox` | Kept |
| `HasAnd`, `HasOr` | Kept |
| `HasSince` | **REMOVED** |
| `PropositionalConnectives` | Kept |
| `FutureTemporalConnectives` | Kept |
| `LTLConnectives` | Kept |
| `ModalConnectives` | **REMOVED** |
| `TemporalConnectives` | **REMOVED** |
| `BimodalConnectives` | **REMOVED** |

The feature branch `Connectives.lean` reduces to: `HasBot`, `HasImp`, `HasUntil`, `HasNext`, `HasAnd`, `HasOr`, `PropositionalConnectives`, `FutureTemporalConnectives`, `LTLConnectives`.

### 2. Notation Convention Changes

| Feature | Current (main) | Target (feature branch) |
|---|---|---|
| Until infix | `" U "` | `" 𝓤 "` (𝓤 is Mathlib's uniformity symbol) |
| Next prefix | `"X"` | `"◯"` |
| Eventually prefix | `"𝐅"` | `"◇"` |
| Globally prefix | `"𝐆"` | `"□"` |
| someFuture body | `φ U ⊤` (event first) | `⊤ U φ` (guard first) |
| Leads-to | absent | `"⇝"` added |
| Burgess1982I ref | present in LTL/Syntax/Formula | removed |
| Burgess1984 ref | present | removed |

### 3. Satisfies.lean Semantic Changes

Current `Satisfies.lean` (main):
- Signature: `Satisfies (v : ℕ → (Atom → Prop)) (i : ℕ) : Formula Atom → Prop`
- `untl` case (Burgess: event first): `∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ` where `untl ψ φ` (ψ=guard, φ=event)

Target `Satisfies.lean` (feature branch):
- Signature: `Satisfies (v : Atom → State → Prop) (w : ωSequence State) : Formula Atom → Prop`
- New imports: `Cslib.Foundations.Data.OmegaSequence.Init`
- `untl` case (standard: guard first): `∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ` where `untl φ ψ` (φ=guard, ψ=event)
- Adds new `State` type variable

---

## Breakage Analysis

### Directly Breaking: Typeclasses

**`HasSince`** — used in:
- `Cslib/Foundations/Logic/Connectives.lean` (definition)
- `Cslib/Foundations/Logic/Axioms.lean` (lines 189–341): extensive use of `HasSince.snce` in 12+ axiom bodies
- `Cslib/Foundations/Logic/ProofSystem.lean` (lines 81, 95, 200, 428, 457): `HasSince` constraint on 4 classes
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` (line 33, 45): `somePast` abbreviation
- `Cslib/Logics/Temporal/Syntax/Formula.lean`: `instance : TemporalConnectives` uses `snce`
- `Cslib/Logics/Bimodal/Syntax/Formula.lean`: `instance : BimodalConnectives` uses `snce`

**`TemporalConnectives`** — used in:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` (lines 133–134): the sole instance registration

**`BimodalConnectives`** — used in:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` (lines 105–106): the sole instance registration

**`ModalConnectives`** — used in:
- `Cslib/Logics/Modal/Basic.lean` (lines 117–118): `instance : ModalConnectives (Proposition Atom)`
- `Cslib/Foundations/Logic/Connectives.lean` (lines 127, 155–167): definition + bridge instance
- `Cslib/Foundations/Logic/Axioms.lean` (lines 153, 164, 176): docstring references only

### Impact on Logics

**Temporal Logic (`Cslib/Logics/Temporal/`)**: The Temporal formula type (`Formula.snce`) is a concrete inductive constructor — it is **not** affected by removing `HasSince` or `TemporalConnectives`. The concrete `Formula.snce` constructor will still exist. Only the typeclass _instance registration_ (`instance : TemporalConnectives`) needs updating. All proof files in `Temporal/Metalogic/` reference `Formula.snce` directly, not via `HasSince.snce`, so they are **unaffected** by the typeclass removal.

**Bimodal Logic (`Cslib/Logics/Bimodal/`)**: Same analysis. Bimodal's `Formula.snce` is a concrete constructor. Proof files use it directly. Only the `instance : BimodalConnectives` registration is affected. No Bimodal metalogic file uses `BimodalConnectives` or `ModalConnectives` as a constraint — confirmed by grep showing zero matches outside `Syntax/Formula.lean`.

**Modal Logic (`Cslib/Logics/Modal/`)**: `ModalConnectives` is used as the instance type in `Basic.lean`. If the class is removed from `Connectives.lean`, this instance declaration breaks. However, the downstream files in `Modal/ProofSystem/`, `Modal/Metalogic/` use `[HasBox F]` directly — not `[ModalConnectives F]`. So only `Basic.lean` needs updating (replace `ModalConnectives` instance with individual `HasBox` and `PropositionalConnectives` or equivalent).

**Foundations (`Cslib/Foundations/Logic/Axioms.lean`, `ProofSystem.lean`, `Theorems/`)**: The `HasSince.snce` usages in `Axioms.lean` and `ProofSystem.lean` are in axiom/rule bodies that are part of the full bimodal/temporal axiom system. If `HasSince` is removed, these sections must either be deleted or migrated. The feature branch's `Connectives.lean` confirms these sections are simply removed (the temporal axiom family `[HasBot F] [HasImp F] [HasUntil F] [HasSince F]` disappears from `Foundations/`).

### Directly Breaking: Notation

**`" U "` notation**: defined in `LTL/Syntax/Formula.lean`, `Bimodal/Syntax/Formula.lean`, `Temporal/Syntax/Formula.lean`. Changing to `" 𝓤 "` is a **notation-only** change for LTL (scoped). Bimodal and Temporal keep `" U "` (they are not in scope of the LTL change per the task description).

**Warning**: `𝓤` is already defined in Mathlib as `uniformity` notation (`scoped[Uniformity]`). This creates a potential namespace clash if both `Uniformity` and LTL scopes are opened simultaneously. The Bimodal GNBA file and OmegaRegular do not open `Uniformity`, so no immediate clash, but it is a latent risk worth noting.

**`"X"` → `"◯"` and `"𝐅"` / `"𝐆"` → `"◇"` / `"□"`**: These are scoped LTL-namespace notation changes. No breakage outside LTL scope. Within LTL files, any use of `X φ`, `𝐅 φ`, or `𝐆 φ` notation would need updating — but since these are scoped, they only appear within `namespace Cslib.Logic.LTL` or explicit `open` statements.

**`someFuture` argument order** (`φ U ⊤` → `⊤ U φ`): This is the most semantically sensitive change. The current `Satisfies.lean` is written with `untl ψ φ` where ψ is the guard and φ is the event (Burgess). So `someFuture φ = .untl .top φ` means `.top` is the guard. The feature branch keeps the same inductive constructor positions but flips the docstring: `untl φ ψ` now means φ=guard, ψ=event, and `someFuture φ = .untl .top φ` now means `.top` is the guard and φ is the event.

**Critical insight**: the argument order of `Formula.untl` is not actually changing. The constructor is always `untl (φ₁ : Formula) (φ₂ : Formula)`. What changes is which of φ₁, φ₂ is called "guard" vs "event" in docstrings, and how `someFuture` is expressed. Looking carefully:
- Current main: `someFuture φ = .untl .top φ` (top is the second arg / "guard" in Burgess)
- Feature branch: `someFuture φ = .untl .top φ` (top is the first arg / "guard" in standard)

Both formulas produce the identical term `.untl .top φ`. The change is purely in the English description and docstrings, not in the actual Lean term structure.

**However**: The `Satisfies.lean` `untl` case changes from:
```
| .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```
to (feature branch):
```
| .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ
```

The pattern variable names are cosmetic, but the semantic content is the same: the second argument of `untl` is always the "event" (the formula that eventually holds). This is confirmed by the IsAtom.untlRight consistency condition in GNBA: `ψ₂ ∈ B → .untl ψ₁ ψ₂ ∈ B` (ψ₂ is the second argument and is the "eventuality"). So there is **no actual semantic inversion** — the semantics in the feature branch are consistent with what `Satisfies.lean` on main already computes. The only change is switching from `v : ℕ → (Atom → Prop)` to `v : Atom → State → Prop` with `ωSequence State`.

### Satisfies.lean Change Impact

The new `Satisfies.lean` signature `Satisfies (v : Atom → State → Prop) (w : ωSequence State)` changes the API used by:
- `OmegaExecutionSatisfies.lean`: currently defines `SatisfiesExec` wrapping `Satisfies`. If the signature changes, this wrapper needs updating (it currently uses `v : ℕ → (Atom → Prop)` and `i : ℕ`).
- `OmegaRegular.lean`: uses `Satisfies (fun n p => p ∈ v n) k φ` where `k : ℕ`. A key private lemma `satisfies_shift` establishes `Satisfies v (i + k) φ ↔ Satisfies (fun n => v (n + k)) i φ`. These proofs would need to be re-expressed in terms of `ωSequence` operations.
- `GNBA.lean`: uses `Formula.canonicalAtom v i φ` defined as `{ψ ∈ closure φ | Satisfies v i ψ}`. The entire GNBA construction builds on `Satisfies v i`. This is the most extensive downstream file.

**Summary**: Changing `Satisfies.lean` is the highest-impact change. It cascades into 3 files (OmegaExecutionSatisfies, OmegaRegular, GNBA) containing hundreds of proofs that use the current `(v, i)` signature.

### References.bib: No New Entries Needed

The task removes Burgess references from LTL Formula docstrings but Burgess1982I, Burgess1982II, Burgess1984 remain legitimately used in:
- Temporal logic (Metalogic, ProofSystem): `h_burgessR`, `BurgessR3Maximal`, chronicle construction
- Bimodal logic: extensively throughout Metalogic

So the BibTeX entries should **not** be removed. The only bib addition that might be warranted is `BaierKatoen2008` (already cited in GNBA.lean and Emptiness.lean but missing from `references.bib`).

---

## Strategy Recommendations

### Recommended Approach: Two-Phase Implementation

**Phase 1** (LTL-only, self-contained): Modify only `Cslib/Logics/LTL/` files.

Files to change:
1. `Cslib/Logics/LTL/Syntax/Formula.lean`:
   - Change notation: `"X"` → `"◯"`, `" U "` → `" 𝓤 "`, `"𝐅"` → `"◇"`, `"𝐆"` → `"□"`
   - Update `someFuture` docstring (argument order docstring only, term stays `.untl .top φ`)
   - Add `leadsto` abbreviation
   - Remove Burgess1982I, Burgess1984 references, keep Pnueli1977, VardiWolper1986
2. `Cslib/Logics/LTL/Semantics/Satisfies.lean`:
   - Rewrite with `ωSequence State` + `v : Atom → State → Prop` signature
   - Add import of `OmegaSequence.Init`
3. `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean`: update to new Satisfies API
4. `Cslib/Logics/LTL/Semantics/OmegaRegular.lean`: update to new Satisfies API
5. `Cslib/Logics/LTL/Semantics/GNBA.lean`: update `canonicalAtom` and all proofs using old Satisfies

This phase is large but LTL-contained.

**Phase 2** (Foundations connective hierarchy): Modify `Cslib/Foundations/Logic/Connectives.lean`.

Files to change:
1. `Cslib/Foundations/Logic/Connectives.lean`: remove `HasSince`, `TemporalConnectives`, `BimodalConnectives`, `ModalConnectives` (keep `HasBox`)
2. `Cslib/Foundations/Logic/Axioms.lean`: remove all `[HasSince F]` sections
3. `Cslib/Foundations/Logic/ProofSystem.lean`: remove `HasSince`-dependent proof system classes
4. `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`: remove `HasSince`-based theorems
5. `Cslib/Logics/Temporal/Syntax/Formula.lean`: update instance to use `FutureTemporalConnectives` + separate `HasSince` (or keep `TemporalConnectives` if that class is retained)
6. `Cslib/Logics/Bimodal/Syntax/Formula.lean`: update instance similarly
7. `Cslib/Logics/Modal/Basic.lean`: update instance to not use `ModalConnectives`

### Alternative Approach: Connectives-First

Reverse the phases: update `Connectives.lean` first, then update all downstream instantiations, then LTL. This has the advantage that Phase 1 is smaller (Foundations only), but the disadvantage that it breaks many files simultaneously and requires fixing them before LTL is touched.

### Alternative Approach: Notation-Only, Defer Semantics

Given the cascade from `Satisfies.lean` changes into GNBA.lean (the largest LTL file), one could:
1. Do notation changes + `someFuture`/`leadsto` additions in a single commit
2. Leave `Satisfies.lean` signature unchanged (keep `v : ℕ → (Atom → Prop)`, `i : ℕ`)
3. Defer the `ωSequence`-based semantics to a follow-up task

This is the lowest-risk option but does not fully achieve the feature branch's target for Satisfies.

### Recommended Order for Phase 1

Within Phase 1, the Satisfies change should come **last** within a single LTL-scoped commit because:
- `OmegaRegular.lean` has a private `satisfies_shift` lemma that is complex and must be re-expressed
- GNBA.lean is the most extensive proof file in LTL (1200+ lines)
- Both files can be updated together once the new Satisfies API is fixed

### References.bib Recommendation

Add `BaierKatoen2008` entry (currently cited by GNBA.lean and Emptiness.lean but missing from bib):
```bib
@book{BaierKatoen2008,
  author    = {Baier, Christel and Katoen, Joost-Pieter},
  title     = {Principles of Model Checking},
  publisher = {MIT Press},
  year      = {2008}
}
```

Do **not** remove Burgess1982I, Burgess1982II, or Burgess1984 — they remain legitimately used in Temporal and Bimodal metalogic.

---

## Confidence Level

**High confidence** on:
- Which files use `HasSince`, `TemporalConnectives`, `BimodalConnectives`, `ModalConnectives` (exhaustively grepped)
- That Bimodal/Temporal proof files do NOT use these typeclasses outside `Syntax/Formula.lean` (confirmed by grep returning zero hits)
- That removing `ModalConnectives` only affects `Modal/Basic.lean` (one instance declaration)
- That `someFuture φ = .untl .top φ` produces the same term before and after the convention change
- That the GNBA construction already treats `untl ψ₁ ψ₂` with ψ₂ as the event (consistent with feature branch)
- That `𝓤` has a Mathlib namespace clash risk

**Moderate confidence** on:
- The GNBA.lean cascade scope (the file is 1200+ lines and the Satisfies signature change is pervasive)
- Whether `satisfies_shift` and `mem_omegaLanguage_drop` can be cleanly re-expressed using `ωSequence` operations without significant proof revision

**Low confidence** on:
- The exact proof burden for `OmegaRegular.lean` and `GNBA.lean` after the `Satisfies` API change (would require full proof attempt to assess)
