# Zulip Thread Analysis: Propositional Logic (Anchor 605341190)

**Thread**: CSLib / Propositional Logic
**URL**: https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/605341190
**Anchor message**: 605341190 (Thomas Waring, 2026-06-21)
**Messages fetched**: 9 (5 before anchor, 3 after; range 603884159–605827029)
**Analysis date**: 2026-06-22

---

## Messages Analyzed

| Message ID | Sender | Date | Summary |
|------------|--------|------|---------|
| 603884159 | Thomas Waring | 2026-06-16 | `evaluate` completeness and `GeneralizedHeytingAlgebra` for MPL |
| 603958377 | Matthew Doty | 2026-06-17 | `botForces` unusual; HA strengthening via DM completion |
| 604025028 | Thomas Waring | 2026-06-17 | `v ⊥ ≠ ⊥` needed for MPL; Benjamin's `bot_val` explained |
| 604166734 | Matthew Doty | 2026-06-17 | Explicit falsum + fragment discussion; DPLL complexity with `⊥ : Atom` |
| 604219492 | Benjamin Brast-McKie | 2026-06-17 | Substitution invariance argument for primitive `⊥`; `bot_val` as Johansson's constant |
| **605341190** | **Thomas Waring** | **2026-06-21** | **Anchor: free-algebra perspective; GHA vs HA; `botVal` "unnatural"** |
| 605712144 | Matthew Doty | 2026-06-22 | IPL as base; fragment design as open question |
| 605813681 | Benjamin Brast-McKie | 2026-06-22 | Summary of ND trade-offs; `bot_val` as designated constant; typeclass options |
| 605827029 | Chris Henson | 2026-06-22 | Query about AI usage policy |

---

## Claim-by-Claim Verification

### Claim 1 (Thomas Waring, msg 603884159)
> "completeness is no longer true for minimal logic — this is why Benjamin's Kripke definitions need separate fields for the valuation of atoms and of bottom"

**Verification**: CONFIRMED.

`KripkeModel` in `Cslib/Logics/Propositional/Semantics/Kripke.lean` (lines 58–67) has a `botForces : World → Prop` field that is separate from the atom valuation `v : World → Atom → Prop`. `IForces` uses `bot_forces w` for the `.bot` case (line 85). `IValid` hardcodes `bot_forces = fun _ => False` (line 148), while `MValid` allows arbitrary upward-closed `bot_forces` (lines 153–158).

This separation exists precisely because MPL completeness requires allowing `⊥` to be forced in some worlds, which collapses to intuitionistic if `bot_forces = fun _ => False`.

---

### Claim 2 (Thomas Waring, msg 603884159)
> "this is avoided by just making `⊥` an atom itself"

**Verification**: CONTEXTUALLY ACCURATE (about Thomas's external branch, not CSLib main).

This is a description of Thomas's `cslib_SKI` branch design, not CSLib main. In CSLib main, `⊥` is a primitive constructor of `Proposition` (`Cslib/Logics/Propositional/Defs.lean`, line 154 via `abbrev MPL : Theory (Atom) := ∅`; the `Proposition` type has a `.bot` constructor). Thomas's claim accurately states that in his alternative design, making `⊥ : Atom` eliminates the need for a separate `bot_val` field at the cost of other complications.

---

### Claim 3 (Thomas Waring, msg 603884159 and 605341190)
> The general completeness theorem uses `GeneralizedHeytingAlgebra` and `Valuation`; specializing to IPL requires `HeytingAlgebra` and `v ⊥ = ⊥`

**Verification**: CONFIRMED for CSLib main.

`Theory.alg_complete` in `Semantics/Algebra/Completeness.lean` (lines 218–229) has signature:
```lean
theorem Theory.alg_complete {A : Proposition Atom} :
    DerivableIn T A ↔
      ∀ {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
        AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤
```

`IPL.alg_complete` (lines 252–267) specializes to `[HeytingAlgebra H]` with `bot_val = ⊥`.

Thomas's branch uses `Valuation Atom H` as a named type (per his external `Heyting.lean`). In CSLib main, valuations are bare functions `v : Atom → H`; there is no `Valuation Atom H` named type in the algebraic semantics files. The `Valuation` type in CSLib (`Bool.lean` line 51) is `Atom → Prop`, used only for bivalent semantics.

---

### Claim 4 (Thomas Waring, msg 605341190)
> "a `GeneralizedHeytingAlgebra` is not an algebra over the signature with `⊥`, which is why you need the extra unnatural field `botVal`"

**Verification**: CONFIRMED AS A MATHEMATICAL FACT; the "unnatural" characterization is DESIGN-CONTESTED.

`GeneralizedHeytingAlgebra` in Mathlib lacks `⊥`, so `AlgEvaluate` requires an explicit `bot_val : H` parameter (confirmed: `Semantics/Algebra.lean` lines 82–88). Thomas's characterization of this as "unnatural" is a design judgment, not a factual error. Benjamin's response (msg 604219492 and 605813681) argues that `bot_val` is the designated constant of Johansson algebras (a principled design choice corresponding to Johansson 1937), and that calling it "unnatural" conflates a free parameter in the model with a defect.

The field name is `bot_val` in the parameter position of `AlgEvaluate`, and `botForces` in `KripkeModel`. There is no struct field called `botVal` in CSLib main.

---

### Claim 5 (Thomas Waring, msg 605341190)
> "If we add the constructor to the signature, we should also add efq to the derivation type... which makes the interpretation land in `HeytingAlgebra`"

**Verification**: ACCURATE as a logical consequence; this is the design choice Thomas advocates.

In CSLib main, `⊥` is a primitive constructor of `Proposition` but `efq` is NOT a primitive constructor of `Theory.Derivation`. Instead, efq enters as a theory axiom via `[IsIntuitionistic T]`. The `Implementation notes` in `NaturalDeduction/Basic.lean` (lines 43–88) explicitly acknowledges this trade-off and states it as a deliberate design choice:

> "ex falso quodlibet (`⊥ → A`) is not a primitive rule — it enters as a theory axiom via `[IsIntuitionistic T]`"

Thomas's logical point is correct: adding `⊥` as a constructor and `efq` as a rule would naturally land in `HeytingAlgebra` semantics. CSLib's hybrid design breaks this correspondence intentionally for the sake of API uniformity.

---

### Claim 6 (Matthew Doty, msg 603958377)
> "I've never seen anything like `botForces` for Kripke semantics for intuitionistic logic before... I wonder why it's needed."

**Verification**: UNDERSTANDABLE SURPRISE, BUT STANDARD.

`botForces` is needed for MPL, not IPL. For IPL, CSLib uses `IValid` with `bot_forces = fun _ => False` (Kripke.lean line 148), which is standard. The `MValid` definition with parameterized `botForces` is what handles MPL. Matthew's observation that `botForces` is unusual for intuitionistic logic is correct—it appears in the MPL definition path, not the standard intuitionistic path.

---

### Claim 7 (Benjamin Brast-McKie, msg 604219492)
> "CSLib's substitution results — `subst_preserves_axiom`, `subst_preserves_intAxiom`, `subst_preserves_minAxiom`, `hilbertSubstitution`, `Theory.Derivation.substAtom` — all work cleanly because of [primitive `⊥`]"

**Verification**: CONFIRMED.

All five named lemmas exist in CSLib main:
- `subst_preserves_axiom` — `NaturalDeduction/FromHilbert.lean` line 232
- `subst_preserves_intAxiom` — line 250
- `subst_preserves_minAxiom` — line 267
- `hilbertSubstitution` — line 286
- `Theory.Derivation.substAtom` — `NaturalDeduction/Basic.lean` line 305

None of these lemmas require a `σ(⊥) = ⊥` side condition because `.bot` is handled by the `| .bot => .bot` case in `Proposition.bind` (the substitution monad). This is the precise point Benjamin is making: with `⊥` as a primitive constructor, substitution automatically preserves it.

---

### Claim 8 (Benjamin Brast-McKie, msg 604219492)
> "Thomas's completeness theorem is genuinely elegant with the `v ⊨ t` framing — and it works just as well with primitive `⊥` and `bot_val`"

**Verification**: CONFIRMED — `AlgTValid` implements exactly this.

`AlgTValid` in `Semantics/Algebra.lean` (lines 141–143):
```lean
def AlgTValid {H : Type*} [GeneralizedHeytingAlgebra H]
    (T : PL.Theory Atom) (v : Atom → H) (bot_val : H) : Prop :=
  ∀ B ∈ T, AlgEvaluate v bot_val B = ⊤
```

The general `Theory.alg_complete` uses `AlgTValid T v bot_val → AlgEvaluate v bot_val A = ⊤`, which is the `v ⊨ T → v ⊨ A` framing Thomas proposed.

---

### Claim 9 (Benjamin Brast-McKie, msg 605813681)
> "I've also added docstrings to all definitions in `Semantics/Algebra/Completeness.lean`"

**Verification**: CONFIRMED.

Reading `Completeness.lean` lines 212–287: all major definitions (`Theory.canonicalV`, `Theory.canonicalBotVal`, `Theory.canonicalBotVal_eq`, `Theory.tValid_canonicalV`, `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`) have docstrings. The Lindenbaum construction is documented.

---

### Claim 10 (Benjamin Brast-McKie, msg 605813681)
> "the conservative extension theorem `ipl_conservative_over_mpl` requires Dedekind-MacNeille completion"

**Verification**: CONFIRMED — but note: the theorem is currently `sorry`.

`Conservative.lean` line 96–99:
```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry
```

The docstring (lines 84–99) explicitly states the proof requires DM completion and is deferred. This is consistent with what Benjamin said, but he presented it as "already adopted" while the proof is not yet complete.

---

### Claim 11 (Thomas Waring, msg 605341190)
> "I'm still not exactly convinced re the cost issue... if you have the `bot_val` field in your definition of valuation, then you still need to ensure for intuitionistic applications that `v ⊥ = ⊥`. You made a separate definition for `IForces` if I remember correctly, which could be encoded simply as a subtype."

**Verification**: PARTIALLY ACCURATE.

Thomas is right that there are two separate definitions: `IValid` (with `bot_forces = fun _ => False`) and `MValid` (with arbitrary `bot_forces`). However, the "cost" is symmetric: in CSLib's design, the restriction to `fun _ => False` is embedded in the `IValid` definition itself, not a side condition on theorems. The `bot_val = ⊥` condition for IPL's algebraic semantics is handled by `IPL.alg_complete` fixing `bot_val = ⊥` at the completeness theorem level, not as a predicate on valuations.

Thomas's subtype suggestion (`IForces` as a subtype of `bot_forces = fun _ => False`) would work but adds definitional complexity without eliminating the semantic distinction.

---

### Claim 12 (Benjamin Brast-McKie, msg 604219492)
> "`⊥` is a nullary operation symbol — same ontological kind as `→` and `∧`"

**Verification**: ACCURATE (design philosophy claim, not codebase-verifiable).

This is a theoretical framing consistent with universal algebra. In CSLib's `Proposition` type, `⊥` is a nullary constructor (`.bot : Proposition Atom`), while atoms are parameterized by `Atom` — making them the "generators" and `⊥` an "operation." This is a design philosophy claim, not a codebase fact, but it is internally consistent with the Lean implementation.

---

## Key Disputes Identified

### Dispute 1: `⊥` as Atom vs. Primitive Constructor
- **Thomas**: MPL's free-algebra should use `GeneralizedHeytingAlgebra` without `⊥`; making `⊥` an atom is cleaner
- **Benjamin**: `⊥` as a constructor gives unconditional substitution invariance; `⊥`-as-atom infects all substitution lemmas with `σ(⊥) = ⊥` side conditions
- **CSLib main position**: Primitive constructor (Benjamin's view is implemented)

### Dispute 2: `botVal` as "unnatural"
- **Thomas**: The `bot_val` field is "unnatural" because `GeneralizedHeytingAlgebra` doesn't have `⊥`
- **Benjamin**: `bot_val` is Johansson's designated constant — a principled parameter, not a patch
- **Assessment**: Both framings are internally consistent. Thomas's characterization is a design preference; Benjamin's is a mathematical reference claim. The field is named `bot_val` (parameter to `AlgEvaluate`), not a struct field.

### Dispute 3: ND Symmetry vs. API Uniformity
- **Thomas**: Natural deduction's appeal requires constructor-rule correspondence; `⊥` with no derivation constructor breaks Gentzen symmetry
- **Benjamin**: `⊥` has no introduction rule in any system; asymmetry is a property of `⊥`, not the design; duplication cost is too high
- **CSLib main position**: Hybrid design (Benjamin's view); acknowledged explicitly in `NaturalDeduction/Basic.lean` lines 55–76

### Dispute 4: IPL vs. MPL as base
- **Thomas**: MPL as base (with IPL encoded via theory); natural from ND/computation perspective
- **Matthew**: IPL as base is easier for various developments
- **Benjamin**: Primitive `⊥` is non-negotiable; the IPL/MPL question is about theory parameters
- **CSLib main position**: Single `Proposition` type with primitive `⊥`; MPL = empty theory, IPL = theory with efq axioms

---

## Context: CSLib Main vs. External Branches

All claims in this thread concern two distinct codebases:

| Claim type | Source |
|------------|--------|
| Thomas's `AlgEvaluate` design, `Valuation Atom H` type | `cslib_SKI/kripke` and `cslib_SKI/intuitionistic` branches (external) |
| `bot_val`, `botForces`, `AlgTValid`, completeness theorems | CSLib main (verified above) |
| Matthew's DM completion result | `xcthulhu/cslib` fork (external) |

The core CSLib main files (`Semantics/Algebra.lean`, `Semantics/Algebra/Completeness.lean`, `Semantics/Kripke.lean`, `NaturalDeduction/Basic.lean`) implement Benjamin's position throughout.

---

## Confidence Summary

| Claim | Author | Confidence | Status |
|-------|--------|------------|--------|
| MPL completeness needs `bot_val ≠ ⊥` freedom | Thomas | HIGH | CONFIRMED |
| `botForces` as separate Kripke field | Thomas | HIGH | CONFIRMED |
| `Theory.alg_complete` uses GHA + `bot_val` | Benjamin | HIGH | CONFIRMED |
| `IPL.alg_complete` uses HA + `bot_val = ⊥` | Benjamin | HIGH | CONFIRMED |
| Substitution lemmas work unconditionally | Benjamin | HIGH | CONFIRMED |
| `AlgTValid` implements `v ⊨ T` framing | Benjamin | HIGH | CONFIRMED |
| `bot_val` is "unnatural" | Thomas | MEDIUM | DISPUTED (design judgment) |
| GHA "not an algebra over signature with ⊥" | Thomas | HIGH | CONFIRMED (math fact) |
| Conservative extension theorem is sorry | (implicit) | HIGH | CONFIRMED (sorry in Conservative.lean) |
| Docstrings added to Completeness.lean | Benjamin | HIGH | CONFIRMED |
| `botForces` as Kripke field is unusual | Matthew | MEDIUM | ACCURATE (for IPL; needed for MPL) |
| ND symmetry broken by hybrid design | Thomas | HIGH | CONFIRMED (acknowledged in Basic.lean) |
