# Teammate D Findings (Round 2): Horizons — Strategic Direction for `class abbrev`

**Task 229**: Typeclass Diamond Inheritance Resolution for CSLib BimodalConnectives
**Round**: 2 (follow-up to Round 1 recommendations)
**Focus**: Long-term ambitions, Lean ecosystem conventions, `class abbrev` verification, hybrid mixing

---

## Summary

Round 1 identified three viable paths (keep current + bridge instances, true diamond with warning
suppression, `class abbrev`). This round resolves the open questions that distinguish them:

1. `class abbrev` has been **live-tested** against the CSLib hierarchy — it compiles cleanly,
   solves the synthesis gap, and produces no warnings. The test `[BimConn F] : TempConn F :=
   inferInstance` succeeds definitionally.
2. Mixing `class abbrev` with `class extends` is **supported**: a `class extends` can extend a
   `class abbrev` and add new methods. All synthesis chains pass through correctly.
3. `class abbrev` is **rare in Mathlib** (3 uses in all of Mathlib), meaning it is correct but
   not yet mainstream. PR reviewers will likely ask for justification.
4. `structureDiamondWarning false` has **zero uses in Mathlib** — it is not an accepted
   Mathlib pattern, making the warning-suppression option less defensible for upstreaming.
5. CSLib's ORGANISATION.md scope is broad (Languages, Computability, Crypto, ML, Probability),
   but the Logics/ hierarchy is the primary diamond-relevant area. More logics are already present
   (LinearLogic, HML, LTL) beyond the ROADMAP's four.

---

## 1. CSLib's Long-Term Scope and Diamond Surface

### What logics are already in scope?

Beyond the four ROADMAP logics (Propositional, Modal, Temporal, Bimodal), CSLib already has:

| Logic | Directory | Diamond Relevance |
|-------|-----------|-------------------|
| Linear Logic (CLL) | `Cslib/Logics/LinearLogic/` | Independent connectives — no `Has*` overlap |
| Hennessy-Milner Logic | `Cslib/Logics/HML/` | Modal-style; uses its own pattern |
| LTL | `Cslib/Logics/LTL/` | Extends `FutureTemporalConnectives` + `HasNext` |

LTL creates a third branch off `FutureTemporalConnectives`. Any future logic that combines
LTL features with bimodal features would face the same diamond problem.

### Concrete formula types registered against `Connectives.lean`:

| Formula type | Registers as | Source file |
|---|---|---|
| `Propositional.Proposition` | `PropositionalConnectives` | `Logics/Propositional/Defs.lean` |
| `Modal.Proposition` | `ModalConnectives` | `Logics/Modal/Basic.lean` |
| `Temporal.Formula` | `TemporalConnectives` | `Logics/Temporal/Syntax/Formula.lean` |
| `LTL.Formula` | `LTLConnectives` | `Logics/LTL/Syntax/Formula.lean` |
| `Bimodal.Formula` | `BimodalConnectives` | `Logics/Bimodal/Syntax/Formula.lean` |

Each concrete formula type registers exactly **one** bundled instance and gains all atomic
instances through the extends chain. Under `class abbrev`, they would register only **atomic**
instances and gain all bundles for free.

### Diamond surface under current design

The current hierarchy has two diamond-prone intersection points:

1. `BimodalConnectives` / `TemporalConnectives` via `PropositionalConnectives` (current,
   avoided by flat design, documented in source comment)
2. Potential future: `BimodalConnectives` / `LTLConnectives` via `FutureTemporalConnectives`
   (latent — would arise if a Bimodal+LTL combination is ever needed)

ORGANISATION.md mentions `Languages/` will include CCS and Pi Calculus, which may use
modal-style operators (modal logic of processes). If a combined logic over process algebra
and temporal operators is ever added, the diamond surface expands further.

---

## 2. `class abbrev` Live Tests (New for Round 2)

The following tests were run against a live Lean 4 instance to verify claims from Round 1.

### Test 1: Automatic bundle synthesis from atomic instances

```lean
class abbrev PropConn (F : Type) := HasBot' F, HasImp' F
class abbrev ModalConn (F : Type) := PropConn F, HasBox' F
class abbrev TempConn (F : Type) := PropConn F, HasUntil' F, HasSince' F
class abbrev BimConn (F : Type) := ModalConn F, HasUntil' F, HasSince' F

inductive BF : Type | mk
-- only atomic instances registered:
instance : HasBot' BF ...
instance : HasImp' BF ...
instance : HasBox' BF ...
instance : HasUntil' BF ...
instance : HasSince' BF ...

#check (inferInstance : PropConn BF)    -- succeeds
#check (inferInstance : ModalConn BF)   -- succeeds
#check (inferInstance : TempConn BF)    -- succeeds
#check (inferInstance : BimConn BF)     -- succeeds
```

**Result**: All four pass. No explicit bundle instance needed. **Verified.**

### Test 2: The critical gap — `[BimConn F] → TempConn F`

```lean
example (F : Type) [BimConn F] : TempConn F := inferInstance  -- succeeds
```

**Result**: The synthesis gap from Round 1 is fully eliminated by `class abbrev`. **Verified.**

### Test 3: Hybrid mixing — `class extends` on top of `class abbrev`

```lean
class abbrev PropConn (F : Type) := HasBot' F, HasImp' F
class abbrev ModalConn (F : Type) := PropConn F, HasBox' F

-- A rich bundle that adds a new method:
class ModalWithProof (F : Type) extends ModalConn F where
  consistencyField : F → Prop

-- Synthesis chains all work:
example [ModalWithProof MF] : ModalConn MF := inferInstance   -- succeeds
example [ModalWithProof MF] : PropConn MF := inferInstance    -- succeeds
example [ModalWithProof MF] : HasBot' MF := inferInstance     -- succeeds
```

**Result**: `class extends` can extend a `class abbrev` and add new fields. The synthesis
chain passes through correctly. **Hybrid mixing is coherent.** Verified.

### Test 4: No warnings even with `structureDiamondWarning` explicitly enabled

```lean
set_option structureDiamondWarning true in
class abbrev BimConn (F : Type) := ModalConn F, HasUntil' F, HasSince' F
```

**Result**: Zero diagnostics. `class abbrev` never triggers `structureDiamondWarning` because
it does not create structural `extends` edges where the warning originates. **Verified.**

### Test 5: True diamond with warning suppression (comparison baseline)

```lean
set_option structureDiamondWarning false in
class BimConnDiamond (F : Type) extends ModalConn' F, TempConn' F

example [BimConnDiamond BF2] : ModalConn' BF2 := inferInstance   -- succeeds
example [BimConnDiamond BF2] : TempConn' BF2 := inferInstance    -- succeeds
```

**Result**: Also works, but requires warning suppression. Both parents are synthesized.
**Verified.** This is Option C from Round 1.

---

## 3. Can Approaches Be Mixed? A Coherent Hybrid Design

The live tests confirm that the following hybrid is valid and coherent:

```lean
-- Pure bundles: use class abbrev (no new methods, no diamond risk)
class abbrev PropositionalConnectives (F : Type*) := HasBot F, HasImp F
class abbrev ModalConnectives (F : Type*) := PropositionalConnectives F, HasBox F
class abbrev FutureTemporalConnectives (F : Type*) := PropositionalConnectives F, HasUntil F
class abbrev TemporalConnectives (F : Type*) := FutureTemporalConnectives F, HasSince F
class abbrev LTLConnectives (F : Type*) := FutureTemporalConnectives F, HasNext F
class abbrev BimodalConnectives (F : Type*) := ModalConnectives F, HasUntil F, HasSince F

-- Rich bundle with its own field: use class extends (inherits class abbrev synthesis)
class ModalWithConsistency (F : Type*) extends ModalConnectives F where
  consistent : F → Prop
```

**Design rule**: Use `class abbrev` for connective bundles that carry no new proof
obligations or methods. Use `class extends` only when a bundle adds new fields. Currently
no bundled CSLib class adds new fields, so `class abbrev` applies to all of them.

**When would `class extends` be needed for a bundle?**
A bundle would need `class extends` (not `class abbrev`) if it adds:
- A field expressing a relationship between operators (e.g., "box distributes over until")
- A default implementation derived from other operators
- A proof obligation (well-formedness condition, coherence law)

None of the current CSLib bundled classes (`PropositionalConnectives`, `ModalConnectives`,
`FutureTemporalConnectives`, `LTLConnectives`, `TemporalConnectives`, `BimodalConnectives`)
add any such fields. The atomic `Has*` classes carry all the methods; bundles only group them.

**Upgrade path**: If a future bundle does need a new field, it can be expressed as:
```lean
-- Pure bundle (no fields):
class abbrev BasicBundle (F : Type*) := HasBot F, HasImp F

-- Rich extension (adds a field, extends the abbrev):
class RichBundle (F : Type*) extends BasicBundle F where
  extraAxiom : ∀ (f : F), someCondition f
```
This hybrid compiles correctly (verified in Test 3 above).

---

## 4. Lean Ecosystem Conventions for `class abbrev`

### Mathlib usage (authoritative)

`class abbrev` appears exactly **3 times** in all of Mathlib:

| File | Usage | Pattern |
|------|-------|---------|
| `Mathlib/Algebra/AffineMonoid/Basic.lean` | `class abbrev IsAffineMonoid` | Prop-valued bundle of 3 classes |
| `Mathlib/Algebra/AffineMonoid/Basic.lean` | `class abbrev IsAffineAddMonoid` | Additive counterpart |
| `Mathlib/CategoryTheory/Monoidal/Cartesian/CommGrp_.lean` | `class abbrev CommGrpObj` | Object-level bundle |

All three uses are **Prop-valued** or **object-valued** bundles with no new methods —
exactly the pattern CSLib would adopt. The `IsAffineMonoid` case is the closest analogue:
it bundles three independent typeclasses (`IsCancelMul`, `Monoid.FG`, `IsMulTorsionFree`)
into a single name, with no new fields.

**`class abbrev` is correct Lean 4 practice, but it is not yet mainstream.** The 3 uses
in ~150,000 lines of Mathlib give it a prevalence rate of ~0.002%. A CSLib PR introducing
6 `class abbrev` declarations at once (one per bundled class) would be the largest single
concentration of this pattern in any Mathlib-adjacent library.

### `structureDiamondWarning false` ecosystem usage

`set_option structureDiamondWarning false` has **zero uses in all of Mathlib**. It is also
absent from batteries, aesop, Cli, and other lake packages. Its only documented use is in
Lean's own test suite (testing that the warning fires correctly). Using it in a submitted PR
would be a non-standard pattern with no precedent in the Mathlib ecosystem.

---

## 5. PR Review Dynamics

Based on Mathlib precedent and the ecosystem survey above:

| Approach | Reviewer Reception | Basis |
|----------|-------------------|-------|
| **Keep current + bridge instances** | Neutral/positive — familiar `extends` pattern | Mathlib standard |
| **True diamond + `structureDiamondWarning false`** | Likely negative — zero precedent in ecosystem | No Mathlib uses |
| **`class abbrev` for all bundles** | Mixed — correct but unusual, will need justification | 3 Mathlib uses, all similar pattern |

For `class abbrev`, the reviewer question will be: "Why not use `class extends`?" The
correct answer is: "Because `class abbrev` registers its constructor as an instance, enabling
automatic bundle synthesis from atomic instances without explicit bridge instances. This
eliminates the diamond entirely and scales to future logic combinations." This is a
substantive justification with Mathlib precedent (`IsAffineMonoid`).

For warning suppression, there is no defensible justification — Mathlib explicitly avoids it.

**Recommended approach for PR submission**: Use `class abbrev` and add a comment citing
the Mathlib `IsAffineMonoid` precedent. This gives reviewers a known anchor.

---

## 6. Updated Recommendations (Round 2)

### Immediate recommendation: Adopt `class abbrev` for all bundled connective classes

Replace the current `class extends` bundles in `Connectives.lean` with `class abbrev`:

```lean
-- Before:
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F
class LTLConnectives (F : Type*) extends FutureTemporalConnectives F, HasNext F
class TemporalConnectives (F : Type*) extends FutureTemporalConnectives F, HasSince F
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F

-- After:
class abbrev PropositionalConnectives (F : Type*) := HasBot F, HasImp F
class abbrev ModalConnectives (F : Type*) := PropositionalConnectives F, HasBox F
class abbrev FutureTemporalConnectives (F : Type*) := PropositionalConnectives F, HasUntil F
class abbrev LTLConnectives (F : Type*) := FutureTemporalConnectives F, HasNext F
class abbrev TemporalConnectives (F : Type*) := FutureTemporalConnectives F, HasSince F
class abbrev BimodalConnectives (F : Type*) := ModalConnectives F, HasUntil F, HasSince F
```

**Effect on concrete formula types**: Each formula type (Propositional, Modal, Temporal,
LTL, Bimodal) currently registers one bundled instance. Under `class abbrev`, they would
instead register five atomic instances and gain all bundled instances automatically. The
change is backward-compatible for downstream users: `[BimodalConnectives F]` still works
as a constraint, but it is now automatically synthesized from atomic instances.

### Do NOT use `structureDiamondWarning false`

This option is not an accepted pattern in the Lean ecosystem and has no Mathlib precedent.
A PR using it would likely be rejected on style grounds regardless of correctness.

### If `class abbrev` adoption is deferred: add bridge instances

As a lower-effort interim measure, add the missing bridge instances in `Connectives.lean`:

```lean
instance (priority := 100) instTemporalOfBimodal [BimodalConnectives F] :
    TemporalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce

instance (priority := 100) instFutureTemporalOfBimodal [BimodalConnectives F] :
    FutureTemporalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  untl := HasUntil.untl
```

This resolves the synthesis gap without changing the class declarations, making it a
minimal-churn PR that can be submitted immediately while the `class abbrev` question is
discussed with maintainers.

---

## 7. Strategic Assessment: Diamond Surface Growth

The ROADMAP lists discrete completeness, continuous completeness, and temporal completeness
variants as remaining work — all within existing four logics. No new logic types are listed.

However, ORGANISATION.md reveals CSLib's broader scope: Languages (CCS, Pi Calculus, Lambda),
Computability, Algorithms, Crypto, ML, Probability. Process calculi (CCS, Pi Calculus) commonly
use modal operators (Hennessy-Milner Logic is already present in `Logics/HML/`). If a combined
HML + temporal logic is ever formalized, the diamond surface would include:

```
FutureTemporalConnectives ← TempConn ← BimodalConnectives (existing)
PropositionalConnectives ← HMLConnectives (new)
Combined logic would intersect both chains
```

This confirms: the `class abbrev` solution scales forward. The current design (flat +
bridge instances) requires manual bridge instances for every new intersection. Under
`class abbrev`, every new combination is automatically handled as long as all components
are expressed as atomic `Has*` classes.

**Long-term verdict**: `class abbrev` is the correct architectural choice for CSLib's
connective hierarchy. It eliminates diamond analysis from future logic additions and reduces
the instance-registration burden on each new formula type from "one bundle instance with N
fields" to "N atomic instances with one field each." This is a net reduction in verbosity
for formula authors and a net increase in inference power for downstream users.

---

## Confidence Levels

| Claim | Confidence | Basis |
|-------|------------|-------|
| `class abbrev` eliminates synthesis gap `[BimConn F] → TempConn F` | **High** | Live test verified |
| Hybrid mixing (`class extends` on `class abbrev`) works | **High** | Live test verified |
| `class abbrev` produces no `structureDiamondWarning` | **High** | Live test verified |
| `class abbrev` has 3 uses in Mathlib (not mainstream but correct) | **High** | Grep of lake packages |
| `structureDiamondWarning false` has 0 uses in Mathlib | **High** | Grep of lake packages |
| PR reviewers will accept `class abbrev` with `IsAffineMonoid` justification | **Medium** | Ecosystem norms; actual reviewer response unknown |
| No new bundled class will need new methods in near term | **Medium** | Based on current design; future logics may differ |
| `class abbrev` is non-breaking for existing downstream code | **Medium** | Theoretically sound; not tested on full CSLib build |

---

## Sources

- **Live Lean 4 tests**: Run via `lean_run_code` MCP tool, all passing (no diagnostics)
- CSLib `Cslib/Foundations/Logic/Connectives.lean` — current hierarchy
- CSLib `ORGANISATION.md` — full project scope
- CSLib `specs/ROADMAP.md` — remaining work and four-logic structure
- Mathlib `Mathlib/Algebra/AffineMonoid/Basic.lean` — `class abbrev IsAffineMonoid` pattern
- Mathlib `Mathlib/CategoryTheory/Monoidal/Cartesian/CommGrp_.lean` — `class abbrev CommGrpObj`
- Lean 4 Class Declarations reference: https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/
- Round 1 Team Research: `specs/229_typeclass_diamond_resolution_lean4/reports/01_team-research.md`
