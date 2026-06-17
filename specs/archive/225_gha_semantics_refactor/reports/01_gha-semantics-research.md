# Research Report: GHA Algebraic Semantics with Primitive Bot

**Task**: 225 -- Implement GHA algebraic semantics with primitive bot on main
**Session**: sess_1750122000_orchestrate225
**Date**: 2026-06-16

## 1. Current State Analysis

### 1.1 Existing Semantics Files

The propositional semantics lives in `Cslib/Logics/Propositional/Semantics/`:

| File | Contents | Key Definitions |
|------|----------|----------------|
| `Basic.lean` | Prop-valued bivalent semantics | `Valuation`, `Evaluate : Valuation Atom -> Proposition Atom -> Prop`, `Tautology` |
| `Bool.lean` | Computable Bool evaluation (imports Basic) | `BoolValuation`, `BoolEvaluate`, `BoolEvaluate_eq_iff` bridge |
| `Kripke.lean` | Intuitionistic/minimal Kripke semantics | `KripkeModel`, `IForces`, `IValid`, `MValid`, `iforces_persistence` |
| `SemanticConsequence.lean` | Set-based derivability + semantic consequence | `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails` |

### 1.2 Existing Soundness Proofs

| File | Axiom Set | Target Semantics | Key Theorem |
|------|-----------|-------------------|-------------|
| `Soundness.lean` | `PropositionalAxiom` (10 axioms incl. peirce) | `Evaluate` (Prop-valued bivalent) | `prop_soundness_tautology` |
| `IntSoundness.lean` | `IntPropAxiom` (9 axioms incl. efq) | `IForces` (Kripke, bot_forces = False) | `int_soundness_derivable` |
| `MinSoundness.lean` | `MinPropAxiom` (8 axioms) | `IForces` (Kripke, arbitrary bot_forces) | `min_soundness_derivable` |

### 1.3 Axiom Hierarchies

The three axiom sets form a strict subsumption chain:

- **MinPropAxiom** (8 constructors): implyK, implyS, andI, andE1, andE2, orI1, orI2, orE
- **IntPropAxiom** (9 constructors): MinPropAxiom + efq
- **PropositionalAxiom** (10 constructors): IntPropAxiom + peirce

Subsumption theorems: `MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`

### 1.4 `PL.Proposition` Type

Five primitive constructors: `atom x | bot | imp a b | and a b | or a b`

Derived connectives: `neg := (.imp . .bot)`, `top := .imp .bot .bot`, `iff A B := (A.imp B).and (B.imp A)`

### 1.5 Downstream Dependencies (Must Not Break)

Files importing `Semantics.Basic` from outside the Semantics directory:

| File | Uses |
|------|------|
| `Modal/FromPropositional.lean` | `PL.Evaluate`, `PL.Tautology` |
| `Temporal/ConservativeExtension.lean` | `PL.Evaluate`, `PL.Tautology` |
| `Bimodal/.../PropositionalConservativity.lean` | `PL.Evaluate` (via transitive import) |
| `Bimodal/.../CountermodelExtraction.lean` | Uses "Evaluate" in a comment context only |
| `Propositional/Metalogic/Soundness.lean` | `Evaluate`, `Valuation` |
| `Propositional/Metalogic/StrongCompleteness.lean` | `Evaluate`, `canonicalValuation` |

**Critical constraint**: All downstream files reference `PL.Evaluate` and `PL.Valuation` by name. These definitions must remain available at the same fully-qualified names (or be re-exported from their current module paths). The Kripke semantics (`IForces`, `IValid`, `MValid`) must remain completely untouched.

### 1.6 PR #648 Context

PR #648 ("five-primitive formula type with primitive bot") explicitly deferred semantics:

> "Semantics (`Basic.lean`, `Bool.lean`) deferred to a follow-up PR per thomaskwaring's request. The question of `Prop` vs `Bool` vs `GeneralizedHeytingAlgebra` for evaluation (raised by thomaskwaring and ctchou) will be addressed there."

This task IS that follow-up. The PR #648 file structure guidance is:
- No `Semantics/Basic.lean` was included in PR #648 (it was deferred)
- The current main branch already has `Basic.lean` and `Bool.lean`
- The task asks to "combine Basic.lean into Bool.lean" to consolidate

## 2. Mathlib API for Algebraic Semantics

### 2.1 Class Hierarchy

```
GeneralizedHeytingAlgebra (GHA)
  extends: Lattice, OrderTop, HImp
  axiom:   le_himp_iff (a b c) : a <= b ⇨ c <-> a ⊓ b <= c
  key:     Has ⊤, ⊓, ⊔, ⇨  (NO ⊥)

HeytingAlgebra (HA)
  extends: GeneralizedHeytingAlgebra, OrderBot, Compl
  axiom:   himp_bot (a) : a ⇨ ⊥ = aᶜ
  key:     Adds ⊥ and complement (ᶜ)

BooleanAlgebra (BA)
  extends: DistribLattice, Compl, SDiff, HImp, Top, Bot
  axioms:  inf_compl_le_bot, top_le_sup_compl, sdiff_eq, himp_eq
  key:     himp_eq : x ⇨ y = y ⊔ xᶜ  (material conditional)
  key:     compl_compl : xᶜᶜ = x  (double negation elimination)
```

Note: `BooleanAlgebra` does NOT extend `HeytingAlgebra` directly, but there is an instance
`BooleanAlgebra.toHeytingAlgebra` (see below). The `Prop` type has instances for all three:
- `Prop.instHeytingAlgebra` (in `Mathlib/Order/Heyting/Basic.lean`)
- `Prop.instBooleanAlgebra` (in `Mathlib/Order/BooleanAlgebra/Defs.lean`)

### 2.2 Key Lemmas for Axiom Soundness

#### GHA-level (for MinPropAxiom: implyK, implyS, and/or axioms)

| Axiom | GHA Lemma | Type |
|-------|-----------|------|
| implyK: `phi -> (psi -> phi)` | `le_himp` | `a <= b ⇨ a` |
| implyS: `(p->(q->r))->((p->q)->(p->r))` | `himp_le_himp_himp_himp` | `b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c` |
| andI: `phi -> (psi -> phi /\ psi)` | `le_himp_iff` + `le_inf` | via adjunction |
| andE1: `phi /\ psi -> phi` | `inf_le_left` | `a ⊓ b <= a` |
| andE2: `phi /\ psi -> psi` | `inf_le_right` | `a ⊓ b <= b` |
| orI1: `phi -> phi \/ psi` | `le_sup_left` | `a <= a ⊔ b` |
| orI2: `psi -> phi \/ psi` | `le_sup_right` | `b <= a ⊔ b` |
| orE: `(p->r)->((q->r)->((p\/q)->r))` | `sup_le` + adjunction | via `le_himp_iff` |

**Note on implyS**: The GHA lemma `himp_le_himp_himp_himp` states `b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c`, which is `(q->r) -> ((p->q) -> (p->r))`. The actual implyS axiom is `(p->(q->r)) -> ((p->q) -> (p->r))`. These differ! We need to prove:

```
(a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤
```

This follows from `himp_himp` (which gives `a ⇨ b ⇨ c = a ⊓ b ⇨ c`) combined with `himp_le_himp_himp_himp` and `le_himp_iff`. The key chain:
1. `himp_himp : a ⇨ b ⇨ c = a ⊓ b ⇨ c` (currying)
2. `himp_le_himp_himp_himp : b ⇨ c <= (a ⇨ b) ⇨ a ⇨ c` (applied to `a ⊓ b ⇨ c`)
3. Combined with step 1, we get `(a ⇨ b ⇨ c) <= (a ⇨ b) ⇨ (a ⇨ c)`

Actually, rewriting: using `himp_himp` on the LHS of implyS gives `(a ⊓ b ⇨ c) ⇨ ((a ⇨ b) ⇨ (a ⇨ c))`. But this is slightly different from `himp_le_himp_himp_himp`. Let me be more precise.

We want to show: `⊤ <= (a ⇨ (b ⇨ c)) ⇨ ((a ⇨ b) ⇨ (a ⇨ c))`.

By `le_himp_iff`, this is: `⊤ ⊓ (a ⇨ b ⇨ c) <= (a ⇨ b) ⇨ (a ⇨ c)`, i.e., `(a ⇨ b ⇨ c) <= (a ⇨ b) ⇨ (a ⇨ c)`.

Using `himp_himp` on the LHS: `(a ⊓ b ⇨ c) <= (a ⇨ b) ⇨ (a ⇨ c)`.

By `le_himp_iff` twice: `(a ⊓ b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= c`.

We have `(a ⊓ b ⇨ c) ⊓ (a ⇨ b) ⊓ a`. By `himp_inf_le` applied to `a ⇨ b` and `a`: `(a ⇨ b) ⊓ a <= b`. So `(a ⊓ b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= (a ⊓ b ⇨ c) ⊓ (a ⊓ ((a ⇨ b) ⊓ a))`. This gets complicated. The simplest proof will use `simp [le_himp_iff, himp_himp, inf_assoc]` or step-by-step with `le_himp_iff` and lattice lemmas.

In practice, we can likely prove this by `simp [himp_eq_top_iff, le_himp_iff, himp_himp, inf_assoc]` or via `himp_inf_himp_inf_le` (which states `(b ⇨ c) ⊓ (a ⇨ b) ⊓ a <= c`).

#### HA-level (additional for IntPropAxiom: efq)

| Axiom | HA Lemma | Type |
|-------|----------|------|
| efq: `bot -> phi` | `bot_himp` | `⊥ ⇨ a = ⊤` (in HA, since HA has ⊥) |

This is direct: `bot_himp : ⊥ ⇨ a = ⊤`.

#### BA-level (additional for PropositionalAxiom: peirce)

| Axiom | BA Lemma | Proof Strategy |
|-------|----------|----------------|
| peirce: `((phi -> psi) -> phi) -> phi` | No direct lemma | Use `himp_eq` to reduce to lattice |

For Peirce's law, we need `((a ⇨ b) ⇨ a) ⇨ a = ⊤` in a BooleanAlgebra.

Using `himp_eq : x ⇨ y = y ⊔ xᶜ` (in BA):
- `a ⇨ b = b ⊔ aᶜ`
- `(a ⇨ b) ⇨ a = a ⊔ (b ⊔ aᶜ)ᶜ = a ⊔ (bᶜ ⊓ a)` (by compl_sup, compl_compl)
- `((a ⇨ b) ⇨ a) ⇨ a = a ⊔ (a ⊔ (bᶜ ⊓ a))ᶜ`

This is getting complex. The cleaner approach: use `himp_eq_top_iff` to reduce to `((a ⇨ b) ⇨ a) <= a`, then use `le_himp_iff` to get `((a ⇨ b) ⇨ a) ⊓ (a ⇨ b) <= a`, and then use `himp_inf_self` or direct BA reasoning. Alternatively, use `simp [himp_eq]` which should work in BA since `himp_eq` reduces everything to `⊔` and `ᶜ`.

**Recommended proof strategy for Peirce**: Use `simp only [himp_eq_top_iff, le_himp_iff]` and then BA-specific reasoning with `simp [himp_eq, compl_sup, compl_compl, inf_sup_left, sup_compl_eq_top]`.

### 2.3 Design Decision: `bot_val` Parameter

The task asks for `Evaluate [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H) : PL.Proposition Atom -> H`.

The `bot_val` parameter is necessary because **GHA has no bottom element** (`GeneralizedHeytingAlgebra` only extends `OrderTop`, not `OrderBot`). When we specialize:
- **GHA**: `bot_val` is an arbitrary element (minimal logic -- bot means anything)
- **HA**: `bot_val = ⊥` (intuitionistic logic -- bot means the actual bottom)
- **BA**: `bot_val = ⊥` (classical logic -- same)

This mirrors the Kripke semantics design where `IForces` takes a `bot_forces` parameter.

## 3. Proposed Architecture

### 3.1 New File: `Semantics/Algebra.lean`

```lean
import Cslib.Logics.Propositional.Defs
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.BooleanAlgebra.Basic

-- Generic algebraic evaluation
def AlgEvaluate [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H) :
    PL.Proposition Atom -> H
  | .atom x => v x
  | .bot => bot_val
  | .imp a b => AlgEvaluate v bot_val a ⇨ AlgEvaluate v bot_val b
  | .and a b => AlgEvaluate v bot_val a ⊓ AlgEvaluate v bot_val b
  | .or a b => AlgEvaluate v bot_val a ⊔ AlgEvaluate v bot_val b

-- Validity definitions
def GHAValid (phi) := forall (H) [GHA H] (v : Atom -> H) (bot_val : H),
    AlgEvaluate v bot_val phi = top

def HAValid (phi) := forall (H) [HA H] (v : Atom -> H),
    AlgEvaluate v bot H phi = top

def BAValid (phi) := forall (H) [BA H] (v : Atom -> H),
    AlgEvaluate v bot H phi = top
```

### 3.2 New File: `Semantics/Algebra/Soundness.lean`

Soundness theorems proving each axiom set is valid under the corresponding algebra:

- `min_alg_axiom_sound : MinPropAxiom phi -> GHAValid phi` (8 cases, all GHA lemmas)
- `int_alg_axiom_sound : IntPropAxiom phi -> HAValid phi` (9 cases = 8 GHA + efq via `bot_himp`)
- `prop_alg_axiom_sound : PropositionalAxiom phi -> BAValid phi` (10 cases = 9 HA + peirce via BA)

Plus derivation-level soundness theorems:
- `min_alg_soundness` / `int_alg_soundness` / `prop_alg_soundness`

### 3.3 Consolidation: Combine Basic.lean into Bool.lean

Move the `Prop`-valued `Evaluate`, `Valuation`, `Tautology` from `Basic.lean` into `Bool.lean`, making `Bool.lean` the single file for both `Prop`-valued and `Bool`-valued evaluation. The file should import only `Defs.lean` (no Mathlib algebra imports).

**Import chain after consolidation**:
- `Bool.lean` imports `Defs.lean` (contains Valuation, Evaluate, BoolEvaluate, bridge lemmas)
- `Algebra.lean` imports `Defs.lean` + Mathlib GHA/HA/BA (contains AlgEvaluate, validity defs)
- `Algebra/Soundness.lean` imports `Algebra.lean` + `Axioms.lean` + `Derivation.lean`

**Re-export strategy**: `Bool.lean` should `public import Defs.lean` so all downstream files that currently `import Semantics.Basic` can switch to `import Semantics.Bool` with no other changes.

### 3.4 Bridge Lemmas

The task asks for bridge lemmas connecting existing evaluators to the generic `AlgEvaluate`:

1. **prop_evaluate_eq**: `Evaluate v phi <-> (AlgEvaluate (fun a => v a) False phi)` -- connecting Prop-valued Evaluate to AlgEvaluate over `Prop` (which is a HeytingAlgebra)

   This works because `Prop.instHeytingAlgebra` defines `himp := (. -> .)`, and `Evaluate v (.imp a b) = Evaluate v a -> Evaluate v b` which equals `(Evaluate v a) ⇨ (Evaluate v b)` in the Prop HA.

2. **bool_evaluate_eq**: `BoolEvaluate v phi = AlgEvaluate (fun a => v a) false phi` -- connecting Bool-valued BoolEvaluate to AlgEvaluate over `Bool` (which is a BooleanAlgebra)

   This works because `Bool.instBooleanAlgebra` exists and `himp` on `Bool` is `!a || b`.

3. **iforces_eq**: Bridge connecting `IForces` to `AlgEvaluate` over an appropriate upward-closed set algebra.

   **WARNING**: This bridge is significantly more complex. Kripke forcing interprets implication as universal quantification over successors (`forall w' >= w, ...`), which corresponds to the GHA structure of upward-closed sets ordered by inclusion. The GHA of upsets of a preorder IS a Heyting algebra, with `A ⇨ B = {w | forall w' >= w, w' in A -> w' in B}`. However, this requires:
   - Defining the upset algebra instance
   - Proving `AlgEvaluate` over this algebra equals `IForces`

   This is a substantial proof that may deserve its own file or could be deferred. The task description mentions it but the implementation complexity is high.

### 3.5 Naming Convention: `Evaluate` vs `AlgEvaluate`

The task says "generic `Evaluate`" for the new function, but reusing the name `Evaluate` would conflict with the existing `Prop`-valued `Evaluate`. Options:

**Option A**: Name the new function `AlgEvaluate` (or `Algebra.Evaluate`)
- Pro: No name collision, clear semantic distinction
- Con: Doesn't match the task description literally

**Option B**: Namespace the new function as `Algebra.Evaluate` (using the `Semantics.Algebra` namespace)
- Pro: Clean namespace separation, matches file location
- Con: Fully qualified name `Cslib.Logic.PL.Algebra.Evaluate` is long

**Recommendation**: Use `AlgEvaluate` as the function name in the `Cslib.Logic.PL` namespace, paralleling the existing `BoolEvaluate` naming convention. This is consistent with the existing codebase style.

## 4. Key Risk Analysis

### 4.1 Peirce's Law in BooleanAlgebra (Medium Risk)

No direct `peirce` lemma exists for `BooleanAlgebra` in Mathlib. The proof requires using `himp_eq : x ⇨ y = y ⊔ xᶜ` to unfold all implications to `⊔` and `ᶜ`, then using BA lattice reasoning. This is doable but may require 5-15 lines of careful proof.

**Mitigation**: Use `simp [himp_eq_top_iff, le_himp_iff]` followed by BA-specific `simp` lemmas. Test with `lean_multi_attempt` before committing.

### 4.2 ImplyS in GHA (Low-Medium Risk)

The implyS axiom requires showing `(a ⇨ b ⇨ c) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤`. The existing lemmas (`himp_himp`, `himp_le_himp_himp_himp`) provide the ingredients but assembly is needed. The key step is:

```lean
-- himp_himp rewrites a ⇨ b ⇨ c to (a ⊓ b) ⇨ c
-- himp_le_himp_himp_himp gives (a ⊓ b) ⇨ c ≤ (a ⇨ (a ⊓ b)) ⇨ (a ⇨ c)
-- We need (a ⇨ b ⇨ c) ≤ (a ⇨ b) ⇨ (a ⇨ c)
```

Actually, looking more carefully at `himp_le_himp_himp_himp`: it states `b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c`. If we set `b := a ⊓ b₀` and use `himp_himp : a ⇨ b₀ ⇨ c = (a ⊓ b₀) ⇨ c`, we get:

`(a ⊓ b₀) ⇨ c ≤ (a ⇨ (a ⊓ b₀)) ⇨ (a ⇨ c)`

But we need `(a ⊓ b₀) ⇨ c ≤ (a ⇨ b₀) ⇨ (a ⇨ c)`. Since `a ⊓ b₀ ≤ b₀` and `a ⊓ (a ⇨ b₀) ≤ a ⊓ b₀` (via `inf_himp`), this should work via monotonicity.

A cleaner approach: directly unfold with `le_himp_iff` and use `inf_assoc` and `himp_inf_self`:

```lean
-- Want: (a ⇨ b ⇨ c) ⇨ ((a ⇨ b) ⇨ (a ⇨ c)) = ⊤
-- Suffices: a ⇨ b ⇨ c ≤ (a ⇨ b) ⇨ (a ⇨ c)   (by himp_eq_top_iff)
-- By le_himp_iff twice: (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c
-- LHS: by himp_himp, a ⇨ b ⇨ c = (a ⊓ b) ⇨ c
-- So: ((a ⊓ b) ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c
-- Using himp_inf_self: (a ⇨ b) ⊓ a = b ⊓ a
-- So: ((a ⊓ b) ⇨ c) ⊓ (b ⊓ a) ≤ c
-- = ((a ⊓ b) ⇨ c) ⊓ (a ⊓ b) ≤ c   (by inf_comm)
-- This is himp_inf_le!
```

This works cleanly. The proof is ~5 lines using `himp_eq_top_iff`, `le_himp_iff`, `himp_himp`, `himp_inf_self`, `himp_inf_le`.

### 4.3 OrE in GHA (Low Risk)

The orE axiom `(p->r) -> ((q->r) -> ((p\/q)->r))` translates to showing:

`(a ⇨ c) ⇨ ((b ⇨ c) ⇨ ((a ⊔ b) ⇨ c)) = ⊤`

Using `le_himp_iff` repeatedly, this reduces to `(a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c`. This follows from `sup_le` and the adjunction: `a ⊔ b ≤ c` when `a ≤ c` and `b ≤ c`. More precisely, distribute the `⊓` over `⊔` and use `himp_inf_le` on each branch. Available via `himp_inf_distrib` or `sup_himp_distrib`.

Actually, there's a cleaner approach: use `sup_himp_distrib` if it exists. Let me check -- no, the relevant direction is: `(a ⇨ c) ⊓ (b ⇨ c) ≤ (a ⊔ b) ⇨ c`. In GHA with a distributive lattice structure, this should hold via adjunction.

**Alternative**: use `le_himp_iff` to get `(a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c`, then use lattice distribution (GHA extends Lattice, not necessarily DistribLattice -- but `GeneralizedHeytingAlgebra` implies distributivity by `GeneralizedHeytingAlgebra.toDistribLattice`).

### 4.4 Bridge Lemma for IForces (High Risk -- May Defer)

The `iforces_eq` bridge connecting Kripke `IForces` to algebraic evaluation over the upset Heyting algebra is mathematically deep (this is essentially the Stone/Esakia duality correspondence). It requires:
1. Defining the type of upsets as a Heyting algebra
2. Proving the evaluation correspondence

**Recommendation**: Implement `prop_evaluate_eq` and `bool_evaluate_eq` in the initial task. Defer `iforces_eq` to a separate task or mark it as optional stretch goal. The task description lists it but the other three items are already substantial.

### 4.5 Basic.lean -> Bool.lean Consolidation (Low Risk)

This is mechanical: move the `Valuation`, `Evaluate`, `Tautology` definitions and simp lemmas from `Basic.lean` to the top of `Bool.lean`. Update all import paths. The only files importing `Semantics.Basic` are:
- `Bool.lean` (will absorb content)
- `SemanticConsequence.lean` (change to import Bool)
- `Soundness.lean` (change to import Bool)
- `StrongCompleteness.lean` (transitively via SemanticConsequence)
- `Modal/FromPropositional.lean` (change to import Bool)
- `Temporal/ConservativeExtension.lean` (change to import Bool)

All downstream modal/temporal/bimodal files import `Semantics.Basic` only transitively through these files, so updating the direct importers suffices. The `Kripke.lean` file does NOT import `Basic.lean` (it independently imports `Defs.lean`), so it is unaffected.

## 5. Implementation Plan Skeleton

### Phase 1: Consolidate Basic.lean into Bool.lean
- Move `Valuation`, `Evaluate`, simp lemmas, `Tautology` from Basic.lean to top of Bool.lean
- Update all imports from `Semantics.Basic` to `Semantics.Bool`
- Remove Basic.lean
- Update `Cslib.lean` barrel import
- Verify: `lake build`

### Phase 2: Create Semantics/Algebra.lean
- Define `AlgEvaluate` with simp lemmas
- Define `GHAValid`, `HAValid`, `BAValid`
- Add to `Cslib.lean`
- Verify: `lake build Cslib.Logics.Propositional.Semantics.Algebra`

### Phase 3: Create Semantics/Algebra/Soundness.lean
- Prove `min_alg_axiom_sound` (8 GHA cases)
- Prove `int_alg_axiom_sound` (9 cases = delegate 8 to min + efq)
- Prove `prop_alg_axiom_sound` (10 cases = delegate 9 to int + peirce)
- Prove derivation-level soundness
- Add to `Cslib.lean`
- Verify: `lake build`

### Phase 4: Bridge Lemmas
- Prove `prop_evaluate_eq` (Evaluate <-> AlgEvaluate over Prop)
- Prove `bool_evaluate_eq` (BoolEvaluate = AlgEvaluate over Bool)
- Optionally prove `iforces_eq` if time permits
- These can live in `Algebra.lean` or a dedicated bridge file

### Phase 5: CI Verification
- `lake build` (full)
- `lake exe checkInitImports`
- `lake exe lint-style`
- `lake test`
- `lake exe mk_all --module`
- `lake shake --add-public --keep-implied --keep-prefix`

## 6. Tactic Survey Results

For the key proof obligations:

| Proof Goal | Recommended Tactic Approach |
|------------|---------------------------|
| implyK (`a <= b ⇨ a`) | Direct: `exact le_himp` |
| implyS | `simp only [himp_eq_top_iff]; rw [himp_himp]; exact ...` using `himp_inf_himp_inf_le` |
| andI | `simp only [himp_eq_top_iff, le_himp_iff]; exact le_inf ...` |
| andE1/andE2 | `simp only [himp_eq_top_iff]; exact inf_le_left / inf_le_right` |
| orI1/orI2 | `simp only [himp_eq_top_iff]; exact le_sup_left / le_sup_right` |
| orE | `simp only [himp_eq_top_iff, le_himp_iff]` + distributivity |
| efq (HA) | `simp only [himp_eq_top_iff]; exact bot_le` or `exact bot_himp` |
| peirce (BA) | `simp only [himp_eq, compl_sup, compl_compl]` + BA lattice |

## 7. Reuse Check Results

| Check | Result |
|-------|--------|
| CSLib Foundations: existing GHA/HA/BA algebraic semantics | **None found** |
| CSLib Logics: existing `AlgEvaluate` or similar | **None found** |
| Bimodal algebraic: `LindenbaumAlg` BooleanAlgebra | Exists but different purpose (Lindenbaum algebra, not semantics) |
| Mathlib: propositional formula GHA evaluation | **None found** (Mathlib has no propositional logic library) |

This is genuinely new work for CSLib.

## 8. Lint Prevention Notes

All new declarations need:
- Docstrings (docBlame)
- Prop-valued declarations must use `lemma`/`theorem` (defLemma)
- lowerCamelCase names (no underscores except in existing conventions like `BoolEvaluate_eq_iff`)
- `import Cslib.Init` in all new files
- `@[simp]` tags on all `AlgEvaluate` case lemmas (with simpNF verification)
