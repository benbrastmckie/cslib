# Research Report: Hilbert-Primary Algebraic Completeness (Task 283)

## 1. Current Completeness Architecture

### 1.1 ND-Level Completeness (Completeness.lean)

The existing completeness theorems in `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` are all stated in terms of the **ND system** (`DerivableIn T`):

| Theorem | Type Signature | Algebra Class |
|---------|---------------|---------------|
| `Theory.alg_complete` | `DerivableIn T A <-> forall {H} [GHA H] (v) (bot_val), AlgTValid T v bot_val -> AlgEvaluate v bot_val A = top` | GHA (with theory T) |
| `MPL.alg_complete` | `DerivableIn (empty : Theory Atom) A <-> forall {H} [GHA H] (v) (bot_val), AlgEvaluate v bot_val A = top` | GHA (empty theory) |
| `IPL.alg_complete` | `DerivableIn (IPL : Theory Atom) A <-> forall {H} [HA H] (v), AlgEvaluate v (bot : H) A = top` | HA |
| `alg_complete_classical` | `DerivableIn T A <-> forall {H} [BA H] (v), (forall B in T, AlgEvaluate v bot B = top) -> AlgEvaluate v bot A = top` | BA (with [IsIntuitionistic T] [IsClassical T]) |

All of these use `DerivableIn T` (the ND system's derivability predicate for `Theory.Derivation`).

### 1.2 Hilbert-Level Completeness (HilbertCompleteness.lean)

The existing `HilbertCompleteness.lean` already provides the Hilbert biconditionals:

| Theorem | Type Signature |
|---------|---------------|
| `MPL.hilbert_alg_complete` | `Derivable MinPropAxiom phi <-> GHAValid phi` |
| `IPL.hilbert_alg_complete` | `Derivable IntPropAxiom phi <-> HAValid phi` |
| `CPL.hilbert_alg_complete` | `Derivable PropositionalAxiom phi <-> BAValid phi` |

**Crucially, these already exist.** However, the current completeness direction (right-to-left) routes through the ND system:

- **MPL**: `GHAValid phi -> DerivableIn (empty) phi` (via `MPL.alg_complete`) -> theory monotonicity -> `hilbert_iff_nd_min`
- **IPL**: `HAValid phi -> DerivableIn IPL phi` (via `IPL.alg_complete`) -> theory monotonicity -> `hilbert_iff_nd_int`
- **CPL**: `BAValid phi -> Tautology phi` (via `Bool` instantiation) -> `prop_completeness_iff_tautology`

### 1.3 What the Task Asks For

The task description says:
> "Replace MPL.alg_complete, IPL.alg_complete, and Theory.alg_complete with versions stated for Derivable/SetDerivable (Hilbert) rather than DerivableIn (ND)."

This means the **primary completeness theorems in Completeness.lean** should be restated with `Derivable Axioms phi` (Hilbert) on the left-hand side, and the ND versions should become corollaries via `hilbert_iff_nd`.

## 2. Existing Soundness Theorems (Already Hilbert-Primary)

The soundness direction is already Hilbert-primary in `Soundness.lean`:

| Theorem | Type | Status |
|---------|------|--------|
| `min_alg_soundness_derivable` | `Derivable MinPropAxiom phi -> GHAValid phi` | Already Hilbert-primary |
| `int_alg_soundness_derivable` | `Derivable IntPropAxiom phi -> HAValid phi` | Already Hilbert-primary |
| `prop_alg_soundness_derivable` | `Derivable PropositionalAxiom phi -> BAValid phi` | Already Hilbert-primary |

These can be kept as-is.

## 3. Hilbert Lindenbaum Algebra (Task 282)

`HilbertLindenbaum.lean` provides:

- `HilbertLindenbaumAlgebra Axioms` -- quotient of `Proposition Atom` by `HilbertEquiv Axioms`
- `hilbertLindenbaumMk A` -- quotient map
- `hilbertLindenbaumGHA` -- `GeneralizedHeytingAlgebra` instance for any `[MinimalAxioms Axioms]`
- `hilbertLindenbaumHeytingAlgebra h_EFQ` -- `HeytingAlgebra` instance (requires EFQ)
- `hilbertLindenbaumBooleanAlgebra h_EFQ h_Peirce` -- `BooleanAlgebra` instance (requires EFQ + Peirce)
- Concrete instances: `hilbertLindenbaumIntHA` for `IntPropAxiom`, `hilbertLindenbaumClHA`/`hilbertLindenbaumClBA` for `PropositionalAxiom`

Key simp lemmas:
- `hilbertLindenbaumMk_le_mk`: `[A] <= [B] <-> Deriv Axioms [A] B`
- `hilbertLindenbaumMk_sup`: `[A or B] = [A] sup [B]`
- `hilbertLindenbaumMk_inf`: `[A and B] = [A] inf [B]`
- `hilbertLindenbaumMk_himp`: `[A imp B] = [A] himp [B]`
- `hilbertLindenbaumTop`: `top = [bot imp bot]`

**Missing but critical**: There is no `hilbertLindenbaumMk_eq_top_iff` lemma yet.

## 4. Gap Analysis

### 4.1 Missing: `hilbertLindenbaumMk_eq_top_iff`

This is the cornerstone lemma analogous to `lindenbaumMk_eq_top_iff` in the ND Lindenbaum:

```lean
-- Existing ND version (Completeness.lean line 197):
theorem lindenbaumMk_eq_top_iff {A : Proposition Atom} :
    lindenbaumMk T A = top <-> DerivableIn T A

-- Needed Hilbert version:
theorem hilbertLindenbaumMk_eq_top_iff
    {Axioms : Proposition Atom -> Prop} [MinimalAxioms Axioms]
    {A : Proposition Atom} :
    hilbertLindenbaumMk (Axioms := Axioms) A = top <-> Derivable Axioms A
```

**Proof sketch**:
- Top in the Hilbert Lindenbaum algebra is `[bot imp bot]` (by `hilbertLindenbaumTop`).
- `[A] = [bot imp bot]` iff `HilbertEquiv Axioms A (bot imp bot)` iff `Deriv Axioms [A] (bot imp bot)` and `Deriv Axioms [bot imp bot] A`.
- Forward: If `[A] = top`, then by `Quotient.exact`: `Deriv Axioms [bot imp bot] A`. From `Deriv Axioms [bot imp bot] A`, we need to derive `Deriv Axioms [] A` (i.e., `Derivable Axioms A`). This requires cutting with `Deriv Axioms [] (bot imp bot)` (which is the identity combinator on `bot`).
- Backward: If `Derivable Axioms A` (i.e., `Deriv Axioms [] A`), then `Deriv Axioms [bot imp bot] A` by weakening, and `Deriv Axioms [A] (bot imp bot)` by the `hilbertImpIDeriv` (deduction theorem for `bot -> bot`). So `HilbertEquiv Axioms A (bot imp bot)` and thus `[A] = top`.

This proof is entirely internal to the Hilbert system; no ND bridge needed.

### 4.2 Missing: Hilbert-Primary Canonical Valuation and Truth Lemma

For the completeness direction, we need an analogue of the ND canonical valuation/truth lemma, but using the Hilbert Lindenbaum algebra directly.

**Canonical valuation** (for a fixed `Axioms`):
```lean
def Hilbert.canonicalV (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms] :
    Atom -> HilbertLindenbaumAlgebra Axioms :=
  fun x => hilbertLindenbaumMk (.atom x)

def Hilbert.canonicalBotVal (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms] :
    HilbertLindenbaumAlgebra Axioms :=
  hilbertLindenbaumMk .bot
```

**Truth lemma**: `AlgEvaluate (Hilbert.canonicalV Axioms) (Hilbert.canonicalBotVal Axioms) A = hilbertLindenbaumMk A`

This follows by the same structural induction on `A` as `Theory.canonicalV_spec`, using the Hilbert simp lemmas (`hilbertLindenbaumMk_himp`, `hilbertLindenbaumMk_inf`, `hilbertLindenbaumMk_sup`).

### 4.3 Architecture Decision: Modify Completeness.lean vs. New File

Two options:

**Option A: Modify Completeness.lean in place**
- Replace `Theory.alg_complete`, `MPL.alg_complete`, `IPL.alg_complete` with Hilbert-primary versions
- Add ND versions as corollaries
- Pro: Single source of truth
- Con: Potentially breaks downstream consumers (Conservative.lean, Glivenko.lean, KripkeBridge.lean may depend on the ND versions)

**Option B: New file HilbertCompleteness.lean (already exists)**
- The existing `HilbertCompleteness.lean` already contains `MPL.hilbert_alg_complete`, `IPL.hilbert_alg_complete`, `CPL.hilbert_alg_complete`
- Refactor these to use the Hilbert Lindenbaum algebra directly instead of routing through ND
- Keep `Completeness.lean` unchanged
- Pro: No breakage, clean separation
- Con: Duplication of the completeness argument

**Recommended: Option B** -- Refactor `HilbertCompleteness.lean` to use the Hilbert Lindenbaum algebra directly, then derive the ND completeness theorems as corollaries by composing with `hilbert_iff_nd`. This avoids breaking any existing consumers of `Completeness.lean`.

However, re-reading the task description more carefully: "Replace MPL.alg_complete, IPL.alg_complete, and Theory.alg_complete with versions stated for Derivable/SetDerivable (Hilbert)." This suggests Option A -- modifying the primary theorems. The downstream impact must be analyzed.

### 4.4 Downstream Impact Analysis

Files that import/use the ND completeness theorems:

| File | Uses | Impact |
|------|------|--------|
| `HilbertCompleteness.lean` | `MPL.alg_complete`, `IPL.alg_complete` (completeness direction) | Would use Hilbert versions directly; simplifies |
| `Conservative.lean` | `MPL.alg_complete`, `IPL.alg_complete` (via evaluation pipeline) | Needs checking |
| `Glivenko.lean` | May use completeness | Needs checking |
| `KripkeBridge.lean` | May use completeness | Needs checking |

Let me check specifics:

**Conservative.lean** (lines 1-50 already read): Uses `Completeness` import but does not reference `alg_complete` directly in the first 50 lines. Uses `DerivableIn` for its own theorems. Likely minimal impact.

**Summary**: The safest approach is to:
1. Add Hilbert-primary completeness theorems alongside (not replacing) the ND versions
2. Mark the existing ND versions as the "corollary" derivations
3. If the task strictly requires replacement, the ND versions become `theorem` -> `corollary` with a proof via `hilbert_iff_nd`

### 4.5 Theory.alg_complete -- The General Case

The existing `Theory.alg_complete` is parameterized over an ND theory `T : Theory Atom` (a `Set (Proposition Atom)`). The Hilbert system uses `Axioms : Proposition Atom -> Prop`. The Hilbert-primary version would be:

```lean
theorem Hilbert.alg_complete
    {Axioms : Proposition Atom -> Prop} [MinimalAxioms Axioms]
    {A : Proposition Atom} :
    Derivable Axioms A <->
      forall {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H),
        (forall phi, Axioms phi -> AlgEvaluate v bot_val phi = top) ->
        AlgEvaluate v bot_val A = top
```

This quantifies over "all GHA valuations that model the axioms" on the right, and uses `Derivable Axioms` on the left.

**Soundness direction**: This is exactly `min_alg_soundness` (already proved).

**Completeness direction**: Instantiate at `HilbertLindenbaumAlgebra Axioms` with canonical valuation. The "models axioms" hypothesis is satisfied because for any axiom `phi` with `Axioms phi`, `Deriv Axioms [] phi` (by the axiom rule), so `hilbertLindenbaumMk phi = top` (by `hilbertLindenbaumMk_eq_top_iff`). Then `AlgEvaluate canonicalV canonicalBotVal A = top` gives `hilbertLindenbaumMk A = top` (by truth lemma), which gives `Derivable Axioms A` (by `hilbertLindenbaumMk_eq_top_iff`).

### 4.6 Tier-Specific Versions

**MPL (Minimal)**:
```lean
theorem MPL.hilbert_alg_complete_direct
    {Atom : Type u} [DecidableEq Atom] {phi : Proposition Atom} :
    Derivable MinPropAxiom phi <->
      forall {H : Type u} [GeneralizedHeytingAlgebra H] (v : Atom -> H) (bot_val : H),
        AlgEvaluate v bot_val phi = top
```
No theory hypothesis needed (empty axioms always satisfied).

**IPL (Intuitionistic)**:
```lean
theorem IPL.hilbert_alg_complete_direct
    {Atom : Type u} [DecidableEq Atom] {phi : Proposition Atom} :
    Derivable IntPropAxiom phi <->
      forall {H : Type u} [HeytingAlgebra H] (v : Atom -> H),
        AlgEvaluate v (bot : H) phi = top
```
Uses `HeytingAlgebra` (which has `bot`) and fixes `bot_val = bot`. The completeness direction uses `hilbertLindenbaumIntHA` (the Heyting algebra instance for `HilbertLindenbaumAlgebra IntPropAxiom`).

**CPL (Classical)**:
```lean
theorem CPL.hilbert_alg_complete_direct
    {Atom : Type u} [DecidableEq Atom] {phi : Proposition Atom} :
    Derivable PropositionalAxiom phi <->
      forall {H : Type u} [BooleanAlgebra H] (v : Atom -> H),
        AlgEvaluate v (bot : H) phi = top
```
Uses `BooleanAlgebra` and `hilbertLindenbaumClBA`.

### 4.7 ND Corollaries via Bridge

After proving the Hilbert-primary versions, ND corollaries follow:

```lean
-- For MPL:
theorem MPL.alg_complete' {A : Proposition Atom} :
    DerivableIn (empty : Theory Atom) A <->
      forall {H} [GHA H] (v) (bot_val), AlgEvaluate v bot_val A = top := by
  rw [<- hilbert_iff_nd_min, iff_derivableIn_empty]  -- or via weakTheory
  -- ... bridge logic
```

The exact proof strategy depends on whether we keep the old names or rename.

## 5. Proof Approach Summary

### Phase 1: Add `hilbertLindenbaumMk_eq_top_iff` to HilbertLindenbaum.lean

```lean
theorem hilbertLindenbaumMk_eq_top_iff
    {Axioms : Proposition Atom -> Prop} [inst : MinimalAxioms Axioms]
    {A : Proposition Atom} :
    hilbertLindenbaumMk (Axioms := Axioms) A = top <-> Derivable Axioms A := by
  rw [hilbertLindenbaumTop]
  constructor
  . intro h
    have heq := Quotient.exact h
    -- heq : HilbertEquiv Axioms A (bot.imp bot)
    -- heq.2 : Deriv Axioms [bot.imp bot] A
    have hBotBot : Deriv Axioms [] (bot.imp bot) :=
      -- bot -> bot is derivable via impI (identity)
      <proof using hilbertImpIDeriv and assumption>
    have hCut := hilbertCutSingletonDeriv inst.h_K inst.h_S
      (hilbertWeakeningDeriv hBotBot (fun _ h => nomatch h) |> ...) heq.2
    -- actually: weaken hBotBot from [] to [bot.imp bot] then it's already heq.2's context
    -- The exact proof: Deriv [] (bot -> bot) gives Deriv [bot -> bot] A via cut, then weaken
    sorry -- proof sketch; actual implementation needs care
  . intro h
    obtain ⟨d⟩ := h
    -- Derivable means Deriv [] A
    -- Need [A] = [bot -> bot], i.e., HilbertEquiv Axioms A (bot.imp bot)
    exact Quotient.sound ⟨
      hilbertImpIDeriv inst.h_K inst.h_S (assumption_deriv List.mem_cons_self),
      hilbertWeakeningDeriv ⟨d⟩.some (fun _ h => nomatch h) |> ...⟩
```

The exact proof will need careful handling of `Deriv Axioms [] (bot.imp bot)` (the K-combinator gives `A -> (bot -> A)` so `bot -> (bot -> bot)` is derivable, and `bot -> bot` itself is derivable by the identity combinator I = S K K pattern, or more directly by `hilbertImpIDeriv`).

### Phase 2: Add canonical valuation and truth lemma for Hilbert Lindenbaum

These are straightforward structural definitions/proofs:

```lean
def Hilbert.canonicalV (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms] :
    Atom -> HilbertLindenbaumAlgebra Axioms :=
  fun x => hilbertLindenbaumMk (.atom x)

def Hilbert.canonicalBotVal (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms] :
    HilbertLindenbaumAlgebra Axioms :=
  hilbertLindenbaumMk .bot

theorem Hilbert.canonicalV_spec
    (Axioms : Proposition Atom -> Prop) [MinimalAxioms Axioms]
    (A : Proposition Atom) :
    AlgEvaluate (Hilbert.canonicalV Axioms) (Hilbert.canonicalBotVal Axioms) A =
    hilbertLindenbaumMk A := by
  induction A with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb => simp only [AlgEvaluate_imp, iha, ihb, hilbertLindenbaumMk_himp]
  | and a b iha ihb => simp only [AlgEvaluate_and, iha, ihb, hilbertLindenbaumMk_inf]
  | or a b iha ihb => simp only [AlgEvaluate_or, iha, ihb, hilbertLindenbaumMk_sup]
```

### Phase 3: Rewrite HilbertCompleteness.lean

Replace the completeness directions to use the Hilbert Lindenbaum algebra directly. The refactored `MPL.hilbert_alg_complete`:

```lean
theorem MPL.hilbert_alg_complete
    {Atom : Type u} [DecidableEq Atom] {phi : Proposition Atom} :
    Derivable MinPropAxiom phi <-> GHAValid phi := by
  constructor
  . exact min_alg_soundness_derivable
  . intro h
    -- Instantiate at HilbertLindenbaumAlgebra MinPropAxiom
    have hLind := h (HilbertLindenbaumAlgebra MinPropAxiom)
      (Hilbert.canonicalV MinPropAxiom) (Hilbert.canonicalBotVal MinPropAxiom)
    rw [Hilbert.canonicalV_spec] at hLind
    exact hilbertLindenbaumMk_eq_top_iff.mp hLind
```

Similarly for IPL and CPL. The CPL case is slightly different since it currently goes through `Bool` and `Tautology`. With the Hilbert Lindenbaum BA instance (`hilbertLindenbaumClBA`), it can instead use the direct algebraic route.

### Phase 4: Derive ND corollaries

Add the ND versions as corollaries of the Hilbert-primary versions:

```lean
theorem MPL.alg_complete_nd {A : Proposition Atom} :
    DerivableIn (empty : Theory Atom) A <->
      forall {H} [GHA H] (v) (bot_val), AlgEvaluate v bot_val A = top := by
  constructor
  . intro h H _ v bot_val
    exact nd_alg_sound h v bot_val (fun _ hB => (Set.mem_empty_iff_false _).mp hB |>.elim)
  . intro h
    -- Via Hilbert bridge: GHAValid -> Derivable MinPropAxiom -> DerivableIn empty
    have hDeriv : Derivable MinPropAxiom A := MPL.hilbert_alg_complete.mpr (fun H _ v bv => h v bv)
    exact hilbert_iff_nd_min.mp hDeriv |>.weakTheory (Set.empty_subset _) |> ...
```

(The exact proof will depend on how `hilbert_iff_nd_min` relates `Derivable MinPropAxiom` to `DerivableIn (AxiomTheory MinPropAxiom)` and how we bridge to `DerivableIn empty`.)

## 6. Key Technical Considerations

### 6.1 Universe Polymorphism

The existing `GHAValid`, `HAValid`, `BAValid` are universe-polymorphic in `H`. The `HilbertLindenbaumAlgebra Axioms` lives in the universe of `Atom`. The completeness direction quantifies over all `H : Type u`, so instantiating at the Lindenbaum algebra requires that `Atom : Type u` (same universe). This matches the existing pattern in `Completeness.lean` where `Theory.alg_complete` has `universe u` and `Atom : Type u`.

The existing `HilbertCompleteness.lean` uses `set_option linter.unusedDecidableInType false` -- this will likely still be needed since `DecidableEq Atom` is needed by the Lindenbaum construction.

### 6.2 `hilbertLindenbaumBot_eq` for IPL/CPL

For the IPL case, we need `Hilbert.canonicalBotVal IntPropAxiom = bot` in the Heyting algebra. The `hilbertLindenbaumHeytingAlgebra` sets `bot := hilbertLindenbaumMk bot`. Since `Hilbert.canonicalBotVal` is also `hilbertLindenbaumMk bot`, this is definitional equality (both are `hilbertLindenbaumMk bot`).

### 6.3 Axiom Validity in Hilbert Lindenbaum

For the general completeness theorem, we need that all axioms evaluate to `top` under the canonical valuation. For `Hilbert.canonicalV`, if `Axioms phi` holds, then `Deriv Axioms [] phi` (by the axiom rule: `DerivationTree.ax [] phi h`). Weakening to `[bot.imp bot]` then applying `hilbertLindenbaumMk_eq_top_iff` gives `hilbertLindenbaumMk phi = top`, so `AlgEvaluate canonicalV canonicalBotVal phi = top` by the truth lemma.

### 6.4 File Organization Recommendation

Given that `HilbertCompleteness.lean` already exists and contains the Hilbert biconditionals, the recommended approach is:

1. Add `hilbertLindenbaumMk_eq_top_iff` + canonical valuation + truth lemma to `HilbertLindenbaum.lean` (or a new `HilbertCompletenessCore.lean`)
2. Refactor `HilbertCompleteness.lean` to use the direct Hilbert route
3. Keep `Completeness.lean` unchanged (ND completeness theorems remain)
4. Optionally add ND corollaries in `HilbertCompleteness.lean` that derive the ND versions from the Hilbert versions

This preserves backward compatibility while making the Hilbert versions the "primary" proofs.

## 7. Blockers and Risks

### No Blockers Identified

All required infrastructure exists:
- Hilbert Lindenbaum algebra with GHA/HA/BA instances (task 282)
- Simp lemmas for quotient operations
- Soundness theorems (Hilbert-primary)
- `hilbert_iff_nd` bridge for deriving ND corollaries
- `MinimalAxioms` typeclass providing K, S, and all connective axioms

### Risks

1. **Universe alignment**: The `GHAValid` definition quantifies over all `H : Type*`. The `HilbertLindenbaumAlgebra` is `Type _`. Must ensure the universe levels align for instantiation. The existing `HilbertCompleteness.lean` already handles this (it uses `{Atom : Type u} [DecidableEq Atom]` and the Lindenbaum algebra inherits the universe from `Atom`).

2. **`hilbertLindenbaumMk_eq_top_iff` proof**: Needs `Deriv Axioms [] (bot.imp bot)`. This should be straightforward using `hilbertImpIDeriv` (which gives `[B, ...] |- B -> B` reduced to `[...] |- B -> B`). Specifically, from the identity combinator `S K K` or from `hilbertImpIDeriv` applied to `assumption_deriv`. Need to verify the exact interface.

3. **The `DecidableEq Atom` requirement**: The Hilbert Lindenbaum algebra currently requires `MinimalAxioms Axioms` but NOT `DecidableEq Atom`. However, the completeness theorem needs `DecidableEq Atom` for `GHAValid` etc. This matches the existing pattern.

## 8. Recommended Implementation Plan

### Phase 1: Foundation Lemmas (HilbertLindenbaum.lean)
- Add `hilbertLindenbaumMk_eq_top_iff : hilbertLindenbaumMk A = top <-> Derivable Axioms A`
- Add `Hilbert.canonicalV`, `Hilbert.canonicalBotVal`
- Add `Hilbert.canonicalV_spec` (truth lemma)
- Add `Hilbert.tValid_canonicalV` (axioms valid under canonical valuation)

### Phase 2: Hilbert-Primary Completeness (HilbertCompleteness.lean)
- Rewrite `MPL.hilbert_alg_complete` completeness direction to use Hilbert Lindenbaum directly
- Rewrite `IPL.hilbert_alg_complete` completeness direction to use Hilbert Lindenbaum directly
- Rewrite `CPL.hilbert_alg_complete` completeness direction to use Hilbert Lindenbaum directly
- Remove dependency on ND completeness for the completeness direction

### Phase 3: ND Corollaries (HilbertCompleteness.lean or Completeness.lean)
- Derive `MPL.alg_complete` (ND version) from `MPL.hilbert_alg_complete` + `hilbert_iff_nd_min`
- Derive `IPL.alg_complete` (ND version) from `IPL.hilbert_alg_complete` + `hilbert_iff_nd_int`
- Derive `alg_complete_classical` (ND version) from `CPL.hilbert_alg_complete` + `hilbert_iff_nd_cl`
- Ensure downstream files (`Conservative.lean`, `Glivenko.lean`, `KripkeBridge.lean`) still compile

### Phase 4: Verification
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness`
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.Completeness`
- `lake build` (full project)

## 9. Tactic Survey

The proofs in this task are primarily structural (algebraic manipulation, cut/weakening, quotient reasoning). Key tactics:

| Tactic | Use Case |
|--------|----------|
| `simp` with `hilbertLindenbaumMk_*` lemmas | Truth lemma, canonical valuation specs |
| `rw [hilbertLindenbaumTop]` | Converting `top` to `[bot imp bot]` |
| `Quotient.sound` / `Quotient.exact` | Moving between quotient equality and equivalence relation |
| `exact` / `apply` | Structural proof assembly |
| `obtain` / `constructor` | Working with `Nonempty` (Deriv) and `And` (HilbertEquiv) |

No heavy automation (omega, decide, ring) is expected. The proofs are fundamentally about composing Hilbert derivation rules and quotient algebra facts.
