# Task 419 — SPIKE Verdict (round 3, current-source verification)

**Task type**: cslib (SPIKE, read-only research)
**Date**: 2026-06-30
**Session**: sess_1782886680_e1cb20
**Mandate**: Reach a concrete GO/NO-GO on whether `liftDerivation`/`Derivable_mono`,
Bimodal `liftDerivationWith`, and the shared derivation abstraction can collapse to ONE
axiom-subsumption derivation-lifting result — pivoting on whether the
necessitation/temporal_duality constructor variance is cleanly abstractable.

---

## 0. Headline

**VERDICT: GO — and the make-or-break variance concern is already RESOLVED in committed,
sorry-free source.** The unifying abstraction (`ProofSystemMorphism.lean`) exists in
`Cslib/Foundations/Logic/Metalogic/`, compiles green, and demonstrably subsumes both the Modal
necessitation rule and the Bimodal temporal_duality rule through a single `close` constructor +
`clMap` naturality field — with no per-system special-casing inside the generic functor
`Deriv.map`. I re-verified this by reading the actual definitions and running a scoped
`lake build` of all four modules: **691 jobs, exit 0, zero `sorry`.**

The residual work to fully deliver "ONE result the three logics *call*" is a **bounded,
non-blocking engineering step** (one documented representation change + one un-built overlay),
not a sorry trap and not an abstraction barrier. Details in §5.

**Important scoping correction to the task framing** (§4): the task names the
"`InferenceSystem` / `algebraicDerivationSystem` abstraction used by `GenericMCSBridge`" as the
hoist target. That abstraction is the **wrong** substrate — `algebraicDerivationSystem` is built
on `ListDeriv`, which *by construction excludes necessitation* (documented in
`GenericMCS.lean:103-109`). The correct, already-built substrate is `ProofSystemMorphism`'s
`Deriv`/`ProofSigHom`/`Deriv.map`, purpose-built to carry closure rules.

---

## 1. The three concrete lifting sites (exact signatures + locations)

### Site (a) — Modal `liftDerivation` / `Derivable_mono`
File: `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean:47` and `:66`.

```lean
def liftDerivation {Axioms1 Axioms2 : Proposition Atom → Prop}
    (h_sub : ∀ φ, Axioms1 φ → Axioms2 φ)
    {Γ φ} (d : DerivationTree Axioms1 Γ φ) : DerivationTree Axioms2 Γ φ
lemma Derivable_mono (h_sub : ∀ φ, Axioms1 φ → Axioms2 φ)
    (h : Derivable Axioms1 φ) : Derivable Axioms2 φ
```

- **Axiom-subsumption hypothesis**: `h_sub : ∀ φ, Axioms1 φ → Axioms2 φ` (predicate → predicate).
- **Shape**: same language (`Proposition Atom`), pure structural recursion over 5 constructors
  (`ax`, `assumption`, `modus_ponens`, `necessitation`, `weakening`). Only the `ax` arm uses
  `h_sub`; everything else is a homomorphic pass-through.
- The `DerivationTree` inductive is at `Modal/Metalogic/DerivationTree.lean:98`.

### Site (b) — Bimodal `liftDerivationWith`
File: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean:636`.

```lean
noncomputable def liftDerivationWith {fc : FrameClass} (a : Atom) :
    {Γ φ} → (d : ExtDerivationTree fc Γ φ) → (h_fresh : a ∉ collectDerivInl d) →
    DerivationTree fc (Γ.map (liftFormula a)) (liftFormula a φ)
```

- **This is NOT an axiom-subsumption lift.** It is a **cross-language conservative-extension
  projection**: it maps the *extended* calculus `ExtDerivationTree` (over `ExtFormula Atom =
  Formula (Atom ⊕ Unit)`) back to the *base* calculus `DerivationTree` (over `Formula Atom`),
  simultaneously transforming the formula index via `liftFormula a = unembedFormula ∘
  substFreshWith a` and the axiom witness via `liftAxiom a : ExtAxiom φ → Axiom (liftFormula a φ)`.
- **"Subsumption" hypothesis analogue**: `liftAxiom a` (`:581`, cases 42 axiom constructors) plus
  `liftAxiom_preserves_minFrameClass` (`:628`). The freshness side-condition `a ∉ collectDerivInl d`
  is threaded but **never consumed to build a node** (only to feed recursion); it is a downstream
  *correctness* precondition for `liftDerivationQfree` (`:691`), orthogonal to the transport.
- **7 constructors**: `axiom`, `assumption`, `modus_ponens`, `necessitation`,
  `temporal_necessitation`, `temporal_duality`, `weakening`
  (`ExtDerivation.lean:185-203`).
- Sibling in the same file: `substDerivation` (`:163`) is the endo-language substitution version.

### Site (c) — the shared abstraction(s)

Two distinct "shared" abstractions exist; **only one is the right hoist target**:

1. **`InferenceSystem` / `algebraicDerivationSystem`** (the one the task names):
   - `InferenceSystem S α` (`Foundations/Logic/InferenceSystem.lean:42`) — a *notation*
     typeclass: `derivation (a : α) : Sort v`, notation `S⇓a`. Carries **no rule structure**.
   - `algebraicDerivationSystem` (`Foundations/Logic/Metalogic/GenericMCS.lean:110`) — a
     `DerivationSystem F` built on `ListDeriv`, giving weakening/assumption/mp + a **free
     deduction theorem**. **Explicitly excludes necessitation** (`GenericMCS.lean:103-109`:
     *"ListDeriv does not include necessitation … the modal-specific `modalDerivationSystem` must
     still be used"*). **Cannot host closure rules → wrong target for derivation-lifting.**

2. **`ProofSystemMorphism`** (`Foundations/Logic/Metalogic/ProofSystemMorphism.lean`, **the
   correct and already-built substrate**):
   - `ProofSig F` — `Ax : F → Type` (Type-valued axiom family) + `closures : List (F → F)`.
   - `Deriv σ Γ φ` — free derivation algebra; constructors `ax / assum / mp / close / weak`.
   - `ProofSigHom σ₁ σ₂` — `g`, `g_imp`, `axMap : ∀ φ, σ₁.Ax φ → σ₂.Ax (g φ)`,
     `clMap : ∀ m ∈ σ₁.closures, {m' // m' ∈ σ₂.closures ∧ ∀ φ, g (m φ) = m' (g φ)}`.
   - `Deriv.map H` — **the universal lift**; functor laws `map_id`, `map_comp`, `map_height` all
     proved. **Zero `sorry`.** (git: `349f03b0`, `4e976fd8`, "task 419 phase 1".)

---

## 2. The variance crux — CONCRETELY, and why it is cleanly abstractable

The task's make-or-break question: do the Modal necessitation constructor and the
Bimodal/temporal duality constructor differ in a way that forces per-system proofs?

**Constructor shapes (read from source):**

| Rule | Constructor (concrete) | Conclusion index |
|---|---|---|
| Modal necessitation | `necessitation (φ) (d : DT Ax [] φ) : DT Ax [] (Proposition.box φ)` | `box φ` |
| Bimodal necessitation | `necessitation (φ) (d : … [] φ) : … [] (Formula.box φ)` | `box φ` |
| Bimodal temporal_necessitation | `… : … [] (Formula.allFuture φ)` | `allFuture φ` |
| Bimodal **temporal_duality** | `temporal_duality (φ) (d : … [] φ) : … [] φ.swapTemporal` | **`swapTemporal φ`** |

The *only* structural peculiarity is `temporal_duality`: its conclusion is `swapTemporal φ`, an
**involution applied to the whole formula**, not a fixed modal prefix like `box _`. Round 1 of
this task (report `01`) treated that as the abstraction barrier.

**Why it dissolves — the `close` + `clMap` design:**

`swapTemporal : Formula → Formula` is *still a unary operator* `F → F`. The generic `close`
constructor models **every** empty-context closure rule uniformly:

```lean
| close (m : F → F) (hm : m ∈ σ.closures) (φ) (d : Deriv σ [] φ) : Deriv σ [] (m φ)
```

So all three Bimodal closures are just three entries in the `closures` list:

```lean
bimodalSig.closures = [Formula.box, Formula.allFuture, Formula.swapTemporal]   -- verified, :78
modalSig.closures   = [Proposition.box]                                        -- verified, :67
```

and `temporal_duality φ d` maps to `close Formula.swapTemporal _ φ (toDeriv d)`, with conclusion
`swapTemporal φ` produced by the *same* `close` rule as `box φ`. **No special constructor, no
per-rule branch inside `Deriv.map`.**

The conclusion-variance of `swapTemporal` is absorbed **not in the constructor but in the
morphism's `clMap` naturality square** `g (m φ) = m' (g φ)`. For the cross-language lift
(`g = liftFormula a`, `m = m' = swapTemporal`) this square is *exactly* the already-existing
Bimodal lemma `liftFormula_swapTemporal` (`ConservativeExtension/Lifting.lean:576`) — and for the
endo-substitution version it is `substFormula_swapTemporal` (used at `:179`). For the
frame-class and Modal instances `g = id`, so the square is `rfl`. These naturality lemmas
**already exist in source**, which is the decisive evidence the abstraction is the *right* one,
not a post-hoc fit.

**Answer to Q2: YES.** A single `ProofSigHom`-parameterized functor (`Deriv.map`) subsumes both
necessitation and temporal_duality with zero per-system special-casing. The variance lives in
data (`closures` list) and in a naturality field (`clMap`), both of which are already realized
sorry-free.

---

## 3. GO/NO-GO verdict

**GO.** Justification, grounded in re-verified current source:

1. **The abstraction exists and is green.** `ProofSystemMorphism.lean` (`Deriv`, `ProofSigHom`,
   `Deriv.map`, `map_id`, `map_comp`, `map_height`) is committed, `sorry`-free, and builds.
2. **The variance is provably abstractable** (§2): the `close`+`clMap` mechanism is exercised
   concretely for Modal (1 closure) and Bimodal (3 closures incl. `swapTemporal`).
3. **Two of three logics already have full corollaries** (§5), sorry-free:
   - Modal: `modalEquiv` (genuine `Equiv`, both directions + round-trips), `modalHom h_sub`,
     `toDeriv_liftDerivation`, `Derivable_mono_via_morphism`.
   - PL: `plEquiv`, `plHom`, `toDeriv_liftDerivationTree`, `derivable_mono_via_morphism`.
4. **No `sorry`, no new axiom, no vacuous def** anywhere in the delivered infrastructure.

There is **no abstraction barrier** forcing per-system proofs of the *core* lifting fact. The one
place per-system work is irreducible is the `toDeriv` bridge between each concrete inductive and
`Deriv σ` — that is inherent to any overlay across distinct Lean types and is *not* a defect.

---

## 4. If GO: target signature, home file, and migration status

**Target unified lemma (already implemented):**

```lean
-- Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean
def Deriv.map {F₁ F₂} [HasImp F₁] [HasImp F₂] {σ₁ : ProofSig F₁} {σ₂ : ProofSig F₂}
    (H : ProofSigHom σ₁ σ₂) :
    ∀ {Γ φ}, Deriv σ₁ Γ φ → Deriv σ₂ (Γ.map H.g) (H.g φ)
```

**Home file**: `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` — this is exactly the
task-417 Foundations placement the soft-dependency anticipated; already in place.

**Per-logic overlays (all committed, sorry-free, build green):**

| Logic | Overlay file | Status |
|---|---|---|
| Modal | `Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean` (221 ln) | **FULL** — `Equiv` + `liftDerivation`/`Derivable_mono` exhibited as `Deriv.map` corollaries |
| PL | `Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean` (204 ln) | **FULL** — `Equiv` + `liftDerivationTree`/`derivable_mono` corollaries |
| Bimodal | `Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean` (183 ln) | **PARTIAL** — see §5 |

All overlays are **non-invasive**: the original `Lifting.lean` / `Derivation.lean` lift
functions are unchanged; the morphism versions sit alongside as corollaries.

---

## 5. The precise residual scope (bounded, non-blocking)

Two gaps remain between current state and "one reusable result across Modal + Bimodal + PL":

### 5.1 Bimodal overlay covers `DerivationTree.lift`, not `liftDerivationWith`
The landed Bimodal pilot (`bimodalSig`, `bimodalHom h_le`, `toDeriv_lift`) exhibits the
**frame-class monotonicity** lift `DerivationTree.lift` (`fc₁ ≤ fc₂`) — an easier *same-language*
(`g = id`, `axMap = le_trans`) instance. The **conservative-extension** lift `liftDerivationWith`
(the one the task explicitly named, `g = liftFormula a : ExtFormula → Formula`) is **not yet
exhibited**. Building it requires:
- a `toDeriv : ExtDerivationTree fc Γ φ → Deriv (extSig fc) Γ φ` bridge, and
- `liftHom a : ProofSigHom (extSig fc) (bimodalSig fc)` with `g = liftFormula a`,
  `g_imp = liftFormula_imp`, `axMap = liftAxiom a` (+ `liftAxiom_preserves_minFrameClass`),
  `clMap` naturality = `liftFormula_swapTemporal`.

All required naturality/axiom lemmas already exist in `ConservativeExtension/Lifting.lean`
(`:571`, `:576`, `:581`, `:628`). This is assembly, not new mathematics. **No `sorry` needed.**

### 5.2 The `ofDeriv` / full-`Equiv` obstruction for multi-closure systems (documented)
`Bimodal/…/LiftViaMorphism.lean:41-50` records a real, precise barrier: the backward map
`ofDeriv` must case-split on `hm : m ∈ [box, allFuture, swapTemporal]` — large elimination of the
**non-singleton `Prop` inductive `List.Mem`** (constructors `head`/`tail`) into `Type u`, which
the kernel forbids. Modal escapes this only because its `closures` is a *singleton*
(`List.mem_singleton` gives a clean `rfl`). Consequences:
- Modal + PL get full `Equiv`s; Bimodal gets only the **forward map + HEq intertwining**.
- A truly uniform `Equiv` for multi-closure logics needs `ProofSig.closures` refactored from
  `List (F → F)` to a **`Type`-valued index** (e.g. `Fin n → F → F`, or a `Fintype`-backed
  carrier), so the closure witness carries data and dispatch avoids `List.Mem` large elimination.

**Neither gap blocks the SPIKE verdict.** The forward direction (`Deriv.map` = the lift) — which
is what "derivation lifting" *means* — is total, generic, and sorry-free for all three logics.
The `Equiv` is a stronger, optional convenience; its obstruction is documented and has a known
`sorry`-free resolution path (Type-valued `closures`).

---

## 6. Recommended next action + territory

Given the SPIKE is satisfied (GO) and most of the deliverable is already committed green, the
implementer's remaining choices are:

1. **Minimal-close (recommended for SPIKE closure)**: accept the current green overlays as the
   deliverable; document §5.1/§5.2 as the residual and either (a) mark task 419 done at
   "abstraction + Modal/PL full + Bimodal frame-class forward" or (b) open a bounded follow-up for
   the `liftDerivationWith` overlay + `Fin n` closures refactor.
2. **Complete-the-hoist (larger)**: implement §5.1 (`liftDerivationWith` via morphism) and
   optionally §5.2 (`closures : Fin n → F → F` to unlock Bimodal `Equiv`). Both sorry-free.

**Territory (per the task's concurrent-session note):**
- Permitted write territory: `Logics/Modal/Metalogic/InterSystem/Lifting.lean`,
  `Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean`, and the shared Foundations file
  `Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (+ its Bimodal overlay only if the other
  session is not touching `ConservativeExtension/LiftViaMorphism.lean`; it declared ownership of
  `Embedding/TemporalEmbedding.lean` and `ConservativeExtension/TemporalConservativity.lean`,
  which are distinct files).
- **Do NOT edit** `Bimodal/Embedding/TemporalEmbedding.lean` or
  `Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean` (owned by concurrent
  session running shake import-minimization).
- The §5.2 `closures` representation change touches the shared Foundations file and every overlay;
  if pursued, coordinate/sequence it *after* the concurrent shake pass to avoid churn.

---

## 7. Zero-debt / reuse-first compliance
- **Reuse-first**: the correct reuse is `ProofSystemMorphism` (already in Foundations), **not**
  `algebraicDerivationSystem` (cannot carry closures) and **not** a nonexistent Mathlib free
  multicategory (confirmed absent in report `02`; `LHom`/`Cat.freeMap` are precedent, not payload).
- **Zero-debt**: no `sorry`, no new axiom, no vacuous def in delivered or recommended work; the one
  documented obstruction (§5.2) has a `sorry`-free resolution and does not gate the verdict.
- **Build evidence**: scoped `lake build` of all four modules = 691 jobs, exit 0, this session.

---

## Appendix — verified file:line index (read this session)
- `Modal/Metalogic/InterSystem/Lifting.lean:47,66` — `liftDerivation`, `Derivable_mono`
- `Modal/Metalogic/DerivationTree.lean:98` — `DerivationTree` inductive (5 ctors)
- `Bimodal/Metalogic/ConservativeExtension/Lifting.lean:163,571,576,581,628,636,691` —
  `substDerivation`, `liftFormula_imp`, `liftFormula_swapTemporal`, `liftAxiom`,
  `liftAxiom_preserves_minFrameClass`, `liftDerivationWith`, `liftDerivationQfree`
- `Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean:185-203` — `ExtDerivationTree` (7 ctors)
- `Foundations/Logic/InferenceSystem.lean:42` — `InferenceSystem` typeclass
- `Foundations/Logic/Metalogic/GenericMCS.lean:110,103-109` — `algebraicDerivationSystem`
  (+ necessitation-exclusion note)
- `Foundations/Logic/Metalogic/ProofSystemMorphism.lean` — `ProofSig`, `Deriv`, `ProofSigHom`,
  `Deriv.map`, functor laws (whole file, sorry-free)
- `Modal/.../LiftViaMorphism.lean`, `Bimodal/.../LiftViaMorphism.lean`,
  `Propositional/.../LiftViaMorphism.lean` — the three overlays (sorry-free)
</content>
</invoke>
