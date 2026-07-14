# Teammate A Findings — Primary Approach (Task 448)

**Angle**: PRIMARY — feasibility and concrete Lean mechanics of representation option **R1**
plus the three ROI-gated phases (Vision B: `Deriv σ` as shared-metatheory substrate).
**Method**: grounded in source reads + one live Lean compile of the core R1 mechanic
(`lean_run_code`, zero diagnostics). No speculation.

---

## Key Findings

1. **The blocker is exactly as report 04 describes, and R1 dissolves it — verified by compiling a
   faithful mini-model.** The `Deriv.close` constructor currently carries closure membership as a
   **`Prop`** (`hm : m ∈ σ.closures`, i.e. `List.Mem` with ctors `head`/`tail`). Backward dispatch
   needs to eliminate that non-singleton `Prop` into a `Type`-valued native derivation — kernel-forbidden
   large elimination. Re-indexing `close` by `Fin σ.closures.length` (**data**) makes backward dispatch
   legal. I built a self-contained model of this (`Sig`/`Der` with `close (i : Fin closures.length)`, a
   3-closure signature, a native 3-ctor inductive, forward+backward maps, and the round-trip theorem)
   and it compiles **sorry-free with zero diagnostics**. This is the load-bearing proof of Phase 1+2
   feasibility (see Evidence §E1).

2. **The "touches only Foundations file + 3 overlays" claim is CONFIRMED — not just plausible, exhaustive.**
   Grepping the entire `Cslib/` tree, only **four** files reference `ProofSystemMorphism` / `Metalogic.Deriv`
   / `Deriv.map` / `clMap` / `ProofSigHom`:
   - `Cslib/Foundations/Logic/Metalogic/ProofSystemMorphism.lean` (the Foundations layer)
   - `Cslib/Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean` (Modal overlay — **full Equiv**)
   - `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean` (PL overlay — **full Equiv**)
   - `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean` (Bimodal — **forward+HEq only**)

   No native `DerivationTree` inductive is touched; the non-invasive A1 posture holds. R1 is fully contained.

3. **The three overlays are asymmetric in exactly the predicted way.** PL: `closures = []` → backward
   `close` case is vacuous (`False.elim (List.not_mem_nil hm)`), full Equiv already delivered.
   Modal: `closures = [Proposition.box]` → `List.mem_singleton.mp hm` collapses membership to `m = box`,
   full Equiv already delivered. Bimodal: `closures = [box, allFuture, swapTemporal]` → three-way
   `head/tail/tail` on a `Prop` → only forward + HEq (`toDeriv`, `bimodalHom`, `toDeriv_lift`); the file
   itself documents the obstruction and names `Fin n → F` indexing as the fix (lines 41–50).

4. **All Layer-1/Phase-2 assembly ingredients already exist and are green.** In
   `Bimodal/.../ConservativeExtension/Lifting.lean`: `liftFormula` (:562), `liftFormula_imp` (:571),
   `liftFormula_swapTemporal` (:576), `liftAxiom` (:581), `liftAxiom_preserves_minFrameClass` (:628),
   and `liftDerivationWith` (:636, `noncomputable`). So exhibiting `liftDerivationWith` as a `Deriv.map`
   instance is pure assembly, requiring no new mathematics.

5. **Phase 3 is the only phase with genuine cost and genuine risk.** Phases 1–2 are mechanical
   (representation change + re-proving already-proven functor laws + one backward recursion + round-trips).
   Phase 3 is a real metatheorem. My recommended flagship consumer is the **generic deduction theorem**
   over `Deriv σ` (see Recommended Approach §Phase 3), with the generic **height-induction recursor** as
   a cheap de-risking warm-up.

---

## Recommended Approach (Phase-by-phase Lean sketch)

### Phase 1 — R1 surgical refactor (Foundations + 3 overlays). Confidence: HIGH.

**ProofSig: unchanged.** Keep `closures : List (F → F)` — the ergonomic "here are my closures" reading
survives (this is R1's advantage over R2).

**`Deriv.close` — re-index by `Fin`:**
```lean
| close (i : Fin σ.closures.length) (φ : F) (d : Deriv σ [] φ)
      : Deriv σ [] (σ.closures.get i φ)
```
For a *concrete* signature the length reduces definitionally: `(bimodalSig fc).closures.length` ⇝ `3`,
so `Fin (bimodalSig fc).closures.length` is definitionally `Fin 3`. This is why literal indices
`⟨0, by decide⟩ … ⟨2, by decide⟩` type-check in the overlays and why backward `fin_cases`/`match` is
exhaustive with no impossible-index branch (verified §E1).

**`ProofSigHom.clMap` — index map with naturality (data, not Prop):**
```lean
clMap : ∀ i : Fin σ₁.closures.length,
    { j : Fin σ₂.closures.length // ∀ φ, g (σ₁.closures.get i φ) = σ₂.closures.get j (g φ) }
```

**`ProofSigHom.id.clMap := fun i => ⟨i, fun _ => rfl⟩`** (index fixed).
**`ProofSigHom.comp.clMap`** stays in *projection form* (as the current `comp` does, lines 161–166) so
`(comp …).clMap.val` is definitionally `(H₂.clMap (H₁.clMap i).val).val` — `map_comp`'s `close` case
relies on this.

**`Deriv.map` close case** — structurally identical to today, cast on the naturality equation:
```lean
| _, _, .close i φ d =>
    (H.clMap i).2 φ ▸ .close (H.clMap i).1 _ (map H d)
```

**Re-prove the functor laws** (`map_height`, `map_id`, `map_comp`). These are the main labor. The `close`
cases change from "membership by `proof_irrel_heq`" to "index equality" — arguably *simpler*, since
`Fin` equalities discharge by `rfl`/projection rather than proof irrelevance. `map_id`'s close case:
the identity index map returns `i`, so both sides carry index `i` and reduce as before. Risk is low but
nonzero because these HEq/`congr 1` proofs are cast-sensitive; budget the bulk of Phase-1 effort here.

**Overlay updates (mechanical):**
- **PL** (`plSig.closures = []`): `clMap`, backward `close`, and `close` round-trip cases stay vacuous —
  `Fin 0` is empty (`i.elim0` / `Fin.elim0`) instead of `List.not_mem_nil`. Trivial.
- **Modal** (`[box]`): `Fin 1` has the single index `⟨0, _⟩`; `toDeriv` uses `⟨0, by decide⟩`, `ofDeriv`
  matches `⟨0, _⟩ => .necessitation …`. Round-trips by `fin_cases i`/`Fin.fin_one_eq_zero`. Trivial.
- **Bimodal** (`[box, allFuture, swapTemporal]`): `toDeriv` uses `⟨0/1/2, by decide⟩` for
  necessitation/temporal_necessitation/temporal_duality; `clMap`/`toDeriv_lift` unchanged in spirit.

**Acceptance**: functor laws re-proved; `lake build` scoped to the 4 modules green; `lean_verify` shows
zero `sorry`/axioms beyond Lean/Mathlib. Achievable sorry-free.

### Phase 2 — Bimodal backward map + uniform Equivs. Confidence: HIGH (mechanic verified).

**`ofDeriv` (Bimodal), now legal:**
```lean
def ofDeriv {fc Γ φ} : Metalogic.Deriv (bimodalSig fc) Γ φ → DerivationTree fc Γ φ
  | .ax _ _ ⟨a, hfc⟩ => .axiom _ _ a hfc
  | .assum _ _ h      => .assumption _ _ h
  | .mp _ φ ψ d₁ d₂   => .modus_ponens _ φ ψ (ofDeriv d₁) (ofDeriv d₂)
  | .close i φ d =>
      match i with
      | ⟨0, _⟩ => .necessitation φ (ofDeriv d)
      | ⟨1, _⟩ => .temporal_necessitation φ (ofDeriv d)
      | ⟨2, _⟩ => .temporal_duality φ (ofDeriv d)
  | .weak _ _ _ d h   => .weakening _ _ _ (ofDeriv d) h
```
In each `close` branch the goal conclusion `(bimodalSig fc).closures.get ⟨k,_⟩ φ` reduces definitionally
to `box φ`/`allFuture φ`/`swapTemporal φ`, matching the native ctor's conclusion — no cast needed. §E1
confirms this exact pattern compiles. `bimodalEquiv : DerivationTree fc Γ φ ≃ Deriv (bimodalSig fc) Γ φ`
then assembles from `toDeriv`/`ofDeriv` + two round-trip inductions (both close by `simp only [toDeriv,
ofDeriv, ih]` per §E1's `round_trip`).

**Uniformity**: rewrite Modal/PL `ofDeriv` close-cases in the `Fin`-dispatch style (Modal: single `⟨0,_⟩`;
PL: `Fin 0` empty). This removes the "Modal is special because singleton" `List.mem_singleton` special-casing
and makes all three logics carry a genuinely uniform full `Equiv`.

**Optional**: exhibit `liftDerivationWith` as a `Deriv.map` instance via a cross-syntax hom
`liftHom a : ProofSigHom (extSig fc) (bimodalSig fc)` with `g = liftFormula a` — all naturality/axiom
lemmas already exist (Key Finding 4). Pure assembly, no R1 dependency.

### Phase 3 — THE ROI GATE. Recommended flagship: **generic deduction theorem**. Confidence: MEDIUM-HIGH.

Warm-up (cheap, de-risks Phase 3): a **generic height-recursor / strong-induction principle** on
`Deriv σ` (leveraging the existing `Deriv.height`, ProofSystemMorphism.lean:92). Low-risk, and it is the
tool the deduction-theorem `weak` case wants.

**Flagship statement** (parameterize `σ` by a small implicational-axiom bundle so the combinators exist):
```lean
/-- σ has the Hilbert implicational axioms as inhabited axiom instances. -/
class HasHilbertImp {F} [HasImp F] (σ : ProofSig F) where
  kAx : ∀ φ ψ,   σ.Ax (φ ⇒ ψ ⇒ φ)
  sAx : ∀ φ ψ χ, σ.Ax ((φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ χ)
  iAx : ∀ φ,     σ.Ax (φ ⇒ φ)

theorem deduction {F} [HasImp F] {σ : ProofSig F} [HasHilbertImp σ]
    {Γ : List F} {φ ψ : F} :
    Deriv σ (φ :: Γ) ψ → Deriv σ Γ (HasImp.imp φ ψ)
```
**Proof obligations by constructor** (induction on the `φ :: Γ ⊢ ψ` derivation):
- `assum`: `ψ ∈ φ :: Γ`. If `ψ = φ` use `iAx` (`⊢ φ ⇒ φ`); else `ψ ∈ Γ`, derive `Γ ⊢ ψ` by `assum`,
  then `Γ ⊢ φ ⇒ ψ` via `kAx` + `mp`.
- `ax`: weaken axiom to `Γ ⊢ ψ`, then `kAx` + `mp`.
- `mp`: IH gives `Γ ⊢ φ ⇒ (χ ⇒ ψ)` and `Γ ⊢ φ ⇒ χ`; combine via `sAx` + two `mp`.
- **`close`: VACUOUS** — `close` is only formable at context `[]`, which cannot be `φ :: Γ` (nonempty).
  This is the cleanest case and a nice structural payoff of the `[]`-only closure design.
- `weak`: subderivation has context `Γ'` with `Γ' ⊆ φ :: Γ`; case on `φ ∈ Γ'` (IH) vs not (weaken).
  The one genuinely fiddly case; the height-recursor warm-up helps here.

**Transport** (the ROI): via `plEquiv`/`modalEquiv`/`bimodalEquiv`, pull `deduction` back to each concrete
logic — e.g. `DerivationTree A (φ :: Γ) ψ → DerivationTree A Γ (φ ⇒ ψ)` for PL/Modal — proving the
deduction theorem **once** instead of three times. That is the concrete downstream consumer that justifies
paying for R1 + Phase 2. `HasHilbertImp` instances are discharged per logic from their existing axiom sets.

**Why deduction theorem over the alternatives**: soundness-skeleton is highest-value but needs a
semantic-algebra abstraction that does not yet exist and diverges across Kripke (modal/bimodal) vs algebraic
(PL) semantics — too heavy for the *first* metatheorem. Height/subformula induction is a technique helper,
not a headline. Deduction theorem is textbook, every Hilbert system wants it, has real consumers in all
three logics, and its `close` case is *vacuous* here — maximal ROI at manageable risk.

---

## Evidence / Examples

### E1 — Live compile of the R1 core mechanic (zero diagnostics)

Ran via `lean_run_code` (`import Mathlib`), compiled clean:
```lean
structure Sig (F : Type) where
  closures : List (F → F)
inductive Der {F} (σ : Sig F) : F → Type
  | base (φ : F) : Der σ φ
  | close (i : Fin σ.closures.length) (φ : F) (d : Der σ φ) : Der σ (σ.closures.get i φ)
def bsig : Sig Nat := { closures := [box, fut, swp] }   -- 3 closures
-- native 3-ctor inductive `Native` (mirrors DerivationTree box/fut/swp)
def toDer : {φ : Nat} → Native φ → Der bsig φ
  | _, .nec φ d => .close ⟨0, by decide⟩ φ (toDer d) | ...
def ofDer : {φ : Nat} → Der bsig φ → Native φ           -- BACKWARD: legal Fin dispatch
  | _, .close i φ d => match i with
      | ⟨0,_⟩ => .nec φ (ofDer d) | ⟨1,_⟩ => .tnec φ (ofDer d) | ⟨2,_⟩ => .tdual φ (ofDer d)
theorem round_trip {φ} (d : Native φ) : ofDer (toDer d) = d := by
  induction d with | base φ => rfl | nec φ d ih => simp only [toDer, ofDer, ih] | ...
```
Result: `{"success":true, "diagnostics":[]}`. Notes: (a) backward dispatch into the `Type`-valued `Native`
is accepted — the forbidden large elimination is gone; (b) the `match` on `Fin 3` is exhaustive with **no**
impossible-index branch, because `bsig.closures.length` reduces to `3`; (c) round-trip proves by plain
structural induction, sorry-free.

### E2 — Current blocker signatures (real source)

`ProofSystemMorphism.lean:82` — the Prop-membership `close`:
```lean
| close (m : F → F) (hm : m ∈ σ.closures) (φ : F) (d : Deriv σ [] φ) : Deriv σ [] (m φ)
```
`ProofSystemMorphism.lean:137-138` — current (already Type-valued) `clMap` over membership:
```lean
clMap : ∀ m ∈ σ₁.closures,
    { m' : F₂ → F₂ // m' ∈ σ₂.closures ∧ ∀ φ : F₁, g (m φ) = m' (g φ) }
```
`Bimodal/.../LiftViaMorphism.lean:41-50` — the file's own documented obstruction, naming
`Fin n → F` indexing as the fix. `Bimodal/.../LiftViaMorphism.lean:93-104` — forward `toDeriv` maps the
three closures to `close box/allFuture/swapTemporal (by simp [bimodalSig]) …`; no `ofDeriv` exists.

### E3 — Dependency containment (exhaustive grep of `Cslib/`)

Only 4 files reference `ProofSystemMorphism`/`Metalogic.Deriv`/`Deriv.map`/`clMap`/`ProofSigHom`:
Foundations `ProofSystemMorphism.lean` + the three `LiftViaMorphism.lean` overlays. No downstream file,
no native inductive. "Touches only Foundations file + 3 overlays" = confirmed exhaustively.

### E4 — Phase-2/Layer-1 ingredients exist (real source)

`Bimodal/.../ConservativeExtension/Lifting.lean`: `liftFormula` (:562), `liftFormula_imp` (:571),
`liftFormula_swapTemporal` (:576), `liftAxiom` (:581), `liftAxiom_preserves_minFrameClass` (:628),
`liftDerivationWith` (:636). Bimodal `DerivationTree` closure ctors: `necessitation` (:70),
`temporal_necessitation` (:74), `temporal_duality` (:79) — the three that map to `Fin 0/1/2`.

---

## Confidence Level

| Phase | Confidence | Basis |
|---|---|---|
| **Phase 1** (R1 refactor + re-prove functor laws) | **HIGH** | Mechanic compiles (§E1); containment exhaustive (§E3); only labor is re-proving 3 already-proven HEq functor laws whose `close` cases get *simpler* (Fin equality vs proof irrelevance). Nonzero risk isolated to cast-sensitive `map_comp`. |
| **Phase 2** (Bimodal `ofDeriv`/`bimodalEquiv` + uniform Modal/PL) | **HIGH** | Backward dispatch + round-trip proved in miniature (§E1); Modal/PL already have full Equivs to pattern-match; `Fin 0`/`Fin 1` cases trivial. |
| **Phase 2 optional** (`liftDerivationWith` as `Deriv.map`) | **HIGH** | Pure assembly; all lemmas exist (§E4); no R1 dependency. |
| **Phase 3** (generic deduction theorem + transport) | **MEDIUM-HIGH** | Textbook proof; `close` case vacuous (structural win); risk concentrated in the `weak` case and setting up the `HasHilbertImp` bundle correctly per logic. De-risk with the height-recursor warm-up first. |

**Net**: R1 + all three phases are feasible and sorry-free-achievable. Phases 1–2 are mechanical with the
key large-elimination wall empirically dissolved. Phase 3 is the only real intellectual cost and is where
ROI must be booked — the generic deduction theorem is the strongest first consumer (vacuous `close` case,
three concrete downstream transports, no new semantic infrastructure required).

**Anti-goals respected**: no A2 inductive replacement, no `Prop`-ifying Bimodal `Axiom`, no
`Classical.choice` backward map — R1's `Fin` data makes all three unnecessary.
