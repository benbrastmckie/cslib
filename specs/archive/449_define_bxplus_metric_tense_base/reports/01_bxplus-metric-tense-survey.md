# Research Report — Task 449: Foundation for BX⁺ (metric tense base)

**Goal**: introduce `BX⁺` = the metric tense logic sound over ordered-abelian-group time, as
the *matching* temporal base over which TM is genuinely conservative (superseding the false
`bimodal_conservative_over_temporal`-over-plain-BX from abandoned task 445).

**Scope of this task (foundation only)**: (1) a new Temporal `FrameClass.Metric` with
`Base < Metric`; (2) the FOUR pure-temporal uniformity axioms gated to `.Metric`; (3) the
semantic class of ordered-abelian-group temporal frames + soundness of the four axioms over it,
extending Temporal soundness to `FrameClass.Metric`; (4) Derivable/DerivationTree plumbing +
a `BX⁺` derivability abbreviation. The conservativity theorem itself and the box-necessity
handling are out of scope (task 450).

## TL;DR — feasibility verdict: GREEN, low risk, sorry-free achievable

Every load-bearing claim below was **machine-verified** with `lake env lean` (exit 0), not
asserted. The task is a clean mirror of the existing `Dense` layering, plus four axiom-soundness
proofs that port **almost verbatim** from the already-proven bimodal uniformity-axiom proofs.

- The Temporal `FrameClass` inductive + `LE`/`PartialOrder`/`DecidableRel`/`base_le` extend
  mechanically to a 4th constructor `Metric` with `Base < Metric` (incomparable to Dense/Discrete).
- The four temporal uniformity axioms are `untl bot top`-based formulas (identical shape to the
  existing `dense_indicator`), gated by adding four lines to `Axiom.minFrameClass`.
- Soundness over ordered-abelian-group frames is provable sorry-free: **two of the four proofs
  were fully reproduced in the temporal `Satisfies` semantics and compiled clean**; the other two
  are their swap-duals with identical arithmetic.
- **Key simplification discovered**: a nontrivial ordered abelian group **auto-synthesizes
  `NoMaxOrder` and `NoMinOrder`** in Mathlib (verified). So the metric frame class needs only
  `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]`, and base-axiom
  delegation to the existing `axiom_sound` (which requires `NoMaxOrder`/`NoMinOrder`) works with
  no extra hypotheses.
- The Derivable/DerivationTree/`DerivFc`/`ThDerivableFc` plumbing is **already frame-class-
  parameterized** — no new plumbing is required beyond a `BX⁺` abbreviation
  (`ThDerivableFc FrameClass.Metric`).

The only mandatory ripple: **two existing exhaustive `cases h_ax with` sites** (`axiom_sound`,
`axiom_sound_dense`) must gain four new absurd-discharge cases, exactly like the existing
`density`/`dense_indicator` catch at `Soundness.lean:325–326`.

## Reuse Check Protocol (reuse-first)

| Candidate reuse | Result |
|---|---|
| Existing Temporal `FrameClass.Metric` | **None** — `grep "Metric" Cslib/Logics/Temporal/` returns nothing. Must add. |
| Frame-class plumbing (`DerivationTree`, `Derivable`, `DerivFc`, `ThDerivableFc`) | **Fully reusable, already `fc`-parameterized** (`ProofSystem/Derivation.lean:50`, `ProofSystem/Derivable.lean:35`, `Metalogic/DenseMCS.lean:60,67`). No new plumbing needed. |
| Axiom soundness arithmetic | **Reusable from bimodal** — `discrete_symm_fwd_valid` … `discrete_propagate_bwd_valid` (`Bimodal/Metalogic/Soundness/Soundness.lean:451–511`) port verbatim (same `t - (s-t)` / `u + (s-t)` translation arithmetic). |
| Dense soundness layering | **Structural template** — `Metalogic/DenseSoundness.lean` is the exact shape to mirror (`density_axiom_sound`, `axiom_sound_dense`, `swap_valid_of_valid_dense`, `soundness_dense`, `soundness_thderivable_dense`). |
| Metric frame constraints | **Reuse the bimodal domain constraints verbatim**: `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]` (= `TaskFrame` domain, `Bimodal/Semantics/TaskFrame.lean`, and `Bimodal/Semantics/Validity.lean:49–55` `valid`). |
| `NoMaxOrder`/`NoMinOrder` for serial | **No explicit hypothesis needed** — Mathlib auto-derives both from a nontrivial ordered abelian group (verified). |

No new notation typeclass is introduced. No new abstraction is introduced beyond the one the
task mandates (`FrameClass.Metric` + four axioms), which has no existing equivalent.

## The four extension points (mirroring `Dense`)

### 1. `FrameClass.Metric` (in `Cslib/Logics/Temporal/ProofSystem/Axioms.lean`)

The inductive currently is `Base | Dense | Discrete` (lines 40–44). Add `| Metric`. The three
instances extend by their existing tactic bodies with **zero manual edits** because they use
`cases a <;> cases b <;> …`:

- `LE` (lines 46–51): the pattern `.Base, _ => True` already gives `Base ≤ Metric`; add
  `| .Metric, .Metric => True` before the `_, _ => False` catch-all. This yields `Base < Metric`
  and `Metric` incomparable with `Dense`/`Discrete` (matches the task's "Base < Metric").
- `DecidableRel` (lines 53–54): `cases a <;> cases b <;> simp only [LE.le] <;> infer_instance`
  extends automatically.
- `PartialOrder` (lines 56–60): `le_refl`/`le_trans`/`le_antisymm` all use
  `cases … <;> simp_all [LE.le]` — extend automatically.
- `FrameClass.base_le` (lines 62–64): `cases fc <;> trivial` extends automatically.
- Update the `FrameClass` docstring to mention `Metric` (metric/ordered-abelian-group time).

### 2. The four temporal uniformity axioms (add to `Axiom` inductive + `Axiom.minFrameClass`)

Add four constructors to `inductive Axiom` (as a new "Layer: Metric Uniformity"), each a
`untl bot top`-based formula — same shape as the existing `dense_indicator`
(`untl Formula.bot Formula.top`, line 222). Using CSLib's `untl` = (guard, event) Pnueli order,
`untl bot top` at `t` means "`t` has an immediate successor" (∃ s>t with empty open interval
`(t,s)`); `snce bot top` is its past mirror.

```lean
  /-- Metric symmetry (fwd): U(⊥,⊤) → S(⊥,⊤). Immediate successor ⇒ immediate predecessor.
      Valid on ordered-abelian-group time (negation symmetry). -/
  | discrete_symm_fwd :
      Axiom ((Formula.untl Formula.bot Formula.top).imp
        (Formula.snce Formula.bot Formula.top))
  /-- Metric symmetry (bwd): S(⊥,⊤) → U(⊥,⊤). -/
  | discrete_symm_bwd :
      Axiom ((Formula.snce Formula.bot Formula.top).imp
        (Formula.untl Formula.bot Formula.top))
  /-- Metric propagation (fwd): U(⊥,⊤) → G(U(⊥,⊤)). Translation-invariance forwards. -/
  | discrete_propagate_fwd :
      Axiom ((Formula.untl Formula.bot Formula.top).imp
        (Formula.allFuture (Formula.untl Formula.bot Formula.top)))
  /-- Metric propagation (bwd): U(⊥,⊤) → H(U(⊥,⊤)). Translation-invariance backwards. -/
  | discrete_propagate_bwd :
      Axiom ((Formula.untl Formula.bot Formula.top).imp
        (Formula.allPast (Formula.untl Formula.bot Formula.top)))
```

Note: names deliberately match the bimodal originals (`Bimodal/ProofSystem/Axioms.lean:250–268`)
for cross-logic legibility; the task specifies these exact names. **Naming caveat**: these
contain `discrete_` prefixes but are NOT the discreteness axioms — they are the *uniformity*
(metric/homogeneity) axioms. This is inherited from the bimodal side; keep it for parity but the
docstrings should say "metric uniformity", not "discreteness" (avoids the `defsWithUnderscore`
lint being the only concern — underscores in constructor names are fine; these are inductive
constructors, not top-level `def`s).

Then gate them in `Axiom.minFrameClass` (lines 256–260) by adding, before the `| _ => .Base`
catch-all:

```lean
  | .discrete_symm_fwd => .Metric
  | .discrete_symm_bwd => .Metric
  | .discrete_propagate_fwd => .Metric
  | .discrete_propagate_bwd => .Metric
```

The bimodal `discrete_box_necessity` (`χ → □χ`) has **no pure-temporal form** (it erases to a
tautology) and is explicitly deferred to task 450 — do NOT add it here.

### 3. Semantic metric frame class + soundness

Create a new module `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean` mirroring
`DenseSoundness.lean`. The "metric frame class" is expressed (as `Dense` is) by the instance
constraints on the domain `D`, reusing the bimodal `TaskFrame` domain constraints:
`[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]`. No `TemporalModel`
change is needed — the existing `TemporalModel` (just a valuation over a `LinearOrder`,
`Semantics/Model.lean:42`) suffices; the metric structure lives entirely in the domain
typeclasses.

Per-axiom soundness proofs port verbatim from the bimodal `*_valid` theorems, but simpler (no
`ℱ M Omega τ` modal machinery — just `Satisfies`). **Machine-verified** (both compiled clean):

```lean
theorem discrete_symm_fwd_sound {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] {Atom : Type*} (M : TemporalModel D Atom) (t : D) :
    Satisfies M t ((Formula.untl Formula.bot Formula.top).imp
      (Formula.snce Formula.bot Formula.top)) := by
  intro ⟨s, hts, _htop, h_guard⟩
  refine ⟨t - (s - t), sub_lt_self t (sub_pos.mpr hts), Satisfies.top_true M _,
    fun c hrc hct => ?_⟩
  have h1 : t < c + (s - t) :=
    calc t = t - (s - t) + (s - t) := (sub_add_cancel t (s - t)).symm
      _ < c + (s - t) := add_lt_add_left hrc (s - t)
  have h2 : c + (s - t) < s :=
    calc c + (s - t) < t + (s - t) := add_lt_add_left hct (s - t)
      _ = s := by rw [add_comm, sub_add_cancel]
  exact h_guard (c + (s - t)) h1 h2
```

`discrete_propagate_fwd_sound` (verified) uses witness `u + (s - t)` and the `sub_sub_cancel` /
`add_sub_sub_cancel` chain from `Bimodal/.../Soundness.lean:481–495`. The two `bwd` variants are
the past mirrors (`discrete_symm_bwd_valid`/`discrete_propagate_bwd_valid` templates,
`Soundness.lean:466–479,497–511`) — note the bimodal `bwd` proofs use the same arithmetic and
compiled in-repo, so they transfer identically. Neither `symm` nor `propagate` needs
`Nontrivial`; only base-axiom delegation does (below).

Extended axiom soundness + derivation soundness (mirror `axiom_sound_dense`/`soundness_dense`/
`soundness_thderivable_dense`):

```lean
theorem axiom_sound_metric {D : Type*} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D]
    {φ : Formula Atom} (h_ax : Axiom φ)
    (_h_fc : h_ax.minFrameClass ≤ FrameClass.Metric)
    (M : TemporalModel D Atom) (t : D) : Satisfies M t φ := by
  cases h_ax with
  | discrete_symm_fwd => exact discrete_symm_fwd_sound M t
  | discrete_symm_bwd => exact discrete_symm_bwd_sound M t
  | discrete_propagate_fwd => exact discrete_propagate_fwd_sound M t
  | discrete_propagate_bwd => exact discrete_propagate_bwd_sound M t
  | density _ => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | dense_indicator => exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])
  | imp_k => exact axiom_sound (.imp_k _ _ _) (FrameClass.base_le _) M t
  -- … all remaining Base axioms delegate to `axiom_sound … (FrameClass.base_le _)`, exactly
  --    as in `axiom_sound_dense` (DenseSoundness.lean:91–124).
```

**Verified**: `axiom_sound (Atom := Atom) .serial_future (FrameClass.base_le _) M t` type-checks
under `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]` with **no explicit
`NoMaxOrder`/`NoMinOrder`** — Mathlib synthesizes them. So the Base-axiom delegation block copies
straight from `axiom_sound_dense` with only the frame-class name changed. The `density`/
`dense_indicator` cases are discharged by `absurd` because `.Dense ≰ .Metric`.

Duality case: `soundness_metric`'s `temporal_duality` branch needs
`swap_valid_of_valid_metric` (mirror of `swap_valid_of_valid_dense`,
`DenseSoundness.lean:141–151`), which transfers a metric-valid φ to its `swapTemporal` via the
`OrderDual` model. **Verified**: `OrderDual D` preserves all six instances
(`AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`, `Nontrivial`, `NoMaxOrder`, `NoMinOrder`),
so `swap_valid_of_valid_metric`'s hypothesis re-instantiates at `OrderDual D`. `swapTemporal`
swaps `untl↔snce` and `allFuture↔allPast` and fixes `bot`/`top`, so the four metric axioms are
swap-duals in matched pairs (`symm_fwd ↔ symm_bwd`, `propagate_fwd ↔ propagate_bwd`) — but the
soundness proof does not depend on that fact; it goes through `OrderDual` exactly like Dense.

### 4. Plumbing + `BX⁺` abbreviation

No new plumbing: `DerivationTree fc`, `Temporal.Derivable fc`, `Temporal.DerivFc fc`,
`Temporal.ThDerivableFc fc` are all already parameterized over `FrameClass` and work at `.Metric`
out of the box. Add only:

```lean
/-- `BX⁺` derivability: derivability at the metric frame class `FrameClass.Metric`. -/
@[nolint dupNamespace]
def Temporal.BXPlusDerivable (φ : Formula Atom) : Prop :=
  Temporal.ThDerivableFc FrameClass.Metric φ
```

plus `soundness_thderivable_metric : BXPlusDerivable φ → Satisfies M t φ` over the metric domain.
**Organizational note**: `DerivFc`/`ThDerivableFc` currently live in `Metalogic/DenseMCS.lean`
(frame-class-generic definitions housed in a "Dense" file). Importing `DenseMCS` from the new
`MetricSoundness` module works but pulls dense-completeness baggage; the cleaner option is to put
the `BXPlusDerivable` abbreviation in the new `MetricSoundness.lean` and `import DenseMCS` only
for `ThDerivableFc`. Relocating `DerivFc`/`ThDerivableFc` to a neutral module is a nice-to-have,
not required, and is arguably out of scope (avoid scope creep).

## Mandatory ripple: exhaustive `cases h_ax with` sites

Adding four `Axiom` constructors forces updates at the **two** existing exhaustive matches (a
missing-cases compile error otherwise). These are the ONLY two such sites in `Cslib/Logics/Temporal`
(confirmed: `grep -rn "cases h_ax with"`; and `density`/`dense_indicator` — the marker
constructors preceding the new ones — appear in only four files, of which only these two are
exhaustive matches; `DenseCompleteness.lean` only *constructs* `.dense_indicator`, it does not
match exhaustively):

1. **`Metalogic/Soundness.lean:78` `axiom_sound`** (Base). Add four cases discharged by
   `exact absurd _h_fc (by simp [Axiom.minFrameClass, LE.le])` (since `.Metric ≰ .Base`),
   identical to the existing `density`/`dense_indicator` cases at lines 325–326.
2. **`Metalogic/DenseSoundness.lean:88` `axiom_sound_dense`** (Dense). Add four cases discharged
   the same way (since `.Metric ≰ .Dense`).

No tableau, MCS, decidability, or chronicle file matches exhaustively on the whole `Axiom`
inductive (verified — the `AxiomMatcher`/`Tableau/Defs.lean` hits reference `minFrameClass` or
construct specific axioms, they do not `cases` over all constructors).

## Module wiring

- New file: `Cslib/Logics/Temporal/Metalogic/MetricSoundness.lean`, `public import
  Cslib.Logics.Temporal.Metalogic.Soundness` (and `import DenseMCS` if `ThDerivableFc` is used
  there). Begins with `import Cslib.Init` implicitly via the import chain — confirm the first
  import resolves `Cslib.Init` transitively (every existing sibling does).
- Add `public import Cslib.Logics.Temporal.Metalogic.MetricSoundness` to
  `Cslib/Logics/Temporal/Metalogic.lean` (barrel, currently lines 9–28).
- Run `lake exe mk_all --module` to update `Cslib.lean` (new file), and
  `lake exe checkInitImports` to confirm the `Cslib.Init` import.

## Verification evidence (all `lake env lean`, exit 0)

1. `OrderDual D` preserves `AddCommGroup`/`LinearOrder`/`IsOrderedAddMonoid`/`Nontrivial`/
   `NoMaxOrder`/`NoMinOrder` under the metric hypotheses (`inferInstance` for each). → duality
   case is sound.
2. `NoMaxOrder D` and `NoMinOrder D` are **auto-synthesized** from
   `[AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D] [Nontrivial D]` (`by infer_instance`).
3. `axiom_sound .serial_future (FrameClass.base_le _) M t` type-checks under the metric
   hypotheses with no explicit serial instances. → Base-axiom delegation works.
4. `discrete_symm_fwd_sound` and `discrete_propagate_fwd_sound` fully proved in the temporal
   `Satisfies` semantics (ported from the bimodal arithmetic). → novel-axiom soundness is
   sorry-free.

Scratch files used for verification are under the session scratchpad (not committed).

## Zero-debt / lint-prevention notes

- **No sorry, no vacuous defs.** All four soundness proofs are genuine (two already written and
  compiled); `BXPlusDerivable` is a real `Prop` abbreviation, not `def X := True`.
- **docBlame**: every new declaration (four axiom constructors, `FrameClass.Metric` note, the
  soundness theorems, `axiom_sound_metric`, `soundness_metric`, `soundness_thderivable_metric`,
  `swap_valid_of_valid_metric`, `BXPlusDerivable`) needs a house-style docstring.
- **defLemma**: soundness results are `Prop`-valued → use `theorem`, not `def` (they already are).
- **defsWithUnderscore**: `BXPlusDerivable` must be lowerCamelCase (no underscore). Inductive
  constructor names (`discrete_symm_fwd` etc.) are exempt (constructors, not top-level defs) and
  match the mandated names.
- **dupNamespace**: `Temporal.BXPlusDerivable` inside `namespace Cslib.Logic.Temporal` needs
  `@[nolint dupNamespace]` (mirror `Temporal.ThDerivableFc`, `DenseMCS.lean:66`).
- **unusedSectionVars**: keep the `Atom`/`D` variables minimal; `_h_fc` is intentionally unused
  in the delegated cases (prefix with `_`, as the existing code does).
- **simpNF**: no new `@[simp]` lemmas are required; do not add any.
- **CI**: `lake build` → `lake exe checkInitImports` → `lake lint` → `lake exe lint-style` →
  `lake test`; run `lake exe cache get` first, `lake exe mk_all --module` after adding the file.

## Tactic Survey (advisory)

The soundness proofs are term-style with explicit `calc` ordered-group arithmetic — do NOT
replace with `omega`/`aesop`/`simp`-only: ordered *abelian group* subtraction (`sub_lt_self`,
`sub_pos`, `add_lt_add_left`, `sub_add_cancel`, `add_sub_sub_cancel`, `sub_sub_cancel`,
`sub_lt_sub_right`) is not linear-integer arithmetic, and the bimodal originals already settled
the exact lemma spine. `omega` does not apply (abstract ordered group, not `ℤ`/`ℕ`).
`infer_instance` is the right tool for the serial/`OrderDual` instance obligations (verified).
The `FrameClass` instance extensions rely on `cases … <;> simp_all [LE.le]` /
`… <;> infer_instance`, which already generalize to the new constructor.

## Risks & recommendation

- **Risk (low)**: the two exhaustive-match updates are mechanical but mandatory; forgetting one
  is a hard compile error (self-announcing), not a silent gap.
- **Risk (low)**: `import` layering for `ThDerivableFc` from `DenseMCS` — if the implementer
  wants to avoid the dense dependency, keep `BXPlusDerivable` defined via
  `Nonempty (DerivationTree FrameClass.Metric [] φ)` inline instead of routing through
  `ThDerivableFc`. Both are fine.
- **Naming risk (cosmetic)**: the `discrete_*` axiom names describe metric *uniformity*, not
  discreteness. Keep the names (task-mandated, bimodal parity) but make docstrings say
  "metric uniformity / homogeneity of ordered-abelian-group time".
- **Recommendation**: proceed to plan/implement. Phase suggestion: (P1) `FrameClass.Metric` +
  four axioms + `minFrameClass`, then fix the two exhaustive matches → `lake build` green;
  (P2) `MetricSoundness.lean` with the four `*_sound` proofs + `axiom_sound_metric`; (P3)
  `swap_valid_of_valid_metric` + `soundness_metric` + `soundness_thderivable_metric` +
  `BXPlusDerivable`; (P4) barrel wiring + full CI. Each phase is one agent run and independently
  green-committable.

## Source anchors (durable)

- Temporal axioms/frame class: `Cslib/Logics/Temporal/ProofSystem/Axioms.lean:40–260`.
- Dense layering template: `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean`.
- Base soundness (delegation target): `Cslib/Logics/Temporal/Metalogic/Soundness.lean:74–326,
  406–435`.
- Bimodal uniformity-axiom soundness (arithmetic to port):
  `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean:451–511`.
- Metric domain constraints: `Cslib/Logics/Bimodal/Semantics/TaskFrame.lean` +
  `Cslib/Logics/Bimodal/Semantics/Validity.lean:49–55`.
- Frame-class plumbing: `Cslib/Logics/Temporal/ProofSystem/Derivation.lean:50`,
  `Cslib/Logics/Temporal/ProofSystem/Derivable.lean:35`,
  `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean:60,67`.
- Root-cause literature (from task 445, archived): `Burgess1984` §6.1 (metric tense = ordered
  abelian group time), `Xu1988` Thm 2.9 (successor not U,S-definable) — grounds *why* these four
  axioms are the ordered-abelian-group validities.
