# Teammate D Findings: Long-Term Strategy and Creative Approaches

**Task 229**: Typeclass Diamond Inheritance Resolution for CSLib BimodalConnectives
**Focus**: Horizons — long-term strategic implications and creative approaches

---

## Key Findings

### 1. Current CSLib Design Avoids the Diamond Correctly but at a Cost

The current `Connectives.lean` design (post-PR #648) uses this structure:

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F
class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F
class TemporalConnectives (F : Type*) extends FutureTemporalConnectives F, HasSince F
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

`BimodalConnectives` avoids the diamond by not extending `TemporalConnectives`. This is explicitly noted in the source comment: "rather than extending `TemporalConnectives`, to avoid a typeclass diamond." The cost is that a `BimodalConnectives` instance does not automatically satisfy `TemporalConnectives`. Any lemma parameterized by `[TemporalConnectives F]` cannot be directly applied to a `[BimodalConnectives F]` context without an explicit instance bridge.

### 2. Lean 4 Diamond Resolution Mechanics (Current State, 2025-2026)

Lean 4 uses **tabled typeclass resolution**: every candidate solution is memoized, preventing exponential blowup and loops in diamond-shaped hierarchies. The Lean 4.19.0 release (May 2025) changed field elaboration so default values now fully respect the structure resolution order in diamond inheritance — each field has at most one default value definition. This is a correctness improvement, not a fundamental change to the diamond problem itself.

The core issue remains: when two inheritance paths reach the same class with *different field implementations*, Lean picks one path deterministically but the unused path's instances become inaccessible. When paths produce *definitionally equal* results (the "morally canonical" case), Lean's optimization fires and no further instances are tried — this is safe and efficient. CSLib's diamond would be dangerous precisely because `TemporalConnectives` via `ModalConnectives` would produce a different `HasBot`/`HasImp`/`HasUntil` source field than `TemporalConnectives` directly — even if propositionally equal, not definitionally so.

### 3. `class abbrev` — The Key Tool for This Problem

Lean 4 provides `class abbrev`, which creates a bundled name for multiple atomic classes with automatic instance synthesis:

```lean
class abbrev C <params> := D_1, ..., D_n
-- expands to:
class C <params> extends D_1, ..., D_n
attribute [instance] C.mk
```

The crucial difference from `class C extends D_1, ..., D_n` is that **the constructor is automatically registered as an instance**, so any type that already has instances of `D_1` through `D_n` automatically gains `C` for free, with no explicit `instance` declaration needed.

Mathlib uses this in exactly the pattern relevant to CSLib — see `IsAffineMonoid` in `Mathlib/Algebra/AffineMonoid/Basic.lean`:

```lean
class abbrev IsAffineMonoid (M : Type*) [CommMonoid M] : Prop :=
  IsCancelMul M, Monoid.FG M, IsMulTorsionFree M
```

If CSLib used `class abbrev BimodalConnectives (F : Type*) := ModalConnectives F, HasUntil F, HasSince F`, then any `F` with separate instances for these three classes would *automatically* be a `BimodalConnectives` instance. More importantly, writing a lemma `[BimodalConnectives F]` would not prevent it from being applied where `[TemporalConnectives F]` and `[ModalConnectives F]` are both available.

**However**: `class abbrev` works best for *purely propositional* bundles (no new methods). BimodalConnectives currently adds no new fields, making it an ideal candidate.

### 4. Future Hierarchy Growth — The Diamond Multiplier Effect

Each new modal logic extension that extends `ModalConnectives` creates a new diamond candidate with any future bimodal-style combination. Plausible near-term CSLib expansions:

| New Bundle | Extends | Diamond Risk |
|---|---|---|
| `EpistemicConnectives` | `ModalConnectives` + knowledge `K_i` operators | `BimodalEpistemicConnectives` would risk K-i/box diamond |
| `DeonticConnectives` | `ModalConnectives` + obligation `O`/permission `P` operators | Same pattern |
| `DynamicConnectives` (PDL) | `ModalConnectives` + program action operators `[π]` | Extends box, risks doubly-modal diamonds |
| `HybridConnectives` | `ModalConnectives` + nominals + `@_i` satisfaction operators | Nominals interact with box, compounding risk |

Without a systematic solution, each new intersection logic requires a manually diamond-avoiding bundled class. With three or more such extensions, the combinatorial space of "which intersection do I need?" becomes unwieldy.

The roadmap currently lists only Bimodal as requiring multi-modal combinations. But `Logics/` structure already anticipates future logics (issue #646 proposes first-order, second-order, separation logic). The hierarchy decision made now will be inherited or broken by each of these.

### 5. Mathlib Compatibility Analysis

CSLib deliberately departs from Mathlib conventions in several ways (e.g., logic-domain naming, the `HasBox`/`HasUntil`/`HasSince` atomic class approach). Mathlib has no modal or temporal logic hierarchy to conflict with; the risk is at the *algebraic* and *order* hierarchy level if CSLib ever formalizes algebraic semantics.

The key Mathlib lesson (from "Use and Abuse of Instance Parameters"): Mathlib historically suffered from diamonds being propositionally equal but not definitionally equal, causing typeclass application failures that required explicit casts. The fix was to ensure all instances in the diamond produce definitionally equal results — either by structural sharing or by careful default derivation. CSLib's current diamond-avoidance strategy sidesteps this entirely, but at the cost of breaking the `TemporalConnectives ← BimodalConnectives` implicit relationship.

**If CSLib contributes to Mathlib**: The logic hierarchy would be entirely novel to Mathlib and would not conflict with existing Mathlib algebraic typeclasses. The main Mathlib style requirement is that the hierarchy should not cause instance resolution slowdowns — and the atomic `Has*` class approach is well-suited for this.

### 6. Lean 4 Recent Evolution (2025-2026) — No Structural Change

Lean 4.19.0 (May 2025) improved diamond handling in elaboration but did not change the fundamental typeclass inheritance model. The PR #10178 ("improved class_abbrev") was still in draft as of recent checking. No Lean 4 RFC proposing structural changes to class/structure inheritance that would affect this design was found. The `structure` vs `class` distinction remains: `structure` fields are definitionally accessible via projection, `class` fields via instance synthesis — both subject to the same diamond mechanics.

Scoped instances (`scoped instance`) remain a tool for limiting instance visibility to namespaces, but they do not help with diamond inheritance per se — they help with preventing instance conflicts between different libraries, not with resolving structural field equality.

---

## Strategic Recommendations

### Recommendation 1: Adopt `class abbrev` for All Bundled Classes (High Impact)

Replace:
```lean
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

With:
```lean
class abbrev BimodalConnectives (F : Type*) := ModalConnectives F, HasUntil F, HasSince F
```

And similarly for `TemporalConnectives`, `FutureTemporalConnectives`, `ModalConnectives`, `PropositionalConnectives`. Under `class abbrev`, a formula type with instances for all the atomic `Has*` classes automatically gets all bundled class instances. This means:

- A `BimodalFormula` that has `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` instances gains `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`, `FutureTemporalConnectives`, and `PropositionalConnectives` automatically.
- **The diamond disappears entirely** because `BimodalConnectives` is just a name for a set of atomic class constraints, not a new structural node.
- **Future extensions are free**: `EpistemicConnectives := ModalConnectives F, HasKnowledge F` can be added without any diamond analysis, because the instances compose from atoms.

**Trade-off**: `class abbrev` does not support adding new methods. If any bundled class ever needs its own methods (not just an atomic `Has*` class), it must become a true `class extends`. Currently no bundled CSLib class has its own methods, so the trade-off does not yet apply.

### Recommendation 2: Establish a Bridge Instance for `TemporalConnectives` Even Now

Even under the current design, add an explicit bridge:

```lean
instance instTemporalConnectivesOfBimodal [BimodalConnectives F] : TemporalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce
```

This costs one declaration per intersection but gives downstream users the ability to apply temporal lemmas directly to bimodal contexts. Without this, users must manually provide all temporal instances in bimodal proofs.

### Recommendation 3: Plan Future Extensions Using the Atomic Pattern

For any new modal extension (`EpistemicConnectives`, `DeonticConnectives`), follow this pattern:
1. Define an atomic `HasKnowledge`/`HasObligation` class (one operator per class).
2. Define the bundled class using `class abbrev` over the atomic classes plus `ModalConnectives`.
3. Register formula instances against the atomic classes only; bundled instances are automatic.

This scales linearly: N new operators = N new `Has*` classes + N `class abbrev` bundles. No diamond analysis needed.

### Recommendation 4: The "All-Atomic" Radical Alternative — Viable but Not Recommended Now

The fully unbundled design — using only `Has*` classes with type abbreviations:

```lean
abbrev TemporalConnectives F := HasBot F × HasImp F × HasUntil F × HasSince F
```

— eliminates all diamond problems at the cost of verbose instance declarations. Mathlib's `Unbundled/` directories show this approach is viable (see `Mathlib.Algebra.Order.Monoid.Unbundled.Defs`). The Mathlib assessment is that unbundling is "unergonomic" for end users — each lemma application site must supply all constraints explicitly. For a logic library used in formal proofs, this verbosity is meaningful: `[HasBot F] [HasImp F] [HasBox F] [HasUntil F] [HasSince F]` is 5 constraints vs one `[BimodalConnectives F]`.

The all-atomic approach is unusual in the Lean ecosystem for *bundled interface classes* (as opposed to algebraic properties), and would make CSLib significantly harder to use than comparable Mathlib modules. The `class abbrev` middle path achieves most of the same benefits with better ergonomics.

---

## Creative Approaches

### Creative Approach 1: Instance Priority to Prefer Canonical Paths

For any unavoidable diamond (e.g., if `class abbrev` is not adopted and bridge instances are needed), use instance priority:

```lean
instance (priority := 200) instTemporalOfBimodal [BimodalConnectives F] : TemporalConnectives F := ...
```

Higher priority ensures Lean finds this instance first and avoids searching alternative paths. This is the Mathlib convention for "preferred instances" in diamond-shaped hierarchies.

### Creative Approach 2: Namespace-Scoped Instances for Competing Extensions

If CSLib adds both `EpistemicConnectives` and `DeonticConnectives` as extensions of `ModalConnectives`, and ever needs a combined `EpistemicDeonticConnectives`, use `scoped instance` within the combined logic's namespace:

```lean
namespace EpistemicDeonticLogic
scoped instance [EpistemicConnectives F] [DeonticConnectives F] : ModalConnectives F := ...
end EpistemicDeonticLogic
```

This prevents the combined instance from polluting global instance search while making it available inside the namespace.

### Creative Approach 3: A "Logic Signature" Structure for Multi-Modal Intersections

For higher-order multi-modal combinations (PDL + temporal, epistemic + deontic), consider a Coq-style "record of records" pattern:

```lean
structure BimodalSignature (F : Type*) where
  modal : ModalConnectives F
  temporal : TemporalConnectives F
```

This is not a typeclass but a bundled proof term. Lemmas parameterized by `BimodalSignature F` are not in the instance synthesis graph, eliminating diamond risk entirely. The downside: notation and tactic integration require explicit field projections. This approach is best for internal metalogic arguments, not end-user API.

### Creative Approach 4: Lessons from Coq's Canonical Structures

Coq's canonical structures system handles the diamond differently: each type has a *single* canonical structure associated with a given projection, and all alternative derivations must agree or be registered as aliases. The Lean equivalent is the "morally canonical instance" assumption — Lean's synthesis optimization fires only when all instances are assumed equivalent. CSLib can adopt this as a policy: **every bundled class instance must be definitionally derived from the atomic `Has*` fields**, ensuring that all synthesis paths produce definitionally equal instances. This policy check can be enforced by `#check @BimodalConnectives.toHasBot` — if the projection is definitionally `HasBot.bot`, the instance is canonical.

### Creative Approach 5: Proof-of-Concept for `class abbrev` Approach in a Branch

Before committing to `class abbrev`, test it in a branch:
1. Change `class PropositionalConnectives` to `class abbrev PropositionalConnectives (F : Type*) := HasBot F, HasImp F`
2. Check if all existing instances still compile (they should, since `class abbrev` is strictly more permissive for instance synthesis)
3. Test that a bimodal formula type with `ModalConnectives` and `HasUntil`/`HasSince` instances automatically gains `BimodalConnectives` and `TemporalConnectives`
4. Run `lake test` to verify nothing breaks

This is a non-breaking change for downstream users who previously needed `[PropositionalConnectives F]` — they still get it, plus additional automatic instances.

---

## Confidence Levels

| Claim | Confidence |
|---|---|
| Current BimodalConnectives diamond avoidance is correct but loses `TemporalConnectives` relationship | **High** — directly verified from source |
| `class abbrev` auto-registers constructor as instance | **High** — from official Lean docs and Mathlib examples |
| `class abbrev` eliminates diamond for bundled-with-no-methods classes | **High** — follows from automatic instance synthesis |
| Lean 4.19.0 did not change the fundamental diamond problem | **High** — from release notes and docs |
| Future `EpistemicConnectives` etc. will require diamond analysis without systematic fix | **High** — follows from hierarchy structure |
| `class abbrev` is non-breaking for downstream users | **Medium** — needs empirical branch test; theoretically sound |
| Mathlib compatibility not endangered by CSLib's atomic class approach | **Medium** — based on no Mathlib modal/temporal hierarchy to conflict with; could change if CSLib upstream contributions require Mathlib interface alignment |
| `scoped instance` can isolate multi-modal intersection instances effectively | **Medium** — Lean 4 supports this but real-world ergonomics for logic libraries unclear |

---

## Summary Table

| Design Question | Current CSLib | Recommended Path | Long-Term Implication |
|---|---|---|---|
| BimodalConnectives diamond | Avoided by not extending TemporalConnectives | `class abbrev` → no diamond | Scales to N future multi-modal combinations |
| Bridge to TemporalConnectives | None (missing) | Add explicit bridge instance | Required for lemma reuse across Temporal/Bimodal |
| Future EpistemicConnectives | Not yet in scope | Atomic `HasKnowledge` + `class abbrev` | No diamond analysis needed if atomic pattern used |
| All-atomic alternative | Not used | Viable but unergonomic | Last resort if `class abbrev` has unexpected limitations |
| Mathlib compatibility | N/A (no Mathlib modal hierarchy) | Follow atomic `Has*` style | Compatible; no conflict expected |

---

## Sources

- [Multiple-inheritance hazards in dependently-typed algebraic hierarchies (arXiv:2306.00617)](https://arxiv.org/pdf/2306.00617)
- [Lean 4.19.0 release notes (lean-lang.org)](https://lean-lang.org/doc/reference/latest/releases/v4.19.0/)
- [Lean 4 Class Declarations documentation (lean-lang.org)](https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/)
- [Lean 4 Instance Synthesis documentation (lean-lang.org)](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/)
- [Tabled Typeclass Resolution (arXiv:2001.04301)](https://arxiv.org/pdf/2001.04301)
- [Use and abuse of instance parameters in the Lean mathematical library (arXiv:2202.01629)](https://arxiv.org/pdf/2202.01629)
- [Mathlib Unbundled Monoid Defs (mathlib4_docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Monoid/Unbundled/Defs.html)
- [CSLib PR #648 — feat(Logics/Propositional): five-primitive formula type](https://github.com/leanprover/cslib/pull/648)
- [CSLib PR #649 — feat(Logics/Temporal): temporal formula type](https://github.com/leanprover/cslib/pull/649)
- [CSLib PR #607 — feat(Logic): logical operators by fmontesi](https://github.com/leanprover/cslib/pull/607)
- [Mathlib IsAffineMonoid using class abbrev](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/AffineMonoid/Basic.lean)
