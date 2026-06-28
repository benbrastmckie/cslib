# Task 345 — Teammate B Findings (Alternative Approaches / Prior Art)

Focus: existing typeclass-to-inclusion bridge patterns in CSLib, how `minimal`/`IPL`/`CPL`
sets are built, whether the 8-witness bridge can be derived "for free", and adaptable prior
art from sibling logics.

## Key Findings

### 1. The exact template already exists — copy `IsIntuitionistic` / `isIntuitionisticIff`

`Defs.lean` already implements precisely the typeclass <-> inclusion bridge the task asks for,
twice. The new `IsMinimal` should be a third instance of this established 4-part pattern:

1. A `@[scoped grind]` class with the schema witnesses as membership fields
   (`Defs.lean:165-167` `IsIntuitionistic`, `:174-176` `IsClassical`).
2. A `@[scoped grind =]` iff-theorem proved by a one-word `grind`
   (`Defs.lean:169-171` `isIntuitionisticIff : IsIntuitionistic T ↔ IPL ⊆ T := by grind`;
   `:178-180` `isClassicalIff`).
3. Membership instances for the canonical set (`Defs.lean:182-186`).
4. Monotone propagation via `@[scoped grind →]` extension theorems proved by `grind`
   (`Defs.lean:188-196` `instIsIntuitionisticExtention` / `instIsClassicalExtention`,
   signature `{T T'} [IsClassical T] (h : T ⊆ T') : IsClassical T'`).

Every sub-deliverable of task 345 maps 1:1 onto a line of this template. The `omit
[DecidableEq Atom] in` prefix on each theorem (`Defs.lean:169,178,188,193`) should be carried
over — the bridge does not need decidable equality.

### 2. CRITICAL structural constraint: `minimal` is NOT `MPL = ∅`, and import order forces a design choice

There is a semantic trap. On the ND/Defs substrate, minimal logic is `MPL := ∅`
(`Defs.lean:153-154`) because the conjunction/disjunction/implication rules are *primitive ND
constructors*. On the Hilbert substrate the same content is 8 *axiom schemas*
(`MinPropAxiom`, `Axioms.lean:126-150`). The task's `minimal` set must be the **8 Hilbert
schemas**, not `∅`:

- If `minimal := ∅`, then `minimal ⊆ AxiomTheory Axioms` is vacuously `True`, but
  `MinimalAxioms Axioms` is not always true — so bridge (2) would be false. Hence `minimal`
  must contain the 8 schemas.

This collides with file ordering. The import chain is
`Defs.lean` -> `Axioms.lean` (defines `MinPropAxiom`) -> ... -> `Equivalence.lean`
(defines `AxiomTheory`, `MinimalAxioms`). `Defs.lean:9-14` imports only `Init`, `Connectives`,
and Mathlib — it has **no access to `MinPropAxiom` or `AxiomTheory`**. Therefore:

- `minimal` cannot be defined in `Defs.lean` as `AxiomTheory MinPropAxiom` (both are downstream).
- To co-locate `minimal` with `IsIntuitionistic` in `Defs.lean`, you would have to **re-encode
  all 8 schemas inline** (a union of 8 `Set.range`s) — duplicating `MinPropAxiom`'s content,
  which violates CSLib's reuse-first / DRY philosophy.

**Recommendation (placement):** Define `minimal` and `IsMinimal` **downstream** (in
`Equivalence.lean`, or `Axioms.lean` for `minimal` + the class), as
`minimal := AxiomTheory (@MinPropAxiom Atom)`, reusing the existing inductive. This is DRY,
import-feasible, and semantically correct. The mild cost is that `IsMinimal` is not physically
next to `IsIntuitionistic`; that is acceptable and arguably more honest (minimal strength is a
Hilbert-axiom notion, whereas `IPL`/`CPL` are single-schema ND sets). Teammate A's "primary
direct implementation" should be checked against this constraint — a naive plan that drops
`IsMinimal` into `Defs.lean` next to the others will not compile.

### 3. The 8 witnesses can be derived "for free" — no hand-proving 8 range lemmas

Two reuse facts collapse the whole task to a single ~3-line lemma.

(a) `Theory Atom = Set (Proposition Atom) = (Proposition Atom → Prop)`
(`Defs.lean:142`). `MinimalAxioms` is a class on a *predicate*
`Axioms : Proposition Atom → Prop` (`Equivalence.lean:114`). Because a `Set` is defeq to its
membership predicate, **`MinimalAxioms (T : Theory Atom)` already typechecks** and its 8 fields
(`h_K : ∀ φ ψ, Axioms (φ.imp (ψ.imp φ))`, etc.) reduce to membership facts
`(φ.imp (ψ.imp φ)) ∈ T`. So `IsMinimal T` need not be a new hand-rolled 8-field class — it can
be `MinimalAxioms (T : Theory Atom)` (def/abbrev), or a fresh class that is provably equivalent.

(b) `mem_axiomTheory` is `Iff.rfl` and `@[simp]` (`Equivalence.lean:88-93`), so
`φ ∈ AxiomTheory Axioms` is *definitionally* `Axioms φ`.

Combining (a)+(b) with `Set.setOf_subset_setOf`
(`Mathlib.Data.Set.Basic`: `{a | p a} ⊆ {a | q a} ↔ ∀ a, p a → q a`, verified via loogle) and
`Set.setOf_subset` (`setOf p ⊆ s ↔ ∀ x, p x → x ∈ s`):

```
minimal ⊆ AxiomTheory Axioms
  = AxiomTheory MinPropAxiom ⊆ AxiomTheory Axioms      -- defn of minimal
  ↔ ∀ φ, MinPropAxiom φ → Axioms φ                     -- setOf_subset_setOf
  ↔ MinimalAxioms Axioms                               -- (★) one lemma
```

The single load-bearing lemma is **(★) `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ`**.
- Forward: `intro h φ hφ; cases hφ <;> first | exact h.h_K .. | exact h.h_S .. | ...`.
- Backward: `intro h; exact ⟨fun φ ψ => h _ (.implyK φ ψ), fun φ ψ χ => h _ (.implyS ..), ...⟩`.

This is mechanically identical to the existing `MinPropAxiom.toIntPropAxiom`
(`Axioms.lean:155-165`), which proves `∀ φ, MinPropAxiom φ → IntPropAxiom φ` by `cases h with
| implyK .. => exact .implyK .. | ...`. That theorem is the **direct prior-art template** for
the `cases`-side of (★). So both bridge (1) and bridge (2) reduce to (★) plus a `setOf_subset`
rewrite — no 8 separate `Set.range` subset proofs needed.

### 4. Monotone propagation infrastructure already exists and is reused in practice

- The extension-theorem pattern (`instIs*Extention`) is the propagation infra; replicate it as
  `instIsMinimalExtention {T T'} [IsMinimal T] (h : T ⊆ T') : IsMinimal T'`.
- Real consumers exist: `AxiomAdmissibility.lean:228-231` builds `IsIntuitionistic (IPL ∪ CPL)`
  / `IsClassical (IPL ∪ CPL)` *via* `instIsIntuitionisticExtention Set.subset_union_left` and
  `instIsClassicalExtention Set.subset_union_right`. `Glivenko.lean:106-111` provides the
  same union instances directly. These show the propagation lemmas are load-bearing, so adding
  `instIsMinimalExtention` plugs `IsMinimal` into existing union/subset usage for free.
- For the monotone proof itself, `grind` suffices in the existing cases; if the inductive
  `cases` defeats `grind` for `IsMinimal`, fall back to: `intro` the witnesses and chain through
  `h` (membership monotone under `⊆`), or rewrite via the (★) lemma then apply `h`.

### 5. Name-collision check (clear)

`grep` shows **no** existing `IsMinimal`, `def minimal`, or `abbrev minimal` in
`Cslib/Logics/Propositional/`. Note the *distinct* `MinTheory` (`MinLindenbaum.lean:53-55`) is
a *deductive-closure* predicate (closed under `MinPropAxiom` derivation), unrelated to the
8-schema set — do not conflate. `minimal`/`IsMinimal` are free names.

### 6. Sibling-logic prior art (Modal / Bimodal)

The cleanest analogue is `Modal/Cube.lean:101-122` (`k_subset_d`, `k_subset_t`, ...), a family
of `⊆` subsumption theorems between axiom sets `K`, `D`, `T`, `B`, `Four`, `Five` — the same
"strength by inclusion of axiom sets" idiom the task wants, proved by short tactic scripts. It
confirms the inclusion-encoding is the house style for logic strength across CSLib, but it does
*not* add a typeclass<->inclusion bridge, so `Defs.lean`'s `IsIntuitionistic` remains the
superior template. Bimodal's `deductiveClosure`/`subset_deductiveClosure`
(`RRelation.lean:154`) is closure infra, not schema-set inclusion — not directly adaptable.

## Recommended Approach

1. **Reuse, don't re-encode.** Define (downstream, in `Equivalence.lean`):
   `def minimal : Theory Atom := AxiomTheory (@MinPropAxiom Atom)` and either
   `abbrev/def IsMinimal (T : Theory Atom) := MinimalAxioms (T : _ → Prop)` or a fresh
   `@[scoped grind]` class mirroring `IsIntuitionistic` whose 8 fields are membership versions
   of `MinimalAxioms`'.
2. **Prove the single core lemma (★)** `MinimalAxioms P ↔ ∀ φ, MinPropAxiom φ → P φ` by
   `constructor` + `cases`/constructor, cloning `MinPropAxiom.toIntPropAxiom`
   (`Axioms.lean:155-165`).
3. **Derive both bridges from (★)** via `Set.setOf_subset` / `Set.setOf_subset_setOf` and the
   `@[simp] mem_axiomTheory` reduction:
   - (1) `IsMinimal T ↔ minimal ⊆ T`
   - (2) `MinimalAxioms Axioms ↔ minimal ⊆ AxiomTheory Axioms`
   Try `by grind` first (matching `isIntuitionisticIff`); if the inductive case-split defeats
   `grind`, use the explicit `(★)` + `setOf_subset` chain.
4. **Add `instIsMinimalExtention`** by the `instIsIntuitionisticExtention` template
   (`Defs.lean:188-191`); attach `@[scoped grind →]`.
5. **Do NOT place `minimal`/`IsMinimal` in `Defs.lean`** unless you accept duplicating the 8
   schemas there (rejected on reuse-first grounds). Flag this to the planner as the main
   divergence from a naive "copy IsIntuitionistic in place" plan.

Zero-debt note: this plan is fully `sorry`-free and `axiom`-free; (★) is concrete and the
bridges are pure rewriting. No deferral patterns required.

## Evidence / Examples

| Claim | Evidence (file:line) |
|-------|----------------------|
| 4-part typeclass<->inclusion template exists | `Defs.lean:165-196` |
| `isIntuitionisticIff` proved by `grind` | `Defs.lean:169-171` |
| `isClassicalIff` proved by `grind` | `Defs.lean:178-180` |
| Monotone propagation theorems | `Defs.lean:188-196` |
| Propagation lemmas actually consumed | `AxiomAdmissibility.lean:228-231`, `Glivenko.lean:106-111` |
| `MPL := ∅` (why `minimal` ≠ MPL) | `Defs.lean:153-154` |
| `IPL`/`CPL` built as `Set.range` | `Defs.lean:157-162` |
| `MinPropAxiom` = 8 schema inductive | `Axioms.lean:126-150` |
| `MinimalAxioms` = 8-field class on predicate | `Equivalence.lean:114-132` |
| `Theory = Set = predicate` (defeq trick) | `Defs.lean:142`; `Equivalence.lean:114` |
| `AxiomTheory` defn + `@[simp] mem_axiomTheory` (`Iff.rfl`) | `Equivalence.lean:85-93` |
| `cases`-style schema-inclusion prior art | `Axioms.lean:155-165` (`MinPropAxiom.toIntPropAxiom`) |
| Import chain Defs -> Axioms -> Equivalence | `Axioms.lean:9`; `Defs.lean:9-14`; `Equivalence.lean:9-11` |
| `Set.setOf_subset` / `Set.setOf_subset_setOf` exist | loogle (Mathlib.Data.Set.Basic) |
| `Set.range_subset_iff` exists (for union encoding) | loogle (Mathlib.Data.Set.Image) |
| No existing `IsMinimal`/`minimal`; `MinTheory` is distinct | grep `Cslib/Logics/Propositional/`; `MinLindenbaum.lean:53-55` |
| Sibling inclusion idiom | `Modal/Cube.lean:101-122` |

## Confidence Level

**High** for: the template identification (#1), the import-ordering constraint and the
`minimal ≠ ∅` semantics (#2), the defeq/`setOf_subset` "for free" reduction (#3), and the
existence of all cited Mathlib lemmas. These are grounded in direct file reads and loogle.

**Medium** for: whether a bare `by grind` closes the two bridge iffs (the existing template
uses single-schema `Set.range` sets; the 8-constructor inductive case-split may need the
explicit `(★)` + `setOf_subset` fallback). I did not execute a build of the proposed lemmas
(team research, no edits), so the exact tactic is the one open risk — but the explicit fallback
proof is mechanical and low-risk.
