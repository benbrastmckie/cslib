# Teammate B Findings: Alternative Approaches and Design Tensions in PR #648

**Task**: Review PR #648 (feat/propositional-v2) — alternative design debate analysis
**Sources**: Zulip thread, PR #648, PR #587 (thomaskwaring), PR #607 (fmontesi), PR #536 (merged)

---

## Summary of Design Tensions

Five major design tensions are active in the PR discussion:

1. Bot as primitive vs bot as atom ([Bot Atom])
2. Prop vs Bool evaluation for semantics
3. GeneralizedHeytingAlgebra (GHA) polymorphic evaluation
4. Connective typeclass organization: per-operator vs bundled
5. IsIntuitionistic/IsClassical: theory-centric vs inference-system-centric

---

## Tension 1: Bot as Primitive vs [Bot Atom]

### Positions

**Upstream main (thomaskwaring)**: Bot is represented as `[Bot Atom]` — a `Bot` instance on the atom type. Upstream `Defs.lean` has 3 constructors (and, or, impl) with `instBotProposition [Bot Atom] : Bot (Proposition Atom) := ⟨.atom ⊥⟩`.

**PR #648 (benbrastmckie)**: Adds a `bot` primitive constructor, making the inductive 5-way (atom, bot, imp, and, or).

**ctchou**: "I like the idea of adding ⊥ as a primitive." (CHANGES_REQUESTED review, supporting primitive bot)

**thomaskwaring (PR comment)**: Raises four objections:
1. In minimal logic, ⊥ behaves exactly like an atomic formula
2. Minimal logic works without ⊥ at all (Curry-Howard reference)
3. Extra constructor makes proofs more verbose (cited: separate Kripke fields for atoms vs ⊥)
4. Non-bot-preserving maps (`WithBot.some` for conservativity) are important

**Matthew Doty**: "I do agree with @Ching-Tsun Chou about a separate bot constructor."

### Technical Analysis

**Who is right?**

Both positions are technically defensible, but primitive bot wins on practical grounds for benbrastmckie's use case. Here is the core trade-off:

**Primitive bot advantages** (benbrastmckie's arguments):
- `Proposition.subst` gets a natural recursive case: `subst f .bot = .bot`. With atom-encoded bot, `subst f (.atom ⊥)` = `f ⊥`, which maps bottom to an arbitrary formula — requiring additional constraints in downstream code that needs to preserve bottom.
- Eliminates `[Bot Atom]` from every signature that mentions ⊥. For completeness proofs in modal, temporal, and bimodal logics (benbrastmckie's broader goal), these constraints accumulate significantly.
- Standard treatment in Avigad (2022), Gentzen (1935), Prawitz (1965).
- `Bot (Proposition Atom)` and `Top (Proposition Atom)` instances are unconditional (no atom constraint needed).

**Atom-encoded bot advantages** (thomaskwaring's arguments):
- Conservativity result: "IPL is conservative over MPL for ⊥-free formulas" can be stated cleanly using `WithBot.some : Atom → WithBot Atom` — this map forgets bottom, and non-bottom-preserving maps remain available.
- No extra constructor case in structural induction/recursion.
- Domain-theory analogy: even in domains with ⊥, functions that don't preserve it are important.

**Assessment** (Confidence: HIGH): ctchou's review approval of primitive bot, combined with Matthew Doty's agreement, signals that the community finds primitive bot acceptable. Thomaskwaring's conservativity argument is valid but not fatal — the `WithBot.some` embedding still works with primitive bot (you can always choose to embed only at atoms). The main concrete cost (extra cases in recursion) is real but minor. The PR #648 revision correctly addresses this by deferring semantics — the bot-primitive approach is the right call for a library that spans propositional, modal, temporal, and bimodal logics.

---

## Tension 2: Prop vs Bool Evaluation

### Positions

**benbrastmckie**: `Evaluate : (Atom → Prop) → Proposition Atom → Prop` for canonical model construction. The Lindenbaum-Zorn MCS construction uses `fun p => atom p ∈ S`, which is inherently `Prop`-valued. Prop evaluation is also uniform with modal/temporal/bimodal Kripke semantics.

**Matthew Doty**: Wants `Atom → Bool` models for DPLL/SAT decision procedures. Argues that `Bool` is more portable for computational use.

**ctchou**: "I don't understand why we need both Semantics/Basic.lean and Semantics/Bool.lean. I think the latter alone is enough." Suggested using `decide` on the canonical valuation.

**benbrastmckie's solution**: Both layers — `BoolEvaluate : (Atom → Bool) → Proposition Atom → Bool` alongside `Evaluate`, bridged by `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ`.

**Matthew Doty counter**: Suggests using `noncomputable def canonicalValuation := fun p => decide (Proposition.atom p ∈ S)` to collapse to Bool-only, making the truth lemma `Evaluate (canonicalValuation S) φ = true ↔ φ ∈ S`.

### Technical Analysis

**Who is right?**

Matthew Doty and ctchou are correct that Bool-only is *sufficient* for classical soundness/completeness. However, benbrastmckie's uniformity argument is *stronger for CSLib's architecture*.

**The core conflict**: There are two legitimate use cases:
1. **Completeness proofs** (benbrastmckie, thomaskwaring): The canonical model for MPL/IPL uses set membership, which is `Prop`. Forcing Bool requires `Classical.propDecidable` or noncomputable machinery, and the truth lemma becomes `v φ = true ↔ φ ∈ S`, which is less natural than `v φ ↔ φ ∈ S`.
2. **Decision procedures** (Matthew Doty): DPLL needs computable Bool evaluation. Using `decide` on Prop-valued set membership works but introduces a `noncomputable` annotation and conceptually conflates model-theoretic completeness with computational decidability.

**thomaskwaring's resolution** (via GHA — see Tension 3 below) offers a third path that transcends this debate.

**ctchou's "Bool only" suggestion** is incorrect in the general case: it works for CPL (classical logic, BooleanAlgebra) but breaks for IPL (intuitionistic) and MPL (minimal) where the canonical model is inherently Prop/GHA-valued.

**Assessment** (Confidence: HIGH): The correct resolution is thomaskwaring's GHA approach: define `Evaluate` over any GeneralizedHeytingAlgebra, then recover both Bool and Prop as special cases. This was correctly deferred to a follow-up PR, which is the right sequencing. For the follow-up, GHA is superior to both single-evaluator approaches.

---

## Tension 3: GeneralizedHeytingAlgebra Polymorphic Evaluation

### Positions

**thomaskwaring** (Zulip, PR #587 Model.lean): Proposes defining evaluation over any `GeneralizedHeytingAlgebra`:
```lean
def HeytingModel.interp (M : HeytingModel Atom) : Proposition Atom → M.H
  | Proposition.atom x => M.v x
  | Proposition.and A B => M.interp A ⊓ M.interp B
  | Proposition.or A B => M.interp A ⊔ M.interp B
  | Proposition.impl A B => M.interp A ⇨ M.interp B
-- NO bot case -- uses bundled HeytingModel type with H : GHA
```

Completeness theorem:
```lean
theorem Theory.complete [Inhabited Atom] {A : Proposition Atom} :
    DerivableIn T A ↔
    ∀ {H : Type u} [GeneralizedHeytingAlgebra H] {v : Valuation Atom H}, (v ⊨ T) → v ⊨ A
```

This captures:
- Bool (classical, BooleanAlgebra ⊆ GHA)
- Prop (classical via Classical.propDecidable, intuitionistic via constructive semantics)
- Non-trivial finite Heyting algebras (needed for completeness of intuitionistic and minimal logic — single algebras don't suffice)

**Matthew Doty's counter-proposal**:
```lean
def Evaluate {Atom A : Type u} [HeytingAlgebra A]
    (v : Atom → A) : Proposition Atom → A
  | .atom p => v p
  | .bot => ⊥       -- maps Proposition.bot to algebra's ⊥
  | ...
```

Uses `HeytingAlgebra` (not `GeneralizedHeytingAlgebra`) so bot maps to the algebra's ⊥.

**thomaskwaring's objection** to Matthew Doty's version: "with that definition of evaluate completeness is no longer true for minimal logic."

### Technical Analysis

**Who is right?**

**thomaskwaring is correct** on the key technical point. Here is the argument:

- `GeneralizedHeytingAlgebra`: A lattice with Heyting implication (⇨) and ⊤, but NOT necessarily a ⊥ element.
- `HeytingAlgebra`: Extends GHA with an explicit ⊥.

For **minimal logic (MPL)** completeness via Lindenbaum-Tarski:
- The canonical Heyting algebra is the set of propositional equivalence classes under MPL-provable equivalence.
- In this algebra, `⊥` maps to the equivalence class of the formula `⊥` — which is NOT ⊥ in the algebra (MPL cannot prove ⊥ from ⊥ being false).
- If you use `[HeytingAlgebra A]` and map `Proposition.bot → ⊥_algebra`, you force models to falsify ⊥, which is the IPL condition (ex falso quodlibet), not the MPL condition.
- Result: Matthew Doty's `[HeytingAlgebra A]` definition gives IPL semantics, not MPL semantics.

For **intuitionistic logic (IPL)** completeness:
- You need to restrict to `[HeytingAlgebra A]` where models satisfy `v (⊥ → A) = ⊤` for all A.
- Or equivalently: `v ⊥ = ⊥_algebra` for all models.
- This is a class constraint on the algebra, not on the formula type.

The GHA approach handles all three levels uniformly:
- MPL: valid in all GHA models where `v ⊨ T` (no constraint on bot)
- IPL: valid in all GHA models where also `v (⊥ → A) = ⊤` for all A
- CPL: valid in all Boolean algebra models where also `v (¬¬A → A) = ⊤` for all A

**Subtlety about bot in GHA**: GHA does not have ⊥, so if `Proposition` has a primitive `bot` constructor, the `interp` function must either (a) omit the bot case (only possible if bot is atom-encoded) or (b) pass `⊥` in via a valuation that also maps `bot` — thomaskwaring's `HeytingModel` bundles the algebra and valuation but does not have a separate field for bot. This is actually a constraint on the design: if bot is a primitive Proposition constructor, the GHA evaluation function needs a way to interpret it. GHA doesn't have a canonical ⊥, so you need to either:
1. Put bot back as an atom (thomaskwaring's design), allowing `v bot = anything`
2. Add a separate `bot_val : H` field to the model structure with `v bot = bot_val`

This is precisely why thomaskwaring says "completeness is no longer true for minimal logic" with primitive bot + HeytingAlgebra evaluation — the standard interp definition maps `bot → ⊥_algebra`, which over-constrains the model.

**Assessment** (Confidence: HIGH): The GHA approach is technically superior for a library aiming to cover MPL/IPL/CPL uniformly. It also resolves the Prop/Bool tension as a special case. For implementation, with primitive bot in Proposition, the follow-up semantics PR should define `HeytingModel` with a separate `bot_val : H` field (or equivalently, extend the valuation to `Proposition.atom + Proposition.bot → H`).

---

## Tension 4: Connective Typeclass Organization

### Three competing approaches

**fmontesi (#607)**: One file per operator, flat structure:
- `Cslib/Foundations/Logic/Operators/And.lean` — `class HasAnd`
- `Cslib/Foundations/Logic/Operators/Box.lean` — `class HasBox`
- etc. (8 separate files total: And, Box, Diamond, Iff, Impl, Not, Or, Tensor)

**thomaskwaring (#587, Connectives.lean)**: Per-operator classes in one file:
- `class HasImpl`, `class HasAnd`, `class HasOr`, `class HasNot`
- Plus `instNotImplBot` — default negation instance from implication + bot
- Single `Cslib/Foundations/Logic/Connectives.lean`

**benbrastmckie (#648, Connectives.lean)**: Per-operator classes + bundled superclasses:
- `class HasBot`, `class HasImp`, `class HasAnd`, `class HasOr`, `class HasBox`, `class HasUntil`, `class HasSince`, `class HasNext`
- Bundled: `PropositionalConnectives extends HasBot, HasImp`
- Higher bundles: `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`

### Technical Analysis

**fmontesi's approach** is the most Mathlib-aligned (Mathlib also has `Min`, `Max`, `HImp` as separate typeclasses). Per-file organization allows fine-grained imports.

**thomaskwaring's approach** is simpler for the current scope (PL + Modal) but doesn't think ahead to Temporal/Bimodal.

**benbrastmckie's approach** is architecturally comprehensive but risks over-engineering at this stage. The bundled classes (`PropositionalConnectives`, `ModalConnectives`, etc.) are useful for benbrastmckie's cross-logic work but represent a design decision that should involve the broader CSLib community.

### Overlap and Conflict Analysis

PR #607 (fmontesi) and PR #648 (benbrastmckie) both define `class HasAnd`, `class HasImp`, `class HasOr`. These are **directly conflicting**: they cannot both be merged unless one defers to the other or they coordinate.

- fmontesi: `HasImpl` (using "Impl") in `Cslib.Foundations.Logic.Operators.Impl`
- benbrastmckie: `HasImp` (using "Imp") in `Cslib.Foundations.Logic.Connectives`
- thomaskwaring (#587): `HasImpl` (using "Impl")

Naming conflict: `imp` vs `impl` is not settled. The current upstream `Defs.lean` uses `impl` (thomaskwaring's convention), but PR #648 proposes `imp`.

**Assessment** (Confidence: HIGH): A merge conflict between #607 and #648 is certain if both are accepted. The resolution path: accept fmontesi's #607 operators as the canonical operator classes (they are more Mathlib-aligned and came first), then have #648 reference those operators rather than defining its own. benbrastmckie's bundled classes (`PropositionalConnectives`, `ModalConnectives`) are a separate contribution that could go on top of #607. The `imp` vs `impl` naming should be resolved in favor of whichever convention the community chooses in #607/#587.

---

## Tension 5: IsIntuitionistic/IsClassical — Theory-Centric vs Inference-System-Centric

### Positions

**PR #536 (merged, thomaskwaring)**: Changed `IsIntuitionistic` and `IsClassical` to be parameterized over `InferenceSystem S` rather than `Theory`. This was merged and is upstream.

**PR #648 (original)**: Had `IsIntuitionistic (Atom : Type u) (S : Type*) [InferenceSystem S (Proposition Atom)]` — aligned with #536.

**Local main branch (after merge)**: Has `class IsIntuitionistic (T : Theory Atom) where efq (A : Proposition Atom) : (⊥ → A) ∈ T` — reverted to theory-centric approach.

### Technical Analysis

The local main branch (benbrastmckie's fork) has diverged from the approach in PR #648. The local branch uses a theory-centric `IsIntuitionistic (T : Theory Atom)` that checks membership in the theory, while PR #648 targets `InferenceSystem S`.

**The theory-centric approach** is simpler and directly states what the theory contains. `isIntuitionisticIff` proves equivalence with `IPL ⊆ T`.

**The inference-system-centric approach** (PR #536, PR #648) is more general — it works for any inference system, not just axiomatic theories. This is needed for the ND system (whose "theory" is not directly a set of sentences in the same way).

**Assessment** (Confidence: MEDIUM): The local branch's theory-centric approach is a meaningful alternative that has been implemented with good support (`isIntuitionisticIff`, `instIsIntuitionisticExtension`). However, it may conflict with the spirit of PR #536 (which was specifically about making these typeclasses inference-system-independent). This tension should be explicitly raised with thomaskwaring in the PR review.

---

## Potential Conflicts Between #587, #607, and #648

| Conflict | Description | Resolution Path |
|----------|-------------|-----------------|
| HasImpl vs HasImp | #587 and #607 use `HasImpl`; #648 uses `HasImp` | Coordinate naming before merge |
| Connectives in separate files (#607) vs single file (#648) | Direct import conflict | Accept #607 operators; #648 Connectives should import and extend |
| `ModalConnectives` bundle in #648 | Not in #587 or #607 | No immediate conflict; can add later |
| `IsIntuitionistic` parameterization | Local main = theory-centric; #648 PR branch = IS-centric | Needs explicit coordination |
| HeytingModel definition | Both #587 and follow-up semantics will define this | PR sequencing can prevent conflict |

---

## What Approach Best Serves CSLib Long-Term?

**Recommendation** (Confidence: MEDIUM-HIGH):

1. **Accept primitive bot** — eliminates constraint accumulation across the entire logic stack (propositional, modal, temporal, bimodal). ctchou and Matthew Doty agree.

2. **Follow fmontesi's per-operator typeclass pattern (#607)** — most aligned with Mathlib conventions. benbrastmckie's `Connectives.lean` should be restructured to import from `#607`'s operator files and add bundled superclasses on top.

3. **Adopt thomaskwaring's GHA evaluation for the semantics follow-up** — technically necessary for MPL completeness and captures Bool/Prop as special cases. This requires either (a) reverting to atom-encoded bot (problematic for other reasons) or (b) adding a `bot_val` field to the model structure.

4. **Use `imp` naming consistently** — PR #648's `imp` is more consistent with Lean/Mathlib conventions (`hsub`, `himp` etc.) vs `impl` which is language-level. But this requires coordinating with thomaskwaring and fmontesi (currently using `impl`).

5. **Keep semantics in a separate PR** — thomaskwaring correctly identified that merging the Prop/Bool/GHA debate with the syntax PR blocks merge progress on the simpler foundational questions.

---

## Confidence Assessment

| Finding | Confidence |
|---------|-----------|
| Primitive bot is the right call given CSLib scope | HIGH |
| GHA evaluation is technically necessary for MPL completeness | HIGH |
| #607 and #648 will conflict if both merged as-is | HIGH |
| ctchou's "Bool only" suggestion is insufficient for non-classical | HIGH |
| Theory-centric vs IS-centric IsIntuitionistic tension exists | HIGH |
| imp vs impl naming preference | LOW (community decision) |
| GHA bot_val field requirement with primitive bot | HIGH |
| Optimal sequencing (#607 first, then #648) | MEDIUM |
