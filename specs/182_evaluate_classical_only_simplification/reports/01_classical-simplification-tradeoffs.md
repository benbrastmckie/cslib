# Research Report: Should Modal/Temporal/Bimodal Remain Classical-Only?

## Task 182 — evaluate_classical_only_simplification

### The Question

Tasks 173-178 added primitive `and`/`or` constructors across all four logic layers to enable intuitionistic and minimal variants. Tasks 179-181 propose adding primitive `dia`, `allFuture`, `allPast` for the same reason. This task asks: is the intuitionistic direction worth pursuing for Modal/, Temporal/, and Bimodal/, or should these layers remain classical-only — and if so, should we revert the `and`/`or` additions to keep them simple?

There are three options on the table:

1. **Full intuitionistic path**: Keep `and`/`or` primitive, add `dia`/`allFuture`/`allPast` (tasks 179-181), build intuitionistic variants of all systems
2. **Classical-only, keep primitives**: Keep `and`/`or` as primitive constructors (status quo after tasks 173-178) but don't add more primitives, don't build intuitionistic variants
3. **Classical-only, revert to abbreviations**: Revert `and`/`or` to Lukasiewicz abbreviations in Modal/Temporal/Bimodal (keeping them primitive only in Propositional where the three-tier completeness requires them)

### Arguments for Full Intuitionistic Path (Option 1)

**Mathematical completeness**: A library called "Computer Science Library" should cover the logics that matter in CS. Intuitionistic modal logic (IS4 in particular) connects to:
- Type theory (Fitch-style modal types, Davies-Pfenning)
- Staged computation (MetaML)
- Constructive reasoning about distributed systems
- Topological semantics (IS4 = interior operator on topological spaces)

**Architectural consistency**: The Propositional layer already supports three tiers (minimal/intuitionistic/classical). Having the upper layers locked to classical creates an asymmetry — the extension hierarchy promises that Modal extends Propositional, but it only extends Classical Propositional.

**Research value**: Intuitionistic tense logic with the bimodal combination is genuinely novel territory. A formalized library covering this space would be a meaningful contribution.

**Upstream direction**: Upstream CSLib chose diamond as primitive and negation as primitive — design choices that lean toward logic-neutrality rather than classical optimization.

### Arguments for Classical-Only (Options 2 or 3)

**Practical usage**: The existing 15 modal systems, temporal logic, and bimodal logic with decidability/separation theorems are all classical. No current user or downstream project needs intuitionistic modal logic in CSLib.

**Maintenance cost**: Each primitive constructor multiplies maintenance burden across every refactor. The and/or propagation (tasks 173-178) required 74 files changed, 4607 insertions, ~20 agent dispatches across the Bimodal layer alone. The dia/G/H expansion (tasks 179-181) would be similar. Every future change to the Formula type repeats this cost.

**Performance**: More constructors = slower builds, larger proof terms, more exhaustiveness cases. The Bimodal layer with 11 constructors would have ~40% more match cases than the current 8, and `encodeNat` injectivity grows quadratically (64 → 121 case pairs).

**Proof redundancy**: In classical systems, `◇A ↔ ¬□¬A` and `GA ↔ ¬F¬A` are theorems. Having both as constructors means every classical proof about ◇ must be stated separately from the equivalent ¬□¬ form, even though they're interchangeable.

**Research maturity**: Intuitionistic temporal logic is not well-standardized. Building a formalized library for something where the mathematical foundations are still being debated risks building on shifting ground.

**Scope creep**: The original five-primitive refactor (task 173) was motivated by concrete problems — the Propositional completeness proofs needed real disjunction for prime theories. The Modal/Temporal/Bimodal propagation was a consistency requirement. But the intuitionistic modal/temporal extension is a new research direction, not a fix for existing problems.

### The Middle Ground: Keep and/or, Skip dia/G/H (Option 2)

This is the current state after tasks 173-178. The argument:

**and/or are already done**: The propagation is complete, the build is clean, and the constructors serve a purpose even classically — pattern matching on `Formula.and φ ψ` is clearer than pattern matching on `Formula.imp (Formula.imp φ (Formula.imp ψ Formula.bot)) Formula.bot`.

**and/or don't hurt much**: Going from 6 to 8 constructors (adding and/or) is a modest increase. Going from 8 to 11 (adding dia/allFuture/allPast) is proportionally larger and adds constructors that are truly redundant in classical logic.

**Preserves future optionality**: If intuitionistic modal logic becomes important later, the and/or foundation is already in place. Adding dia/G/H on top of an already-primitive and/or is easier than doing everything at once.

**Propositional consistency**: The and/or constructors match the Propositional layer's primitive set, so the embedding `Propositional → Modal` is a clean injection on all constructors. Reverting and/or in Modal would mean the embedding maps primitive constructors to abbreviations, which is semantically correct but architecturally ugly.

### The Revert Option (Option 3)

Arguments for reverting and/or in Modal/Temporal/Bimodal (keeping them primitive only in Propositional):

**Minimize blast radius**: The Propositional layer is small (~20 files) and genuinely needs primitive and/or for the three-tier completeness. The upper layers are large (Modal: 55, Temporal: 37, Bimodal: 127) and don't currently use the intuitionistic features.

**Simpler proofs**: Many Bimodal proofs were simpler with the Lukasiewicz encoding because `A ∧ B` was just `¬(A → ¬B)`, which is a nested `imp` — and `imp` already had all the proof infrastructure (deduction theorem, MCS implication property, etc.). With primitive `and`/`or`, every proof that worked via the encoding needed explicit and/or helpers (mcs_or_resolve, etc.).

**Embedding still works**: The `FromPropositional` embedding can map Propositional's primitive `and`/`or` to Modal's derived `and`/`or` (abbreviations). The embedding is still semantically correct — it's a homomorphism at the logical level even if not at the constructor level.

**Against reverting**: This would mean re-doing the 74-file refactor in reverse — a large effort to remove working code. The and/or cases are now part of every pattern match and every induction proof. Removing them is not just deleting lines; it's restructuring proofs back to the encoding-based versions.

### Cost Comparison

| Option | Immediate cost | Ongoing cost | Expressiveness |
|--------|---------------|-------------|---------------|
| 1. Full intuitionistic | ~20 tasks (179-181 + intuitionistic systems) | High (11 constructors everywhere) | Maximum |
| 2. Keep and/or, skip dia/G/H | 0 (already done) | Moderate (8 constructors) | Classical + future option |
| 3. Revert and/or in upper layers | ~5-10 tasks (reverse refactor) | Low (6 constructors in upper layers) | Classical only |

### Decision Criteria

The decision should weigh:

1. **Is intuitionistic modal/temporal logic a research goal for CSLib?** If yes → Option 1. If no → Option 2 or 3.
2. **Is the ~40% case-analysis overhead of 8 vs 6 constructors causing real problems?** If yes → Option 3. If no → Option 2.
3. **Is there a near-term use case for IS4, intuitionistic temporal, or constructive bimodal logic?** If yes → Option 1. If no → Option 2.
4. **How much does upstream compatibility matter?** Upstream uses `{atom, not, and, dia}` — both Options 1 and 2 have `and` as primitive (matching upstream), while Option 3 would diverge.

### Recommendation

This report presents the tradeoffs without making a recommendation. The decision depends on the project's research direction, which is a human judgment call. The task should be resolved by choosing one of the three options and either:
- Proceeding with tasks 179-181 (Option 1)
- Closing tasks 179-181 as unnecessary (Option 2)
- Creating revert tasks and closing 179-181 (Option 3)
