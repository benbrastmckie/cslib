# Teammate D Findings: Strategic Horizons for Upstream Contribution

## Key Findings

### 1. Divergence Between Fork and Upstream is Already Significant

The upstream `Cslib/Logics/Propositional/` directory contains only two things:
- `Defs.lean` (same file as in the fork)
- `NaturalDeduction/Basic.lean`

The fork has added everything else: `Semantics/`, `Metalogic/`, `ProofSystem/`, and all of `Modal/`, `Temporal/`, `Bimodal/`. There is no `Semantics/` subdirectory upstream at all. This means PR #648 is proposing the first semantics files. The stakes for getting conventions right are high — these become canonical for all subsequent PRs.

### 2. PR #607 Introduces a Competing Typeclass Architecture for Operators

PR #607 (fmontesi, CHANGES\_REQUESTED) refactors `Modal/Basic.lean` to register `HasAnd`, `HasOr`, `HasImpl`, `HasNot`, `HasBox`, `HasDiamond` instances rather than using scoped notation directly. It also applies the same changes to `Propositional/Defs.lean`.

**Critical conflict with PR #648**: The fork's `Modal/Basic.lean` already uses `ModalConnectives` (a typeclass defined in `Cslib.Foundations.Logic.Connectives`), while the upstream's PR #607 adds separate `Has*` classes defined in `Cslib/Foundations/Logic/Operators/` as individual files (`And.lean`, `Box.lean`, etc.). These are competing approaches to the same goal of generic logical operators.

**The tension**: The fork's `ModalConnectives` bundles `bot + imp + box` together (used in `ProofSystem/Axioms.lean` across Modal/Temporal/Bimodal), whereas PR #607's approach has one class per operator. ctchou commented on PR #607 proposing 3 files: `Modal`, `Tensor`, and `Propositional` — not the 9 separate files that PR #607 currently creates.

**Impact on PR #648**: Any semantics files added now will need updating when PR #607 is eventually merged (or when this fork's equivalent of PR #607 lands). But this is not a blocker since semantics files don't import the operator typeclasses.

### 3. PR #587 is a DRAFT That Overlaps Significantly with PR #648's Semantics Layer

PR #587 (thomaskwaring, DRAFT) proposes:
- `Foundations/Logic/Model.lean`: typeclasses `Models α β`, `ParamModels α β`, `InterpModels α β`
- Defines `Valuation` for PL as an instance of this framework
- ctchou asked: "would an abbreviation for `Atom → H` (where H is a `GeneralizedHeytingAlgebra`) suffice?" vs thomaskwaring's bundled `HeytingModel Atom` type

The existing `Basic.lean` in PR #648 defines `Valuation := Atom → Prop` (an abbreviation, not a typeclass instance). This is simpler and will likely survive even if PR #587's framework lands, since `Prop` is a specific `HeytingAlgebra`/`GBA`. However, any generic semantics framework from PR #587 that eventually merges will make the standalone `Valuation` definition redundant or need to be replaced by an instance declaration.

**Impact on PR #648**: Low immediate risk, but medium strategic risk. The recommended merger of `Basic.lean` and `Bool.lean` should be framed as a temporary consolidation pending #587's resolution.

### 4. The Prop-Valued Evaluate is Non-Negotiable for Subsequent Modal/Temporal/Bimodal PRs

The existing modal `Satisfies` in `Modal/Basic.lean` uses `Prop`-valued truth, and `Temporal.Satisfies` and `Bimodal.truthAt` do as well. The `PL.Evaluate` function in `Semantics/Basic.lean` is the propositional specialization of this: it plays the same role as `Satisfies` without worlds. The upstream `Modal/Basic.lean` already has this pattern.

**The canonical model argument** (from the existing report) is decisive: completeness proofs use `fun p => atom p ∈ S` where `S` is a maximal consistent set. This is inherently `Prop`-valued. The fork's `Metalogic/StrongCompleteness.lean` and `Modal/Metalogic/Completeness.lean` both depend on this pattern. ctchou's suggestion that `Bool.lean` alone suffices would break the canonical model construction.

**The winning argument in the PR response**: "Prop-valued `Evaluate` is the degenerate case of `Modal.Satisfies` for the world-free case. Every subsequent PR (Modal, Temporal, Bimodal) uses Prop-valued satisfaction and the same canonical MCS construction. Bool.lean is needed only for the computable layer (DPLL/Matthew Doty). Bool alone cannot support completeness proofs."

### 5. The Merged `Semantics.lean` Design Sets Critical Precedents for Modal/Temporal PRs

The fork's `Modal/Basic.lean` (which is already significantly ahead of upstream) uses Prop-valued `Satisfies` with the same `{atom, bot, imp, box}` four-constructor design. Temporal and Bimodal have analogous structures. The merged `Semantics.lean` from PR #648 should:
- Be explicit that `Valuation := Atom → Prop` is intentional and consistent with `Modal.Satisfies`
- Reference Avigad chapters 2-3 (not Chagrov/Zakharyaschev) as ctchou requested
- Add a `## Design Notes` section explaining the Prop vs Bool layering — this same rationale will need to appear in every subsequent logic PR

**Positive observation**: The existing module docstring structure in `Bool.lean` already has a `## Design Notes` section explaining the two-layer architecture. This needs to survive the merge and be promoted to the top-level merged file's docstring.

### 6. PR Sequencing Strategy for Full Upstream Contribution

The upstream currently has: `Modal/Basic.lean` (Montesi's version, HML-style, no proof system), `Propositional/Defs.lean` (Waring's version, four constructors), and is adding the operator typeclasses.

The fork has: everything, including full soundness and completeness for propositional (classical, intuitionistic, minimal), modal (13 systems), temporal, and bimodal.

**Recommended upstream PR sequence**:

1. **Wait for #536** (ready to merge): refactors `IsClassical`/`IsIntuitionistic` — the fork's `Defs.lean` extends this work with the five-primitive design and the fork must stay compatible
2. **PR #648 (current)**: Add `Semantics/Semantics.lean` (merged file) — establishes the Prop+Bool layer
3. **Propositional Metalogic PR**: `Metalogic/Soundness.lean` + `Metalogic/StrongCompleteness.lean` — self-contained, no Modal dependency
4. **Modal Semantics PR**: This fork's expanded `Modal/Basic.lean` vs upstream's current version need reconciliation. The fork adds `box` as primitive, `ModalConnectives` typeclass, derived `diamond`, many frame-condition theorems. This is a large refactor of existing upstream code — highest coordination risk
5. **Modal Metalogic PR**: The 13 systems' soundness/completeness. Should come after Modal Semantics is accepted
6. **Temporal PR**: Syntax + Semantics + ProofSystem + Metalogic (no upstream overlap)
7. **Bimodal PR**: Depends on Temporal being upstream first

**Cannot parallelize**: Modal PR must reconcile with fmontesi's existing `Modal/Basic.lean` in upstream. This is the highest-risk coordination point. The fork uses `{atom, bot, imp, box}` as primitives; upstream uses `{atom, not, and, diamond}` as primitives. These are fundamentally different formula type designs and must be resolved before any modal metalogic PR can land.

### 7. The Formula Primitive Conflict: The Single Biggest Strategic Risk

The upstream's `Modal/Basic.lean` (Montesi) uses `{atom, not, and, diamond}` with `box` and `or` and `impl` as derived. The fork's `Modal/Basic.lean` uses `{atom, bot, imp, box}` with `diamond`, `and`, `or`, `neg` as derived. These cannot coexist — any PR adding modal metalogic to upstream must first resolve this.

**The fork's design is better for proof systems**: Hilbert-style axioms and the K axiom are naturally stated with `box` as primitive and `imp` as primitive. Necessitation (`⊢ φ → ⊢ □φ`) directly applies to the `box` constructor. With diamond-as-primitive, necessitation becomes indirect.

**Strategic recommendation**: The Modal Semantics PR must explicitly propose replacing Montesi's four-constructor `Proposition` with the fork's `{atom, bot, imp, box}` five-constructor design, with a clear justification referencing Chagrov/Zakharyaschev §3.1 for the box-first convention. This is a potential flashpoint — fmontesi (Montesi) is an active reviewer/contributor who may resist changing his formula type design.

PR #607 further complicates this: it adds `HasBox`/`HasDiamond` typeclass instances to Montesi's `Modal/Basic.lean`. If PR #607 merges before the modal rewrite PR, the rewrite becomes harder.

### 8. What PR #648 Should Avoid to Prevent Painting into a Corner

**Avoid**: Removing `BoolEvaluate` from the merged file just because ctchou prefers the Bool-only approach. The fork's entire metalogic depends on the Prop layer. Removing it now means re-adding it when completeness PRs land.

**Avoid**: Defining `Valuation` as a typeclass instance for PR #587's `Models` framework prematurely. Wait until #587 is resolved (it's currently DRAFT).

**Avoid**: Referencing this fork's `Cslib.Foundations.Logic.Connectives` in `Semantics.lean`. The upstream doesn't have this module yet (it's in PR #648 itself via `Defs.lean`'s import chain). `Semantics.lean` should import only `Defs` for simplicity.

**Avoid**: Adding the Kripke semantics to the merged file. `Semantics/Kripke.lean` is separate and involves `IForces`, `IValid`, `MValid` which are intuitionistic and not relevant to the classical/Bool layer ctchou is commenting on.

### 9. Conventions PR #648 Should Establish

The merged `Semantics.lean` should establish these conventions explicitly:

- `Valuation := Atom → Prop` (Prop-valued, not Bool)
- `BoolValuation := Atom → Bool` (Bool-valued, computable)
- `Evaluate : Valuation → Proposition → Prop` (Prop-valued evaluation)
- `BoolEvaluate : BoolValuation → Proposition → Bool` (Bool-valued, computable)
- Bridge: `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ`
- Decidability: `instDecidableBoolEvaluate`
- Reference: Avigad §2-3 (not Chagrov/Zakharyaschev)

These exact naming conventions (`Evaluate`, `BoolEvaluate`, `Valuation`, `BoolValuation`) should be declared stable for subsequent PRs since they appear extensively in `FromPropositional.lean` and will appear in completeness proofs.

## Recommended Approach

### Immediate (PR #648 fix)

1. Merge `Basic.lean` and `Bool.lean` into `Semantics/Semantics.lean` (or just `Semantics.lean` if `Semantics/` becomes a flat directory)
2. Update all references from `ChagrovZakharyaschev1997` to `avigad2023` (Avigad chapters 2-3)
3. Add explicit `## Design Notes` section justifying the two-layer (Prop + Bool) architecture with reference to completeness proofs and DPLL
4. Do NOT touch `Kripke.lean` or `SemanticConsequence.lean` — they are separate concerns

### The PR Response to ctchou

Frame the Prop-valued layer not as redundancy with Bool, but as the *primary* semantic layer: "Bool is the computable fragment; Prop is the metatheoretically primary layer needed for completeness." Then position Bool as an add-on for decidable evaluation, not as the replacement.

### Medium-term (post-PR #648)

Before submitting Modal PRs: open a Zulip thread proposing to refactor `Modal/Basic.lean` to use `{atom, bot, imp, box}` primitives (matching the fork's design). Get fmontesi/ctchou buy-in before writing code. This is the highest-risk coordination point for the entire upstream contribution effort.

### Long-term sequencing

```
#536 merges → PR #648 (Semantics) → Propositional Metalogic PR
→ Modal Semantics (primitive refactor, coordinate with fmontesi)
→ Modal Metalogic (13 systems)
→ Temporal PR
→ Bimodal PR
```

Do not submit Temporal or Bimodal PRs until the Modal primitive formula type is resolved upstream. Both Temporal and Bimodal's `FromPropositional` modules and embedding theorems depend on the modal primitive design.

## Evidence/Examples

**Evidence for Prop necessity**: `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` at line ~31 uses `fun p => atom p ∈ S` as the canonical valuation, which is `Prop`-valued. `Cslib/Logics/Modal/Metalogic/Completeness.lean` uses the same MCS pattern.

**Evidence for formula type conflict**: Upstream `Modal/Basic.lean` line 46: `| diamond (φ : Proposition Atom)` as primitive constructor. Fork's `Modal/Basic.lean` line 70: `| box (φ : Proposition Atom)` as primitive, with diamond derived at line 99.

**Evidence for PR #607 complication**: PR #607 adds `instance : HasDiamond (Proposition Atom)` on Montesi's diamond-as-primitive formula type. If this merges before the fork's modal rewrite PR, a second refactor of instances will be needed.

**Evidence for PR #587 low urgency**: PR #587 is DRAFT, has had no activity suggesting imminent merge, and ctchou's comments question its design. Treating it as a future concern (not a blocker) is appropriate.

## Confidence Level

- **High confidence**: Prop layer is necessary for completeness (direct dependency chain in codebase)
- **High confidence**: Modal primitive formula type conflict is the largest strategic risk
- **Medium confidence**: PR sequencing recommendation (depends on upstream merge timelines not in our control)
- **Medium confidence**: PR #607 will be redesigned before merging (based on ctchou's comment proposing only 3 files vs 9)
- **Low confidence**: PR #587 timeline and final design (still DRAFT with open design questions)
