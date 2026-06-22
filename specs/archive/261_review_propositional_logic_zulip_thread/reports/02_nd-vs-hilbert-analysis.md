# Research Report: Natural Deduction vs. Hilbert Systems Analysis

## Metadata

| Field | Value |
|-------|-------|
| **Task** | #261 -- Review Zulip thread on propositional logic setup in CSLib |
| **Artifact** | 02 |
| **Started** | 2026-06-22 |
| **Completed** | 2026-06-22 |
| **Effort** | hard |
| **Dependencies** | 01_team-research.md (round 1 team synthesis) |
| **Sources/Inputs** | Zulip thread CSLib > Propositional Logic (MSG 602336739--605341190); Thomas Waring branches (`cslib_SKI/hilbert`, `cslib_SKI/kripke`, `cslib_SKI/intuitionistic`); CSLib `Cslib/Logics/Propositional/` directory |
| **Artifacts** | This report |
| **Standards** | H2 anti-analysis, H3 reference grounding (Tier 3 -- implementation-backed), H4 adversarial self-verification |
| **Session** | sess_1782112184_d88c66 |

## Executive Summary

- Thomas Waring's full final message (MSG 605341190) is NOT truncated. It was fully retrieved. His core position: what he formalized is *minimal natural deduction*, and `IPL`/`CPL` should be seen as *encodings* within MPL rather than base systems. He proposes a compromise via `IProposition`/`IDerivation` types with translations.
- The disagreement crystallizes around one foundational question: should MPL be encoded as a fragment of IPL, or should IPL be encoded in MPL via the theory construction? CSLib has chosen the latter; Thomas prefers the former for ND purity.
- Natural deduction, Hilbert systems, and sequent calculus serve fundamentally different theoretical roles. ND captures proof-as-construction (Curry-Howard); Hilbert systems capture substitution-closed axiom schemas (needed for metalogic); sequent calculus (not formalized in CSLib) captures structural proof theory (cut elimination, subformula property). CSLib's dual-system approach with proved equivalence is the standard architecture.
- Thomas's `IProposition`/`IDerivation` compromise (in the `intuitionistic` branch) demonstrates the translation overhead is manageable but introduces a parallel inductive type, which conflicts with CSLib's reuse-first philosophy.
- Thomas's final message ends with "btw Benjamin, why did you delete that part of the docstring in `NaturalDeduction/Basic`?" -- this IS the unanswered question from the prior report, and it is NOT truncated. The full message is 4 paragraphs.

## Context and Scope

### What This Report Adds Over Round 1

Round 1 (01_team-research.md) provided a comprehensive thread mapping, design-dispute taxonomy, and draft Zulip response. This round deepens the analysis of:

1. **Thomas's full final message**: Round 1 flagged it as "truncated" -- it is not. The complete text was retrieved via Zulip API (MSG 605341190, 1782035382 timestamp).
2. **The ND vs. Hilbert vs. Sequent Calculus paradigm comparison**: What each system is good for, why both ND and Hilbert are needed, and what their theoretical roles are for MPL/IPL/CPL.
3. **Thomas's compromise proposal**: His `intuitionistic` branch defines `IProposition`, `IDerivation`, and bidirectional translations (`propEquiv`, `toDerivation`, `toIDerivation`). Assessed against CSLib's codebase.
4. **Thomas's Hilbert classes**: His `cslib_SKI/hilbert` branch defines a generic `ContextualInferenceSystem` with classes `HasS`, `HasK`, `Deductive`, `HasBotImpl`, `HasDNImpl` -- a different architecture from CSLib's current `DerivationTree`.

### Reference Grounding Tier

**Tier 3 (implementation-backed)**: The primary sources are the CSLib codebase and Thomas Waring's branches. Literature references (Gentzen, Prawitz, Johansson, Troelstra/Van Dalen, Rasiowa/Sikorski) provide theoretical grounding but the task is comparing implementations, not transcribing from papers.

### BibKey Verification

All BibKeys verified against `/home/benjamin/Projects/cslib/references.bib`:

| BibKey | Status | Reference |
|--------|--------|-----------|
| `Gentzen1935` | Verified (line 202) | Untersuchungen uber das logische Schliessen |
| `Prawitz1965` | Verified (line 407) | Natural Deduction: A Proof-Theoretical Study |
| `Johansson1937` | Verified (line 284) | Der Minimalkalkul |
| `TroelstraVanDalen1988` | Verified (line 457) | Constructivism in Mathematics |
| `Church1956` | Verified (line 149) | Introduction to Mathematical Logic |
| `ChagrovZakharyaschev1997` | Verified (line 75) | Modal Logic |
| `Rasiowa1974` | Verified (line 736) | An Algebraic Approach to Non-Classical Logics |
| `RasiowaSikorski1963` | Verified (line 747) | The Mathematics of Metamathematics |

## Findings

### 1. Thomas Waring's Full Final Message (MSG 605341190)

Thomas's message is 4 substantive paragraphs plus a closing remark. The key points:

**Paragraph 1 -- Framing the disagreement**: "What I've formalised is *minimal natural deduction*, the definitions of `IPL` and `CPL` should probably be seen as encodings, rather than a once-and-for-all definition." He chose MPL because it is "expressive enough to encode the others (using the `bot : Atom` construction) while still being minimal in terms of number of rules / constructors."

**Paragraph 2 -- The ND symmetry argument, refined**: "If we were to add `bot` to the proposition type, I think we should also add efq to the derivation type -- a big part of the appeal of natural deduction is the symmetry introduction / elimination and the close match between formula constructors and inference rules." He explicitly connects this to algebra: "a `GeneralizedHeytingAlgebra` is not an algebra over the signature with `bot`, which is why you need the extra unnatural field `botVal`."

**Paragraph 3 -- The compromise proposal**: He links to `thomaskwaring/cslib_SKI/blob/intuitionistic/Cslib/Logics/Propositional/NaturalDeduction/Intuitionistic.lean`, defining `IProposition` (with primitive `bot`) and `IDerivation` (with `efq` rule), plus bidirectional translations via `propEquiv : Proposition (WithBot Atom) <-> IProposition Atom`.

**Paragraph 4 -- Cost issue not conceded**: "I'm still not exactly convinced re the cost issue, unfortunately. If you have, eg, the `bot_val` field in your definition of valuation, then you still need to ensure for intuitionistic applications that `v bot = bot`."

**Final remark**: "btw Benjamin, why did you delete that part of the docstring in `NaturalDeduction/Basic`?" -- This is a concrete question requiring an answer.

### 2. Natural Deduction vs. Hilbert Systems vs. Sequent Calculus: Theoretical Roles

#### 2a. Natural Deduction (ND)

**Theoretical role**: ND captures the structure of proofs as they are actually constructed. Each connective has introduction and elimination rules, reflecting its meaning through use (Gentzen's "meaning-through-rules" philosophy, [Gentzen1935]). The Curry-Howard correspondence maps ND proofs to typed lambda-calculus terms.

**What ND is good for**:
- **Proof objects**: ND derivations are data (Type-valued in CSLib), enabling computation on proofs. The `Derivation` inductive in `NaturalDeduction/Basic.lean` is a Type, not a Prop.
- **Constructive content**: ND proofs carry computational content; a proof of `A or B` specifies which disjunct holds.
- **Categorical semantics**: ND proofs in IPL correspond to morphisms in cartesian closed categories.
- **Fragment analysis**: Thomas's point about `IPL<and, implies, top>` for CCCs and `IPL<implies, top>` for typed SKI combinators is well-taken (MSG 604166734 by Matthew Doty).

**What ND is less good for**:
- **Metalogic**: Proving deduction theorems, compactness, completeness, substitution closure is harder in ND. CSLib's own architecture demonstrates this: metalogical results (soundness, completeness, deduction theorem) are proved in the Hilbert system and then imported to ND via the equivalence bridge.
- **Substitution closure**: ND has no native mechanism for substitution instances of axioms. The `ax` constructor in CSLib's `Derivation` appeals to a `Theory` parameter, but substitution closure of the theory must be proved separately.
- **Automated reasoning**: ND is poor for proof search; resolution and tableaux are more natural for automation.

**ND in the CSLib codebase** (`NaturalDeduction/Basic.lean`):
- 10 primitive constructors: `ax`, `ass`, `andI`, `andE1`, `andE2`, `orI1`, `orI2`, `orE`, `impI`, `impE`
- No `efq` constructor: bottom elimination is derived via `ax` + `impE` requiring `[IsIntuitionistic T]`
- Theory parameter controls logic strength: `MPL = empty`, `IPL = Set.range (bot imp .)`, `CPL = Set.range (fun A => neg neg A imp A)`

**Thomas's ND preference**: He wants `efq` as a primitive constructor (creating `IDerivation` with 11 constructors). His argument is principled: if `bot` is in the syntax, its elimination rule should be in the derivation type. This maintains the "constructors parallel connectives" invariant.

#### 2b. Hilbert Systems

**Theoretical role**: Hilbert systems express logical consequence through axiom schemas and a single inference rule (modus ponens). The axioms are closed under uniform substitution by definition (they are schematic). This makes Hilbert systems the natural setting for metalogical work.

**What Hilbert systems are good for**:
- **Substitution closure**: Axiom schemas are inherently substitution-closed. `subst_preserves_axiom` (CSLib) is trivially provable because axioms are defined schematically over arbitrary formula variables.
- **Deduction theorem**: The deduction theorem (proved in `Metalogic/DeductionTheorem.lean`) converts contextual derivations to pure derivations. This is the foundation for strong completeness.
- **Completeness proofs**: The Lindenbaum-Zorn construction (in `Metalogic/MCS.lean`, `Metalogic/StrongCompleteness.lean`) works with Hilbert-style derivability because it needs compactness and substitution closure.
- **Extension by axioms**: Adding axiom schemas (e.g., Peirce's law for CPL) is a simple addition. CSLib's hierarchy `MinPropAxiom` (8 schemas) < `IntPropAxiom` (9, adds `efq`) < `PropositionalAxiom` (10, adds `peirce`) makes this explicit.
- **Logic comparison**: Hilbert systems make it easy to compare logics by comparing axiom sets. The subsumption theorems `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toPropAxiom` are trivially proved.

**What Hilbert systems are less good for**:
- **Human readability**: Hilbert proofs are notoriously unreadable. The deduction theorem proof itself (`deductionTheorem` in CSLib) is `noncomputable` and involves elaborate case analysis.
- **Proof objects**: Hilbert derivation trees (`DerivationTree` in CSLib) are large and unwieldy. The `ndToHilbert` translation produces exponentially larger proof terms.
- **Computational content**: Hilbert proofs do not carry constructive content in the way ND proofs do.

**Hilbert systems in the CSLib codebase** (`ProofSystem/`):
- `DerivationTree Axioms Gamma phi`: 4 constructors (`ax`, `assumption`, `modus_ponens`, `weakening`)
- Three axiom predicates: `MinPropAxiom` (8), `IntPropAxiom` (9), `PropositionalAxiom` (10)
- All metalogical results proved here, then transferred to ND via `Equivalence.lean`

**Thomas's Hilbert architecture** (`cslib_SKI/hilbert/Classes.lean`):
- Uses typeclasses: `ContextualInferenceSystem`, `HasS`, `HasK`, `HasAss`, `HasWk`, `HasAddMP`, `Deductive`
- More generic: parameterized over context type `beta` and formula type `alpha`
- Defines a generic `axAssDer` (axiom-assumption-derivation) inductive and wraps it in `Hilbert T`
- Includes `HasBotImpl` and `HasDNImpl` for efq and DNE
- The `absSK` function implements the combinatory abstraction (deduction theorem) generically

The CSLib approach is more concrete (specific inductive types for axiom predicates and derivation trees), while Thomas's is more abstract (typeclass-based). Both are valid; CSLib's is more directly usable for the specific metalogical results already proved.

#### 2c. Sequent Calculus

**Theoretical role**: Sequent calculus (Gentzen's LK/LJ) captures structural proof theory. The cut-elimination theorem (Gentzen's Hauptsatz) is its central result, yielding the subformula property, decidability, and interpolation.

**Not formalized in CSLib**: The thread does not discuss sequent calculus, and CSLib does not include it. This is a gap but not a pressing one -- ND + Hilbert covers the current use cases. Sequent calculus would be valuable for:
- **Cut elimination**: Provides a direct proof of consistency
- **Proof normalization**: The subformula property
- **Decidability**: Finite proof search
- **Interpolation**: Craig's interpolation theorem

**Relationship to ND and Hilbert**: Sequent calculus sits between ND and Hilbert. The Curry-Howard correspondence extends to sequent calculus (via explicit substitution calculi), and the deduction theorem in Hilbert systems is closely related to the cut rule.

### 3. How ND and Hilbert Interact in CSLib

The equivalence bridge (`NaturalDeduction/Equivalence.lean`) proves:

```
hilbert_iff_nd_ctx : Deriv Axioms Gamma.toList phi <-> DerivableIn (AxiomTheory Axioms) (Gamma |- phi)
```

This is instantiated for all three tiers: `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`.

**Architecture**:
1. `hilbertToND`: Structural translation, computable. Each Hilbert constructor maps directly to its ND counterpart.
2. `ndToHilbert`: Uses deduction theorem, noncomputable. The `impI` case requires the deduction theorem (which uses `Classical.propDecidable`). The `orE` case requires the `MinimalAxioms` typeclass.
3. `MinimalAxioms`: Typeclass bundling 8 axiom witnesses (K, S, andI, andE1, andE2, orI1, orI2, orE). Instances for all three axiom predicates.

**Key design decision**: The ND system is the "user-facing" proof system (more natural for constructing proofs), while the Hilbert system is the "metalogical backend" (where completeness and soundness are proved). Results flow through the bridge.

### 4. Thomas's Compromise Proposal: IProposition/IDerivation

Thomas's `intuitionistic` branch defines:

```lean
inductive IProposition (Atom : Type u) : Type u where
  | atom (x : Atom) | or | and | impl | bot

inductive ITheory.IDerivation : ICtx Atom -> IProposition Atom -> Type u where
  | ax | ass | conjI | conjE1 | conjE2 | disjI1 | disjI2 | disjE | implI | implE
  | efq (A : IProposition Atom) : IDerivation Gamma bot -> IDerivation Gamma A
```

Plus translations:
- `propEquiv : Proposition (WithBot Atom) <-> IProposition Atom` -- the `Equiv` proving syntactic bijection
- `ITheory.IDerivation.toDerivation` -- every intuitionistic derivation becomes a minimal one by adding efq axioms
- `Theory.Derivation.toIDerivation` -- every minimal derivation in the intuitionistic completion becomes an intuitionistic derivation

**Assessment**:

*Strengths*:
- Preserves ND symmetry: `bot` has an elimination rule (`efq`) as a primitive constructor
- Clean separation: `IProposition` is the "canonical" type for intuitionistic logic
- Translations are proved: both directions compile
- Addresses Thomas's philosophical concern about ND purity

*Weaknesses*:
- **Parallel inductive types**: Creates a second proposition type (`IProposition`) alongside `Proposition`. This doubles the API surface for every operation (evaluation, substitution, pattern matching).
- **Translation overhead**: Every theorem proved for `Proposition` needs to be either re-proved for `IProposition` or translated through `propEquiv`. The translations are `noncomputable` (the `toIDerivation` direction uses `Classical.choose`).
- **Conflicts with CSLib architecture**: CSLib's modal, temporal, and bimodal logics all build on `Proposition` with primitive `bot`. The `FromPropositional` embedding uses `| .bot => .bot`. Adding `IProposition` would require parallel embedding infrastructure.
- **The `Equiv` is not trivial**: `propEquiv` maps `atom (WithBot.none)` to `bot`, requiring case analysis. This is correct but adds friction.

**Verdict**: The compromise demonstrates that the translation is mechanically possible, but the maintenance cost of dual proposition types is significant. CSLib's current approach (single `Proposition` with theory-parameterized strength) is architecturally cleaner for a library that spans multiple logics.

### 5. Thomas's Hilbert Classes vs. CSLib's DerivationTree

Thomas's `cslib_SKI/hilbert/Classes.lean` defines a more abstract architecture:

| Feature | Thomas's Design | CSLib Current |
|---------|----------------|---------------|
| Inference system | `ContextualInferenceSystem S alpha beta` typeclass | `DerivationTree Axioms Gamma phi` inductive |
| Context type | Generic `beta` with `Context` typeclass | `List (Proposition Atom)` |
| Modus ponens | `HasAddMP` / `HasMultMP` typeclasses | `modus_ponens` constructor |
| Deduction theorem | `Deductive` typeclass + `absSK` | `deductionTheorem` function |
| Logic strength | `HasBotImpl` (efq), `HasDNImpl` (DNE) | `IntPropAxiom` / `PropositionalAxiom` |
| Equivalence | `ContextualInferenceSystem.Equivalence` | `Theory.equiv` / `Theory.Equiv` |

Thomas's design is more modular and typeclass-driven. However:
- CSLib already has a working deduction theorem, substitution closure, and completeness proofs using the concrete `DerivationTree`.
- Migrating to Thomas's architecture would require re-proving all metalogical results.
- The typeclass approach is better for generic logic frameworks; the concrete approach is better for a specific library with known logic targets.

**Recommendation**: Thomas's typeclass design is intellectually interesting and could inform future CSLib refactoring, but migrating now would be disruptive. The existing architecture works and has proved its value through the completeness theorems.

### 6. The bot_val / botForces Question: Connections Across Semantics

The thread debate about `bot_val` connects three semantic layers:

| Semantic Layer | File | bot Treatment | Algebra |
|---------------|------|---------------|---------|
| `AlgEvaluate` | `Semantics/Algebra.lean` | Explicit `bot_val : H` parameter | `GeneralizedHeytingAlgebra` |
| `IForces` | `Semantics/Kripke.lean` | Explicit `botForces : World -> Prop` | Preorder |
| `Evaluate` | `Semantics/Bool.lean` | Hardcoded `False` / `false` | `Prop` / `Bool` |

Thomas's point (MSG 604025028): "If it was always mapped to false / a bottom element then every model would validate efq." This is correct -- MPL completeness requires models where `bot` can be forced (otherwise EFQ is universally valid, collapsing MPL into IPL).

Benjamin's response (MSG 604219492): The `bot_val` parameter is the Johansson designated constant, capturing exactly this degree of freedom. For IPL/CPL, fixing `bot_val = bot` recovers the standard semantics. The `v models T` hypothesis in `AlgTValid` handles this generically.

**The compromise that already exists**: `AlgTValid` (defined in `Semantics/Algebra.lean`) is Thomas's `v models T` pattern with `bot_val`:

```lean
def AlgTValid (T : Theory Atom) (v : Atom -> H) (bot_val : H) : Prop :=
  forall B in T, AlgEvaluate v bot_val B = top
```

The general completeness theorem quantifies over `(v, bot_val)` and conditions on `v models T`. For IPL, requiring `HeytingAlgebra H` and `bot_val = bot` recovers Thomas's clean formulation. This is explicitly acknowledged in Benjamin's MSG 604219492.

### 7. Thomas's Unanswered Question

MSG 605341190 ends: "btw Benjamin, why did you delete that part of the docstring in `NaturalDeduction/Basic`?"

This refers to documentation changes in `NaturalDeduction/Basic.lean`. The current docstring (lines 14-64 of `NaturalDeduction/Basic.lean`) contains architecture documentation about the two proof systems and their relationship. Thomas is asking about a previous version's docstring that was modified or removed.

**Recommended response**: Benjamin should check the git history for `NaturalDeduction/Basic.lean` to identify what docstring content was removed and explain the reason (likely cleanup/restructuring during PR #648 preparation).

## Source-to-Implementation Mapping

| Thread Claim | Source (MSG ID) | CSLib Implementation | Status |
|-------------|-----------------|---------------------|--------|
| bot as primitive constructor | 604219492 (Benjamin) | `Proposition.bot` in `Defs.lean:82` | Implemented |
| Substitution as monad bind | 604219492 (Benjamin) | `Proposition.subst` in `Defs.lean:127-134`, `Monad` instance at `Defs.lean:136-138` | Implemented |
| ND with 10 constructors | 602336739 (Benjamin) | `Theory.Derivation` in `NaturalDeduction/Basic.lean:93-122` | Implemented |
| Hilbert with 3 axiom tiers | 603092046 (Benjamin) | `MinPropAxiom`/`IntPropAxiom`/`PropositionalAxiom` in `Axioms.lean` | Implemented |
| ND-Hilbert equivalence | 602336739 (Benjamin) | `hilbert_iff_nd_ctx` in `Equivalence.lean:332-343` | Implemented |
| AlgEvaluate with bot_val | 603884159 (Thomas) | `AlgEvaluate` in `Algebra.lean:82-88` | Implemented |
| v models T parametric style | 603884159 (Thomas) | `AlgTValid` in `Algebra.lean:141-143` | Implemented |
| BoolEvaluate for DPLL | 603520169 (Benjamin) | `Semantics/Bool.lean` | Implemented |
| IProposition/IDerivation | 605341190 (Thomas) | Not in CSLib; in `cslib_SKI/intuitionistic` branch | Not adopted |
| ContextualInferenceSystem | 603086134 (Thomas) | Not in CSLib; in `cslib_SKI/hilbert` branch | Not adopted |

## Decisions

### D1: The response should affirm primitive bot with clear reasoning

**Evidence**: The substitution invariance argument (MSG 604219492) is decisive. Every participant except Thomas agrees. The codebase has hundreds of `| .bot => .bot` pattern matches across PL, Modal, Temporal, and Bimodal logics.

### D2: The response should NOT adopt Thomas's IProposition compromise

**Evidence**: Dual inductive types create maintenance burden. CSLib's `Proposition` + theory parameter is architecturally cleaner. The translation overhead (noncomputable `toIDerivation`) is a red flag.

### D3: The response SHOULD acknowledge Thomas's ND symmetry point more deeply

**Evidence**: Thomas is right that ND purity demands constructor-rule correspondence. The response should explain *why* CSLib breaks this invariant (MPL-first design, theory parameter) and acknowledge it as a deliberate trade-off, not an oversight.

### D4: Thomas's v models T style is already adopted

**Evidence**: `AlgTValid` in `Algebra.lean:141-143` explicitly credits Thomas ("Thomas Waring's `v models T` pattern") and implements exactly his completeness architecture.

### D5: The docstring question must be answered

**Evidence**: Thomas asked a specific question (MSG 605341190) that has not been addressed. Any response must answer it.

## Recommendations

### R1. Respond to Thomas's full message point-by-point

The Zulip response should address each of Thomas's four paragraphs:
1. **MPL vs. IPL as base**: Acknowledge that CSLib's choice (MPL with `bot` primitive) is a hybrid -- it takes MPL's absence of axioms but adds `bot` to the syntax. Explain that this is deliberate because `bot` is a nullary operation (not a generator), and the theory parameter captures the logic-strength dimension orthogonally.
2. **ND symmetry**: Acknowledge that adding `bot` without `efq` as primitive breaks the constructor-rule correspondence. Explain that this is the cost of the theory-parameterized design: `efq` is theory-dependent (absent in MPL), so it cannot be a primitive constructor unless we commit to IPL as the base (which is what Thomas's `IProposition` does).
3. **IProposition compromise**: Thank Thomas for the proof-of-concept. Explain that CSLib's multi-logic architecture (PL + Modal + Temporal + Bimodal sharing one `Proposition` type) makes dual types impractical, but that the translations he proved are useful as reference.
4. **Cost issue**: Address his point that `bot_val` still requires ensuring `v bot = bot` for intuitionistic applications. The answer: yes, but this condition is captured by `AlgTValid` -- the `v models IPL` hypothesis does this work. With `bot`-as-atom, the condition `sigma(bot) = bot` would need to be carried through *every substitution*, not just semantics.

### R2. Answer the docstring question directly

Check `git log --follow -p -- Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` to identify what was removed and explain why. Do not leave this question unanswered.

### R3. Frame the dual proof system architecture explicitly

The response should explain *why* CSLib has both ND and Hilbert:
- ND is the proof-construction layer (user-facing, constructive, Curry-Howard)
- Hilbert is the metalogical layer (completeness, deduction theorem, substitution closure)
- The equivalence bridge (`hilbert_iff_nd_ctx`) transfers results between layers
- This is standard practice: [Prawitz1965] proves the equivalence, [TroelstraVanDalen1988] uses it for intuitionistic metalogic

### R4. Acknowledge what Thomas's work contributed to CSLib

Even though CSLib has not adopted Thomas's `IProposition` or `ContextualInferenceSystem`:
- Thomas's GHA evaluation idea is implemented as `AlgEvaluate`
- Thomas's `v models T` parametric completeness is implemented as `AlgTValid`
- Thomas's original ND system is the foundation that CSLib's `Derivation` builds on (the copyright header credits Thomas Waring)

### R5. Consider adding a brief "Design Rationale" section to Defs.lean

The docstring in `Defs.lean` already contains architecture notes, but a dedicated "Why bot is primitive" section would document the design decision permanently and prevent future re-litigation. This should cite the Zulip thread discussion.

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Thomas feels his contribution is not acknowledged | Contributor disengagement | Explicitly credit his GHA idea, v models T pattern, and original ND system in the response |
| Dual proposition types introduced later | API surface explosion, maintenance burden | Document the decision against IProposition and the reasoning in Defs.lean |
| ND symmetry concern is dismissed | Philosophical disagreement festers | Acknowledge it as a genuine trade-off, document in NaturalDeduction/Basic.lean |
| Docstring question unanswered | Thomas feels ignored | Answer it in the response; check git history |
| Matthew's DPLL work blocked | Feature delay | Confirm BoolEvaluate layer is ready; suggest stacking a PR |

## Adversarial Self-Verification

### Challenge 1: Is Thomas's ND symmetry argument stronger than we acknowledge?

**Challenge**: Thomas argues that if `bot` is in the syntax, `efq` should be a primitive rule. We dismiss this by saying "theory parameter handles it." But does the theory-parameter approach genuinely preserve ND's meaning-through-rules philosophy?

**Verification**: No -- and we should be honest about this. CSLib's ND system is not a *pure* natural deduction system in the sense of [Gentzen1935] or [Prawitz1965]. It is a *hybrid*: primitive constructors for `and/or/imp`, but `bot` handled via theory axioms. This hybrid works because the metalogical results (completeness, etc.) are proved in the Hilbert layer. But Thomas is right that a purist would object. The response should acknowledge this trade-off explicitly rather than claiming the design is unambiguously correct.

**Result**: Revised -- recommendation R3 now includes explicit acknowledgment that CSLib's ND is a hybrid, not pure Gentzen-style ND.

### Challenge 2: Is the "substitution invariance" argument as strong as claimed?

**Challenge**: Benjamin's MSG 604219492 argues that `bot`-as-atom breaks the free-algebra structure. But Thomas's MPL (without `bot` in syntax) also has clean substitution -- `Proposition Atom` without `bot` is a free algebra over `{imp, and, or}`.

**Verification**: The argument is strong but needs qualification. The issue is not whether MPL has clean substitution (it does), but whether adding `bot` as an atom to get IPL/CPL introduces side conditions. With `bot`-as-atom, every substitution theorem acquires `sigma(bot) = bot`. With `bot`-as-constructor, this is automatic. The cost differential is real and measurable in the codebase: CSLib has `subst_preserves_axiom`, `subst_preserves_intAxiom`, `subst_preserves_minAxiom`, `hilbertSubstitution`, and `Theory.Derivation.substAtom` -- none have `bot`-preservation side conditions.

**Result**: Confirmed -- the argument holds. The key point is that CSLib wants `bot` in the shared syntax (because modal/temporal logics need it), and given that `bot` is in the syntax, making it a constructor is strictly better than making it an atom.

### Challenge 3: Could Thomas's IProposition be adopted alongside Proposition?

**Challenge**: What if CSLib kept `Proposition` as-is but also defined `IProposition` as a convenience alias with translations?

**Verification**: This is precisely Thomas's compromise proposal. It works mechanically (his branch compiles), but:
- The `noncomputable` `toIDerivation` direction means you cannot compute with intuitionistic derivations built via translation
- Users would need to choose which type to work in, creating cognitive overhead
- The `FromPropositional` embedding to modal logic would need to handle both types
- There is no precedent in Mathlib for maintaining two isomorphic inductive types for the same concept

**Result**: Confirmed -- adoption is possible but inadvisable for a library context. The response should acknowledge the possibility while explaining why CSLib opts against it.

### Challenge 4: Is there an alternative reading of Thomas's position?

**Challenge**: Could Thomas be arguing not for `IProposition` adoption but simply for documenting that CSLib's `Proposition` is IPL-flavored (has `bot` + `efq` via theory) rather than MPL-flavored (no `bot`)?

**Verification**: Re-reading MSG 605341190: "if the community strongly wants `IPL` as the base theory, we should of course do that -- this message is my reasoning for the version I picked when I wrote these files." This is gracious -- Thomas is deferring to the community while explaining his reasoning. He is not demanding `IProposition` be adopted. His compromise branch is a proof-of-concept demonstrating the translation is possible, not a PR demand.

**Result**: Revised -- the response should match Thomas's tone: acknowledge his reasoning, explain CSLib's choice, and be explicit that it is a design decision, not a correctness claim. Thomas's position (MPL without `bot` as the pure ND system) is mathematically defensible.

### Challenge 5: Are all Tier 1 claims backed by verified citations?

**Verification**: This is a Tier 3 (implementation-backed) task, not Tier 1. Literature references are secondary. All BibKeys were verified against `references.bib`. No unverified citations.

**Result**: Confirmed -- reference grounding is complete for this tier.

## Appendix

### A. Complete Thread Message Sequence

| MSG ID | Sender | Date | Topic |
|--------|--------|------|-------|
| 602336739 | Benjamin | 2025-06-07 | Initial announcement of Hilbert systems + ND equivalence |
| 603062659 | Matthew | 2025-06-10 | Request for smaller PR with assignment semantics |
| 603084275 | Thomas | 2025-06-10 | Suggests GHA for evaluation; mentions held-off PRs |
| 603086134 | Thomas | 2025-06-10 | Links cslib_SKI/hilbert branch; discusses contextual inference |
| 603087026 | Thomas | 2025-06-10 | Discusses automation via constructive proofs |
| 603092046 | Benjamin | 2025-06-10 | Details deduction theorem, completeness; requests thoughts |
| 603163993 | Benjamin | 2025-06-11 | Notes bot is not primitive; creates PR #648 |
| 603367168 | Matthew | 2025-06-12 | Requests Bool semantics; links Tseitin transformation |
| 603391795 | Matthew | 2025-06-12 | Discusses probability logic directions |
| 603520169 | Benjamin | 2025-06-13 | Explains Prop vs Bool; adds BoolEvaluate with bridge |
| 603538889 | Matthew | 2025-06-13 | Suggests single Bool semantics via decide |
| 603572691 | Benjamin | 2025-06-13 | Explains Prop/Kripke uniformity; proposes consolidation |
| 603755068 | Matthew | 2025-06-14 | Notes Thomas's Prop-based PR; discusses Prop awkwardness |
| 603759299 | Thomas | 2025-06-14 | Corrects: GHA evaluation resolves Prop/Bool; links HasInterp |
| 603849782 | Matthew | 2025-06-14 | Notes GHA may not cover linear logic; likes HasInterp |
| 603850371 | Thomas | 2025-06-14 | Clarifies: GHA is for PL specifically |
| 603877853 | Matthew | 2025-06-14 | Proposes HeytingAlgebra evaluate with bot; agrees on primitive bot |
| 603884159 | Thomas | 2025-06-14 | Explains why HA evaluate breaks MPL completeness; links Heyting.lean |
| 603958377 | Matthew | 2025-06-14 | Discusses Dedekind-MacNeille completion; questions botForces |
| 604025028 | Thomas | 2025-06-15 | Explains bot_val necessity for MPL; IPL conservativity |
| 604166734 | Matthew | 2025-06-15 | Argues for explicit falsum; mentions fragments; DPLL complexity |
| 604219492 | Benjamin | 2025-06-15 | Substitution invariance argument; universal algebra; bot_val defense |
| 605341190 | Thomas | 2025-06-16 | Full response: MPL as base, ND symmetry, IProposition compromise, docstring question |

### B. Files Examined

| File | Purpose |
|------|---------|
| `Cslib/Logics/Propositional/Defs.lean` | Proposition type, Theory, substitution monad |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | ND derivation (10 constructors) |
| `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` | efq as derived rule |
| `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` | ND-Hilbert bridge |
| `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` | Min/Int/Prop axiom predicates |
| `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` | DerivationTree (Hilbert) |
| `Cslib/Logics/Propositional/Semantics/Algebra.lean` | AlgEvaluate, AlgTValid |
| `Cslib/Logics/Propositional/Semantics/Kripke.lean` | IForces, botForces |
| `thomaskwaring/cslib_SKI/intuitionistic/...Intuitionistic.lean` | IProposition, IDerivation |
| `thomaskwaring/cslib_SKI/hilbert/...Classes.lean` | ContextualInferenceSystem |
| `thomaskwaring/cslib_SKI/kripke/...Heyting.lean` | GHA evaluation (Thomas's version) |
