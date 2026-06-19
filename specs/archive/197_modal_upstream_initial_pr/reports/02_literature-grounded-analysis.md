# Research Report: Literature-Grounded Analysis for Modal/ Upstream PR

- **Task**: 197 - Scope initial Modal/ upstream PR (~300 LOC)
- **Started**: 2026-06-14T18:00:00Z
- **Completed**: 2026-06-14T18:45:00Z
- **Effort**: 45 minutes
- **Dependencies**: Task 198 (PR #647, now CLOSED), Report 01
- **Sources/Inputs**:
  - `Cslib/Logics/Modal/Basic.lean` (local, 424 LOC)
  - `Cslib/Logics/Modal/Denotation.lean` (local, 85 LOC)
  - `Cslib/Foundations/Logic/Connectives.lean` (local)
  - `upstream/main:Cslib/Logics/Modal/Basic.lean` (upstream, 277 LOC)
  - `upstream/main:Cslib/Logics/Modal/Denotation.lean` (upstream, 53 LOC)
  - `references.bib` -- BibKey verification
  - `specs/literature/burgess_1984.md` -- Burgess 1984 tense logic
  - `specs/198_submit_propositional_upstream_pr/pr-description.md`
  - GitHub API: PR #607 (fmontesi), PR #647 (benbrastmckie)
- **Artifacts**: This report
- **Standards**: report-format.md, artifact-formats.md

## Executive Summary

- **PR #647 (Propositional) is CLOSED without merge** (closed 2026-06-14). This changes the dependency picture: the Modal PR can no longer stack on a merged PR 198. Either PR #647 must be re-submitted or the Modal PR must be self-contained.
- **PR #607 (fmontesi) remains OPEN** (updated 2026-06-01) with active review discussion. Reviewers have proposed consolidating operator typeclasses into fewer files and questioned simp/grind direction. The PR modifies `Modal/Basic.lean`.
- **All 7 BibKeys in the draft PR description are verified present** in `references.bib` with correct metadata.
- **The Burgess 1984 literature strongly supports the box-as-primitive choice**: tense logic's G = NOT F NOT pattern is the exact temporal analog of BOX = NOT DIAMOND NOT, and Burgess explicitly presents the universal quantifier operators (G, H) as the "dual" operators derived from the existential ones, but the Kt axiomatization uses G/H as the subjects of necessitation and the K axiom -- confirming box/necessity as the natural primitive.
- **The upstream diff is 291 insertions / 110 deletions** across Basic.lean and Denotation.lean, confirming the ~290 LOC target from Report 01 remains accurate.

## Context & Scope

This is supplementary research for task 197, adding literature-grounded analysis and status updates that Report 01 did not cover. The first report established the recommended PR scope (Basic.lean + Denotation.lean, ~290 LOC) and identified key risks. This report addresses five specific gaps: citation verification, literature support for primitive choice, upstream comparison, PR #607 status, and PR #647 readiness.

## Findings

### 1. Citation Verification

All BibKeys referenced in the draft PR description (Report 01, Section 5) exist in `references.bib`:

| BibKey | Type | Status | Used For |
|--------|------|--------|----------|
| `Blackburn2001` | `@book` | Present, correct | Box-as-primitive justification (Ch. 1) |
| `ChagrovZakharyaschev1997` | `@book` | Present, correct | Box-as-primitive justification (S. 1.1) |
| `Bentzen2023` | `@inproceedings` | Present, correct | Five-primitive signature precedent |
| `Trufas2024` | `@inproceedings` | Present, correct | Five-primitive signature precedent |
| `Johansson1937` | `@article` | Present, correct | Bot-as-primitive convention origin |
| `Wajsberg1938` | `@article` | Present, correct | Referenced in `Connectives.lean` docstring |
| `McKinsey1939` | `@article` | Present, correct | Referenced in `Connectives.lean` docstring |

Additionally, `Burgess1984` (`@incollection`) is present in `references.bib` and can be cited in the PR description to strengthen the roadmap toward tense/temporal logic.

**No missing or incorrect BibKeys identified.**

### 2. Literature Support for Box-as-Primitive

The Burgess 1984 literature provides independent support for choosing box (necessity/G) over diamond (possibility/F) as the primitive modal operator:

**Argument from tense logic analogy (Burgess 1984)**:

- Tense logic uses four operators: F (future possibility), P (past possibility), G (future necessity), H (past necessity)
- The duality laws are: G = NOT F NOT, H = NOT P NOT -- exactly the pattern BOX = NOT DIAMOND NOT
- The Kt axiomatization (Section 3) states axioms and necessitation rules in terms of G and H (the universal/necessity operators), not F and P:
  - (K_G): G(phi -> psi) -> (G phi -> G psi) -- this is axiom K for the future direction
  - (K_H): H(phi -> psi) -> (H phi -> H psi) -- this is axiom K for the past direction
  - Necessitation_G: from phi, infer G phi
  - Necessitation_H: from phi, infer H phi
- The interaction axioms (GP, HF) connect the two directions but use G and H as the outer operators

This confirms the pattern: the K axiom and necessitation rule are naturally stated with the universal/necessity operator (box/G/H), making it the natural primitive. The existential operators (diamond/F/P) are then derived via classical negation.

**Argument from the existing CSLib codebase**:

The local `Basic.lean` already documents the rationale comprehensively (lines 28-38):
- Box = universal quantification over accessible worlds
- Box preserves conjunction: BOX(phi AND psi) IFF BOX phi AND BOX psi
- Box distributes over implication: axiom K
- Box is the subject of necessitation
- Diamond is derived classically as DIAMOND phi := NOT BOX NOT phi

**Argument from the standard textbooks**:

- Blackburn et al. (2001) Ch. 1 presents box as the primitive modal operator and derives diamond
- Chagrov and Zakharyaschev (1997) S. 1.1 similarly treats box as primitive

**Argument for the CSLib roadmap**:

When CSLib extends to tense/temporal logic (which the Burgess paper covers), having box as primitive in the monomodal case creates a consistent convention. The temporal `Proposition` type already uses `HasUntil`/`HasSince` (existential temporal operators), while the bimodal extension adds `HasBox` for the universal modality. Box-as-primitive in the modal case sets up the correct pattern for the entire hierarchy.

### 3. Upstream Comparison

A detailed comparison of upstream vs. local `Basic.lean`:

**Upstream (277 LOC)** uses primitives `{atom, not, and, diamond}`:

```
Proposition: atom | not | and | diamond     (4 constructors)
Derived:     or, impl, iff, box             (4 defined terms)
Satisfies:   4 match cases (atom, not, and, diamond)
Proofs:      Mostly `grind`-based
```

**Local (424 LOC)** uses primitives `{atom, bot, imp, box}`:

```
Proposition: atom | bot | imp | box          (4 constructors, + DecidableEq, BEq)
Derived:     neg, top, or, and, diamond, iff (6 abbrevs)
Satisfies:   4 match cases (atom, bot, imp, box)
Proofs:      Explicit term-mode / lightweight tactics
New:         neg_iff, diamond_iff, and_iff, or_iff (unbundled satisfaction lemmas)
New:         ModalConnectives instance
New:         Connectives.lean import
```

**Key structural differences**:

| Aspect | Upstream | Local |
|--------|----------|-------|
| Negation | Primitive constructor `.not` | Derived: `neg phi := imp phi bot` |
| Conjunction | Primitive constructor `.and` | Derived: `and phi psi := imp (imp phi (imp psi bot)) bot` |
| Diamond | Primitive constructor `.diamond` | Derived: `diamond phi := neg (box (neg phi))` |
| Implication | Derived `def` | Primitive constructor `.imp` |
| Box | Derived `def` | Primitive constructor `.box` |
| Bot | Not present | Primitive constructor `.bot` |
| `Satisfies` characterizations | `grind` proves them via definitions | Explicit lemmas needed (neg_iff, and_iff, etc.) |
| `derivation_def` attribute | `@[scoped grind =_]` | `@[scoped grind =]` |
| Proof style | Heavy `grind` usage | Explicit term-mode proofs |
| Copyright | Montesi only | Montesi + Brast-McKie |
| Authors | Montesi, Girlando | Montesi, Girlando, Brast-McKie |

**Upstream `Denotation.lean` (53 LOC)** vs. **local (85 LOC)**:

The upstream denotation uses primitive match cases:
- `.not phi => (phi.denotation m)^c`
- `.and phi1 phi2 => phi1.denotation m INTER phi2.denotation m`
- `.diamond phi => {w | EXISTS w', m.r w w' AND w' IN phi.denotation m}`

The local denotation uses the new primitives:
- `.bot => EMPTY`
- `.imp phi1 phi2 => (phi1.denotation m)^c UNION phi2.denotation m`
- `.box phi => {w | FORALL w', m.r w w' -> w' IN phi.denotation m}`

The local `satisfies_mem_denotation` uses an explicit induction proof instead of `grind`.

### 4. PR #607 Status Update

**Status**: OPEN (last updated 2026-06-01)

**Key review feedback** (from GitHub API):

1. **@chenson2018** suggested consolidating operator typeclasses into a single file rather than one-file-per-operator (`Operators/And.lean`, `Operators/Box.lean`, etc.). This aligns with our `Connectives.lean` approach.

2. **@chenson2018** questioned simp/grind direction on characterization lemmas -- should they simplify into notation rather than away from it.

3. **@thomaskwaring** noted difficulty making `grind` see through notation/typeclass layers in satisfaction proofs.

4. **@ctchou** proposed three-file organization: `Modal` (box+diamond), `Tensor` (by itself), `Propositional` (the rest).

5. **@fmontesi** acknowledged the file organization is provisional.

**Implications for our PR**:

- The single-file `Connectives.lean` approach is favored by at least one reviewer
- Our explicit proofs (rather than `grind`) sidestep the transparency issues @thomaskwaring reported
- PR #607 keeps `{atom, not, and, diamond}` as primitives while adding typeclass instances -- this is structurally incompatible with our `{atom, bot, imp, box}` approach
- PR #607 includes `HasDiamond` and `HasNot` (since diamond and not are primitive there) -- our approach derives both, so these typeclasses would be unnecessary
- **The primitive set disagreement remains the core coordination issue**

### 5. PR #647 (Propositional) Status

**Status**: CLOSED (not merged), closed 2026-06-14T19:42:19Z

This is a significant development that was not anticipated in Report 01. PR #647 (our Propositional PR with `Connectives.lean` and the five-primitive formula type) was closed the same day it was submitted, with no review comments.

**Impact on Modal PR**:

- The Modal PR cannot be stacked on PR #647 since it was not merged
- `Connectives.lean` (which defines `ModalConnectives`, `HasBox`, etc.) does not exist upstream
- **Two options**:
  1. **Re-submit PR #647 first**, then stack the Modal PR on it
  2. **Bundle `Connectives.lean` into the Modal PR** -- include the relevant typeclass definitions directly (only `HasBot`, `HasImp`, `HasBox`, `PropositionalConnectives`, `ModalConnectives`), making the Modal PR self-contained at the cost of a larger diff
  3. **Submit Modal PR without `ModalConnectives` instance** -- defer the typeclass registration to a follow-up after `Connectives.lean` is accepted

**Recommendation**: Re-submit PR #647 as a prerequisite. The Propositional PR is architecturally independent of the Modal PR and provides the foundational layer. If re-submission is not viable, option 3 (defer typeclass instance) preserves independence while still delivering the formula type refactoring.

## Decisions

- **BibKeys are verified** -- no changes needed to the draft PR description's citations
- **Box-as-primitive is well-grounded** -- supported by Blackburn, Chagrov-Zakharyaschev, Burgess, and the CSLib typeclass hierarchy design
- **PR #647 closure must be addressed** before submitting the Modal PR -- either re-submit or adjust scope

## Recommendations

1. **Investigate PR #647 closure** -- determine whether it was closed intentionally (self-closed due to an issue) or by a reviewer. The absence of review comments suggests self-closure. If self-closed, re-submit after addressing any issues found.

2. **Engage on Zulip before re-submission** -- the PR #607 review discussion shows active interest in the typeclass organization question. Opening a Zulip thread about primitive set choice (bot/imp/box vs. not/and/diamond) with literature citations would build consensus before submitting.

3. **Add Burgess1984 citation to the PR description** -- strengthen the roadmap section by noting that the box-as-primitive choice aligns with tense logic conventions (Burgess 1984), where G and H (the universal temporal operators) are the subjects of axiom K and necessitation, exactly as box is in monomodal logic.

4. **Address the `grind` vs explicit proof style proactively** -- the PR #607 review shows reviewers are aware of the grind transparency issue. Our explicit proofs are a feature, not a liability. Note in the PR description that explicit proofs avoid the transparency issues reported in PR #607.

5. **Consider the `=_` vs `=` attribute difference** -- the upstream `derivation_def` uses `@[scoped grind =_]` while local uses `@[scoped grind =]`. Verify this does not break `Cube.lean` proofs that may depend on grind's rewriting direction.

6. **Keep the import path adjustment in the plan** -- `Cslib.Foundations.Data.Relation` must revert to `Cslib.Foundations.Relation.Euclidean` for the upstream PR.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| PR #647 closure blocks Modal PR | H | H | Investigate closure reason; re-submit or adjust scope |
| PR #607 merges with incompatible primitives | H | M | Zulip discussion with literature-backed arguments for box-as-primitive |
| Proof style rejected by reviewers | M | L | Offer to convert to `grind` if requested; note transparency advantages |
| `grind =_` vs `grind =` causes Cube.lean breakage | L | L | Test on PR branch; revert to `=_` if needed |

## Literature Proof Structure (Burgess 1984)

The Burgess paper's structure maps to our Modal PR as follows:

| Burgess Section | Content | CSLib Analog |
|----------------|---------|--------------|
| S2: Kripke Semantics | Model = (T, <, V), satisfaction induction | `Model`, `Satisfies` in Basic.lean |
| S2: Satisfaction of G/H | forall-quantification over accessible worlds | `Satisfies` case for `.box` |
| S2: Validity | Valid on a frame class | `Proposition.valid`, `logic` in Basic.lean |
| S3: Kt axiomatization | K_G, K_H, necessitation | `Satisfies.k` (axiom K), future proof system PRs |
| S3: Soundness/completeness | Canonical model construction | Future PR (roadmap PR 9+) |
| S4: Extensions | T4, linearity, density, discreteness | Frame condition theorems (T, B, 4, 5, D) in Basic.lean |
| S5: Until/Since | Temporal operators, Kamp's theorem | Future temporal logic PRs |

The correspondence validates our approach: the monomodal `Basic.lean` is the special case of Burgess's framework with a single accessibility relation and a single necessity operator (box = G with no past direction).

## Appendix

### A. Diff Statistics (upstream/main vs local)

```
Basic.lean:      248 insertions, 101 deletions (net +147)
Denotation.lean:  43 insertions,   9 deletions (net +34)
Total:           291 insertions, 110 deletions (net +181)
```

### B. PR #607 Files Modified

```
Cslib/Foundations/Logic/Operators/And.lean      (new)
Cslib/Foundations/Logic/Operators/Box.lean       (new)
Cslib/Foundations/Logic/Operators/Diamond.lean   (new)
Cslib/Foundations/Logic/Operators/Iff.lean       (new)
Cslib/Foundations/Logic/Operators/Impl.lean      (new)
Cslib/Foundations/Logic/Operators/Not.lean       (new)
Cslib/Foundations/Logic/Operators/Or.lean        (new)
Cslib/Foundations/Logic/Operators/Tensor.lean    (new)
Cslib/Logics/Modal/Basic.lean                   (modified)
Cslib/Logics/Propositional/Defs.lean            (modified)
Cslib.lean                                       (modified)
```

### C. PR #607 Review Timeline

- 2026-05-29: PR opened by @fmontesi
- 2026-05-29: @chenson2018 -- consolidate files, question simp/grind direction
- 2026-05-29: @thomaskwaring -- grind transparency issues with typeclass notation
- 2026-05-29: @chenson2018 -- suggests judgement-level characterization lemmas
- 2026-06-01: @ctchou -- proposes 3-file organization (Modal, Tensor, Propositional)
- 2026-06-01: @fmontesi -- acknowledges file organization is provisional
- No further activity since 2026-06-01
