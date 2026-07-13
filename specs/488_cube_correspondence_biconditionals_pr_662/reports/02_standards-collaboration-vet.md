# Vet Report: PR #662 (task-487-pr662-bot-primitive) — Standards & Collaboration

- **Scope**: diff `ddc2c9b8..b041c6f7` on branch `task-487-pr662-bot-primitive`
  (worktree `/home/benjamin/Projects/cslib-task-487-pr662-bot-primitive`), base = upstream #607
  (`fmontesi/connectives`, `ddc2c9b8`).
- **Files**: `Cslib/Logics/Modal/{Basic,Cube,Denotation,LogicalEquivalence}.lean`, `references.bib`,
  `CslibTests/GrindLint.lean` (+233/−56).
- **Assessment only** — no files modified, no fix tasks created, no CI re-run (already confirmed
  green: `lake build` 2759/2759, `lake test` 8790/8790, `checkInitImports`, `lint-style`, `lint`,
  `shake`).
- **Also reviewed**: draft PR body at
  `specs/488_cube_correspondence_biconditionals_pr_662/artifacts/pr-662-body.md`.
- **Standards read**: `CONTRIBUTING.md`, `NOTATION.md`, `ORGANISATION.md`, `CODE_OF_CONDUCT.md`
  (repo root).

## Findings

| Severity | File:Line | Standard | Description | Suggested fix |
|---|---|---|---|---|
| **blocker** | `artifacts/pr-662-body.md` (whole doc) | CONTRIBUTING.md § "The role of AI" | The draft PR body has no `## AI Tools Used` (or equivalent) section. This work was produced via Claude Code task dispatches (task 477/486/487/488, session-tagged commits). CSLib follows the Mathlib AI-use policy, which requires the PR description to explain which AI tool(s) were used and how. This is currently absent. | Add a short `## AI Tools Used` section before posting, naming the tool(s) and describing the workflow (e.g. "Implemented via Claude Code agent dispatches from a task-tracking system; author reviewed and verified all proofs/CI locally"). |
| **should-fix** | `artifacts/pr-662-body.md` §"Design notes"/"Scope" | Collaboration etiquette (CONTRIBUTING.md "Before you start: coordination to avoid rework"; spirit of CODE_OF_CONDUCT.md "respectful of differing viewpoints") | Per task 486's own research report (`specs/486_.../reports/01_modal-soundness-package.md` §0 point 4, §8 item 4), whether PR #662 should "re-own" the Cube's B/4/5/D validity+canonicity (i.e. complete what #607 shipped only for K/T) was explicitly flagged as **a PR-boundary/ownership decision deferred to fmontesi, back 23 July** — not something to unilaterally settle. The current PR body presents the cube completion (`B.b_valid`…`D.d_correspondence`, 15 new theorems) as a plain enhancement without surfacing that this scope question was identified and left open. Given fmontesi previously asked contributors to "take things one at a time" and is away until 23 July, silently completing their deliberately-minimal cube risks reading as scope creep on their return, even though the work itself is technically sound. | Add an explicit line to the PR body (e.g. under "Scope / relationship to other PRs") acknowledging that the cube completion goes beyond #607's shipped K/T-only scope, framing it as an offer ("happy to split this into its own follow-up, or to have you take it from here, if you'd rather own the cube completion yourselves") rather than a fait accompli. Consider holding the PR until fmontesi returns (23 July) or flagging on Zulip first, consistent with the "coordination to avoid rework" norm for major/authorial-boundary changes. |
| **should-fix** | `Cslib/Logics/Modal/{Basic,Cube}.lean` header `Authors:` lines | CONTRIBUTING.md § Style ("we generally follow the mathlib style… "); Mathlib author-attribution convention | `Basic.lean` and `Cube.lean` copyright headers still list only `Fabrizio Montesi, Marianna Girlando`. This PR substantially reshapes `Proposition` (7-constructor fully-primitive base, `not` dropped as primitive) and adds 15 new theorems (Validity/Canonicity/Correspondence) — a genuinely substantial contribution, not a typo fix. Mathlib convention (which CONTRIBUTING.md defers to) is to add contributing authors' names for substantial changes. | Either add the contributing author's name to the `Authors:` line of `Basic.lean` and `Cube.lean` (the two files with the largest substantive additions), or explicitly raise attribution with fmontesi/Girlando given this stacks on their file — don't leave it unaddressed. |
| **nit** | `Cslib/Logics/Modal/Denotation.lean:27` | CONTRIBUTING.md § Proof style (terseness/consistency) | `\| .bot => (∅ : Set World)` carries a redundant explicit type ascription; the match's return type (`Set World`) already pins the elaborated type, and the sibling arms (`.and`, `.or`, `.box`, `.diamond`) have no ascriptions. | Simplify to `\| .bot => ∅` for stylistic consistency with the rest of the match. Purely cosmetic — not required before `/pr`. |
| **nit** | `CslibTests/GrindLint.lean:88` | CONTRIBUTING.md § Linting | New `#grind_lint skip Cslib.Logic.Modal.not_denotation` entry (well-commented, mirrors existing HML precedent) suppresses a lint-threshold violation rather than restructuring the proof. Reasonable and precedented, but worth flagging explicitly to the reviewer since it's a repo-wide lint exception, not a local proof simplification. | No action required; the existing comment already explains the rationale adequately. Reviewer may want to double check whether `not_denotation`'s proof could be golfed to avoid the exception, but this is optional. |

## Standards Compliance — Detail

### CONTRIBUTING.md
- **Copyright/license headers**: present and unmodified in all 4 touched `.lean` files (blocker/should-fix on `Authors:` attribution noted above; license/copyright boilerplate itself is fine).
- **Docstrings**: every new/changed public declaration has a docstring — `Proposition.bot`/`.imp`/`.and`/`.or`/`.box`/`.diamond` constructors, `Bot`/`HasImp`/`HasOr`/`HasBox` instances (implicit, standard to leave undocumented per Mathlib convention for trivial instances), `Proposition.neg` abbrev, all `*_def` lemmas, `Satisfies.dual`, `Satisfies.box_iff_not_diamond_not`, and all 15 new Cube.lean theorems (`B.b_valid` … `D.d_correspondence`). CI's `lake lint` (docBlame) already confirms this passes. No gaps found.
- **Design/reuse**: notation is wired entirely through #607's existing `Operators` typeclasses (`HasImp`/`HasAnd`/`HasOr`/`HasNot`/`HasBox`/`HasDiamond`) plus Mathlib's own `Bot` typeclass — no new ad hoc notation introduced, consistent with "prefer typeclasses over raw notation declarations." Correspondence proofs reuse existing `Std.Refl`/`Std.Symm`/`IsTrans`/`Relation.RightEuclidean`/`Relation.Serial` infrastructure rather than reinventing frame-condition machinery. Fully compliant.
- **Proof style**: `Satisfies.dual` grew from a two-`grind` proof (with dead commented-out code) into an explicit, well-documented manual proof, because negation is no longer definitionally transparent (now `imp · bot`). This is a net readability improvement (the old code had a stale commented-out alternative proof attempt, now removed) and is properly explained inline. No golfing/readability concerns.
- **PR title**: draft title `feat(Logics/Modal): fully-primitive modal formula base + semantic cube (stacked on #607)` correctly starts with an allowed category (`feat`) with a parenthetical area. Compliant.
- **CI compliance**: confirmed green per task instructions (build/test/checkInitImports/lint/lint-style/shake) — not re-run here.

### NOTATION.md
- Not materially applicable: this diff concerns standard logical connectives (`⊥, →, ∧, ∨, ¬, □, ◇`) via Mathlib/CSLib typeclasses, not the operational-semantics arrow notation (Option A/B/C) or bisimilarity notation NOTATION.md governs. No inconsistency found; the connective notation is unchanged in surface syntax across the primitive/derived reshuffling (only which connectives are constructors vs. derived changed, not their display notation).

### ORGANISATION.md
- File placement unchanged and correct: all touched files already live under `Logics/Modal/`, matching the documented module tree (`Modal/{Basic,Cube,Denotation,LogicalEquivalence}.lean`).
- Namespace `Cslib.Logic.Modal` used throughout, matching the documented convention.
- Per-axiom namespacing (`K.k_valid`, `T.t_valid`, `B.b_valid`, `Four.four_valid`, `Five.five_valid`, `D.d_valid`, and the corresponding `_canonical`/`_correspondence` names) follows the pre-existing convention already established in `Cube.lean` before this PR (`K.k_valid`/`T.t_valid` predate this diff) — the new axioms (B/Four/Five/D) extend the same dot-qualified naming scheme consistently. Compliant.

### CODE_OF_CONDUCT.md
- No language or framing issues in code comments, docstrings, or the PR body. The PR body's tone toward the maintainer and toward #648 is collegial and appropriately deferential on the propositional-basis question. The one substantive concern (completing the maintainer's minimal cube while they're away) is a collaboration-etiquette/coordination issue rather than a literal CoC violation — captured above under "should-fix."

## Collaboration Assessment

- **Stacking on #607 / independence from #648**: correct etiquette. The PR body clearly states it reuses #607's `Operators` typeclasses and reviews as "just the `Logics/Modal` delta," and explicitly defers the #648-vs-#607 propositional-basis question without forcing it. This is exactly the right way to avoid entangling two open design questions.
- **Size/reviewability**: +233/−56 across 6 files is small and coherent — one semantic unit (fully-primitive base + completed semantic cube). Given the maintainer's earlier complaint that #662 was "too big," this reworked, much-smaller diff is a marked improvement and should read as reviewable in one sitting.
- **PR body accuracy**: the body's technical description (primitive-basis change, dual/box_iff_not_diamond_not additions, cube sections) accurately matches the diff. The "Verification" section's numbers (2759/2759, 8790/8790, +233/−56) are internally consistent with what's found in this review.
- **Deferred propositional-basis question**: handled well — "nothing here forces it" is an accurate and appropriately hands-off statement.
- **Cube-completion ownership question**: **not** handled well (see should-fix finding above). This is the one substantive collaboration gap: the PR body should acknowledge, not silently resolve, the ownership question that task 486's own research explicitly flagged as belonging to fmontesi.

## Overall Verdict

**Minor fixes advised** (not "ready to ship" as-is; not "needs work" — the code itself is clean, well-documented, and CI-green).

The Lean code is in excellent shape: fully documented, correctly typeclass-wired, well-namespaced, and its size is genuinely reviewable. The issues found are entirely about the PR *framing* and *process*, not the formalization.

### Must fix before running `/pr`

1. **Add an `## AI Tools Used` section** to the PR body per CONTRIBUTING.md's AI-disclosure requirement (blocker).
2. **Add an explicit acknowledgment** in the PR body that completing #607's B/4/5/D cube wrappers goes beyond its shipped K/T-only scope, and that this was previously identified as an ownership question for fmontesi — frame it as an offer, not a fait accompli (should-fix, collaboration risk).
3. **Resolve author attribution** on `Basic.lean`/`Cube.lean` headers — either add the contributor's name or explicitly flag it to the maintainers rather than leaving it silently unaddressed (should-fix).

### Optional / can defer past this PR
- `Denotation.lean:27` redundant type ascription (nit, cosmetic).
- `not_denotation` grind-lint skip entry (nit, already well-precedented and documented).

Given the maintainer is away until 23 July and previously asked for smaller, sequential contributions, the safest path is to address items 1–3 above and consider a short Zulip heads-up (or simply waiting for their return) before opening/updating the PR, rather than merging the cube completion silently while they're away.
