# PR Description: feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}

## Title

`feat(Logics/Modal): refactor formula primitives to {atom, bot, imp, box}`

## Summary

This PR refactors `Cslib/Logics/Modal/Basic.lean` to use four classical primitives `{atom, bot, imp, box}` instead of the current `{atom, not, and, diamond}`. Negation, conjunction, disjunction, and diamond become derived connectives via the Lukasiewicz encoding (`¬φ := φ → ⊥`, `φ ∧ ψ := ¬(φ → ¬ψ)`, `φ ∨ ψ := ¬φ → ψ`, `◇φ := ¬□¬φ`). Four files are modified: `Basic.lean` (formula type), `Denotation.lean` (match cases), `LogicalEquivalence.lean` (context constructors), and `Connectives.lean` (new `HasBox` class and `ModalConnectives` bundle, stacking on PR #648). Approximate diff: ~355 insertions, ~222 deletions.

This PR stacks on PR #648 (`feat/propositional-v2`). PR #649 (temporal) is a sibling with no dependency in either direction.

## Design Rationale

### Why box, not diamond?

With box primitive, necessitation is a pure rule — `⊢ φ → ⊢ □φ` — mentioning only `box`. The K axiom `□(φ → ψ) → □φ → □ψ` uses only `box` and `imp`. With diamond primitive, necessitation becomes an interaction law: `⊢ φ → ⊢ ¬◇¬φ` (requiring `neg`), or expanding, `⊢ φ → ⊢ (◇(φ → ⊥)) → ⊥` (requiring `dia`, `imp`, and `bot`). The underlying reason is that `□` pairs naturally with `→` — both primitive in the `{bot, imp, box}` signature — while `◇` pairs with `∨`, which is derived from `→` and `⊥`. [ChagrovZakharyaschev1997] §3.1 adopts the box-first presentation.

Semantically, box is universal quantification over accessible worlds and distributes over implication (K). Diamond is derived as `◇φ := ¬□¬φ = (□(φ → ⊥)) → ⊥`, which requires excluded middle and is therefore specific to classical modal logic. `HasDia` should be added as a separate typeclass once non-classical modal logics (IK, CK) are formalized.

### Why bot and imp as primitives?

This follows PR #648: bot and imp are the classical minimal signature. The key reason for primitive `bot` is substitution invariance — `⊥` as a nullary operation is fixed by every substitution, preserving the free algebra property. See the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/604219492) for the full argument. Propositional `and`/`or` are primitive in `PL.Proposition` (via `HasAnd`/`HasOr`); the Modal formula type uses Lukasiewicz encodings instead.

### Extending to non-classical modal logics

In classical modal logic, `and`, `or`, and `dia` are all derivable from `{bot, imp, box}`. Non-classical systems require these as primitives: `and`/`or` are not interdefinable via `imp`/`bot` without excluded middle, and `◇` is independent of `□`. The typeclass hierarchy accommodates this:

| System | Primitives | Bundle |
|--------|-----------|--------|
| Classical modal (K, T, S4, S5) | `{atom, bot, imp, box}` | `ModalConnectives` |
| Intuitionistic modal (IK, CK) | + `and`, `or`, `dia` | + `HasAnd`, `HasOr`, `HasDia` |

`HasAnd` and `HasOr` already exist as standalone typeclasses (instantiated on `PL.Proposition`). Adding `HasDia` and instantiating all three on a non-classical modal formula type requires no changes to `ModalConnectives`. We recommend completing the classical metalogic (proof system, completeness, soundness) before adding these extensions.

## Main Definitions

- `Proposition (Atom)` — inductive formula type with constructors `{atom, bot, imp, box}`
- `Proposition.neg`, `.top`, `.and`, `.or`, `.diamond`, `.iff` — derived connectives (abbrev)
- `Proposition.Context` — one-hole context type with constructors `{hole, impL, impR, box}`
- `LogicallyEquivalent` — semantic equivalence across all models and worlds
- `ModalConnectives` — bundled typeclass extending `PropositionalConnectives` with `HasBox`

## Notation

All notation is scoped to `Cslib.Logic.Modal`:

| Symbol | Precedence | Definition |
|--------|-----------|-----------|
| `¬` | prefix:40 | `Proposition.neg` |
| `∧` | infix:36 | `Proposition.and` |
| `∨` | infix:35 | `Proposition.or` |
| `→` | infix:30 | `Proposition.imp` |
| `□` | prefix:40 | `Proposition.box` |
| `◇` | prefix:40 | `Proposition.diamond` |
| `↔` | infix:30 | `Proposition.iff` |
| `Modal[m,w ⊨ φ]` | — | `Judgement.mk m w φ` |

## Relationship to Other PRs

**PR #648 (stacking dependency)**: This PR stacks on #648 and carries all its changes including `Connectives.lean` with `PropositionalConnectives`. Review and merge #648 first.

**PRs #528 and #535 (foundation)**: This PR builds directly on @fmontesi's #528/#535, retaining the `Model`/`Satisfies`/`Judgement` structure unchanged.

**PR #607 (coordination)**: PR #607 by @fmontesi introduces per-operator typeclass files. PR #607 is active as of 2026-06-16. The `imp` naming in this PR is #648's settled convention — it aligns with the `HasImp` typeclass name and the elimination rule `impE` across CSLib's Bimodal and Temporal types. PR #607 uses `impl`. Happy to align on whichever naming reviewers prefer. The constructor refactoring from `{not, and, diamond}` to `{bot, imp, box}` is structurally incompatible with #607's current instances and requires coordination — see the [comment on PR #607](https://github.com/leanprover/cslib/pull/607#issuecomment-4735753144).

**PR #587 (coordination)**: PR #587 by @thomaskwaring (DRAFT) creates `Connectives.lean` with semantic typeclasses. PR #648 creates the same path with syntactic typeclasses. The content is complementary — see the [comment on PR #587](https://github.com/leanprover/cslib/pull/587#issuecomment-4735825910).

## Breaking Changes

- Constructors `Proposition.not`, `.and`, `.diamond` replaced by derived abbrevs with the same names (`.and`, `.diamond` continue to work at call sites; `.not` becomes `.neg`)
- `Proposition.Context` constructors renamed: `notC` removed, `andL` → `impL`, `andR` → `impR`, `diamondC` → `box`
- New constructors: `Proposition.bot`, `.imp`, `.box`

## Changed Files

- `Cslib/Foundations/Logic/Connectives.lean` — added `HasBox` + `ModalConnectives` (stacks on #648)
- `Cslib/Logics/Modal/Basic.lean` — refactored `Proposition` type, derived connectives, `ModalConnectives` instance, `Satisfies` cases
- `Cslib/Logics/Modal/Denotation.lean` — match cases updated for new primitives
- `Cslib/Logics/Modal/LogicalEquivalence.lean` — `Context` constructors and `congruence` proof updated

**Excluded**: `FromPropositional.lean` (depends on deferred `Semantics.Bool`), `ProofSystem/`, `Metalogic/`, `Cube.lean` (scoped to subsequent PRs).

## Contribution Roadmap

1. **PR #648**: Connective typeclasses + five-primitive propositional formula type *(open)*
2. **This PR**: Classical modal formula type with `{atom, bot, imp, box}` primitives
3. **PR 3**: [Hilbert proof systems](https://github.com/benbrastmckie/cslib/tree/main/Cslib/Logics/Modal/ProofSystem) for the 15 modal cube logics (K, T, B, D, S4, S5, K4, K5, K45, KB5, D4, D5, D45, DB, TB) using the `InferenceSystem` API as @fmontesi [suggested](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic)
4. **PR 4**: Kripke semantics with strong soundness and strong completeness for all [15 systems](https://github.com/benbrastmckie/cslib/tree/main/Cslib/Logics/Modal/Metalogic/Systems) (canonical model construction via [maximal consistent sets](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/MCS.lean)):

   | System | Strong Soundness | Strong Completeness | Biconditional |
   |--------|-----------------|--------------------|----|
   | K | [`k_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K/StrongCompleteness.lean#L51) | [`k_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K/StrongCompleteness.lean#L69) | [`k_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K/StrongCompleteness.lean#L114) |
   | T | [`t_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/T/StrongCompleteness.lean#L52) | [`t_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/T/StrongCompleteness.lean#L69) | [`t_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/T/StrongCompleteness.lean#L125) |
   | B | [`b_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/B/StrongCompleteness.lean#L52) | [`b_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/B/StrongCompleteness.lean#L69) | [`b_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/B/StrongCompleteness.lean#L124) |
   | D | [`d_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean#L52) | [`d_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean#L69) | [`d_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean#L128) |
   | S4 | [`s4_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/S4/StrongCompleteness.lean#L52) | [`s4_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/S4/StrongCompleteness.lean#L71) | [`s4_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/S4/StrongCompleteness.lean#L136) |
   | S5 | [`s5_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean#L52) | [`s5_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean#L72) | [`s5_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean#L152) |
   | K4 | [`k4_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K4/StrongCompleteness.lean#L49) | [`k4_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K4/StrongCompleteness.lean#L62) | [`k4_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K4/StrongCompleteness.lean#L113) |
   | K5 | [`k5_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K5/StrongCompleteness.lean#L49) | [`k5_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K5/StrongCompleteness.lean#L62) | [`k5_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K5/StrongCompleteness.lean#L114) |
   | K45 | [`k45_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K45/StrongCompleteness.lean#L49) | [`k45_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K45/StrongCompleteness.lean#L64) | [`k45_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/K45/StrongCompleteness.lean#L121) |
   | KB5 | [`kb5_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/KB5/StrongCompleteness.lean#L51) | [`kb5_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/KB5/StrongCompleteness.lean#L70) | [`kb5_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/KB5/StrongCompleteness.lean#L129) |
   | D4 | [`d4_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean#L53) | [`d4_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean#L72) | [`d4_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean#L140) |
   | D5 | [`d5_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean#L53) | [`d5_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean#L72) | [`d5_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean#L137) |
   | D45 | [`d45_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean#L53) | [`d45_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean#L73) | [`d45_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean#L150) |
   | DB | [`db_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean#L53) | [`db_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean#L72) | [`db_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean#L140) |
   | TB | [`tb_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/TB/StrongCompleteness.lean#L52) | [`tb_strong_completeness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/TB/StrongCompleteness.lean#L71) | [`tb_strong_completeness_iff`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Modal/Metalogic/Systems/TB/StrongCompleteness.lean#L136) |

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]

## AI Tools Used

This PR was prepared with the assistance of Claude Code (Anthropic), used for drafting the PR description, analyzing the upstream PR landscape, running CI verification. The mathematical content, proof architecture, and design decisions were verified by the author. All Lean code compiles with no sorries.
