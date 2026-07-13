# feat(Logics/Modal): fully-primitive modal formula base + semantic cube (stacked on #607)

*Draft PR body for #662 — supersedes the earlier "make box primitive" description. Stacked on #607 (`fmontesi/connectives`). Not for posting until the branch is pushed and CI is confirmed green at that time.*

## Summary

This PR reshapes the modal formula type into a **fully-primitive base** and rounds out the **semantic modal cube** on top of the operator typeclasses introduced in #607. It is purely semantic — no proof system or completeness — and is meant to review as the modal delta on top of #607.

**Modal `Proposition` is now**

```lean
inductive Proposition (Atom) where
  | atom | bot | imp | and | or | box | diamond   -- all primitive
-- ¬A := A → ⊥   (the only derived connective)
```

i.e. `⊥`, `→`, `∧`, `∨`, `□`, `◇` are all constructors, with negation derived as `A → ⊥`. Notation is wired through #607's `Foundations/Logic/Operators` typeclasses (`HasImp`/`HasAnd`/`HasOr`/`HasNot`/`HasBox`/`HasDiamond`) and Mathlib's `Bot` (`instance : Bot (Proposition Atom) := ⟨.bot⟩`, unconditional).

## What changed

**1. Both modalities primitive.** `□` and `◇` are independent constructors, so `Satisfies.box_iff_forall` and `Satisfies.diamond_iff_exists` are both `Iff.rfl`, and `◇φ ↔ ¬□¬φ` (`Satisfies.dual`) is a derived lemma rather than a definitional unfolding.

**2. `⊥` (and `→`) primitive.** `⊥` is a genuine constructor (not an encoded `atom ⊥` conditional on `[Bot Atom]`), and `→` is a constructor, so negation is `neg := imp · ⊥`. This makes the type structurally uniform with the propositional side and is the natural basis for the forthcoming proof-theoretic development.

**3. Semantic cube completed.** `Cube.lean` now carries, for the modal-cube axioms:
- **Validity** — `K.k_valid`, `T.t_valid`, plus the previously-missing `B.b_valid`, `Four.four_valid`, `Five.five_valid`, `D.d_valid`.
- **Canonicity** — `T.t_canonical`, `B.b_canonical`, `Four.four_canonical`, `Five.five_canonical`, `D.d_canonical` (axiom globally valid on a frame ⇒ the frame satisfies the corresponding condition).
- **Correspondence** — `T.t_correspondence` … `D.d_correspondence`: the biconditional packaging of the two directions (`axiom valid on frame r ↔ r has the frame property`), over `Std.Refl` / `Std.Symm` / `IsTrans` / `Relation.RightEuclidean` / `Relation.Serial`.

The 15 cube logic definitions and the essential logic-inclusion lemmas from #607 are unchanged.

## Design notes

- **Why fully primitive** (esp. `⊥`/`→`): the intended downstream is the modal metalogic (Hilbert calculus, soundness, completeness), whose axiom schemata and derivation induction are cleanest with `⊥` and `→` as constructors. Fixing the base here avoids a later formula-type refactor once the proof system stacks on top.
- **Consistency with the propositional side**: this base is the propositional core `{atom, bot, imp, and, or}` extended with `{box, diamond}`, so the two `Proposition` types share one primitive discipline and the eventual `Modal.FromPropositional` embedding is constructor-to-constructor.
- `¬` is the sole derived connective; `⊤`, `↔` remain derived abbreviations.

## Scope / relationship to other PRs

- **Stacked on #607** (`fmontesi/connectives`) — reuses its `Operators` typeclasses; base points at `fmontesi/connectives`, so this reviews as just the `Logics/Modal` delta.
- **Independent of #648.** #648 reworks the *propositional* `Proposition` (primitive `⊥`); this PR's modal layer has no functional dependency on the propositional files, so the two do not stack — they are siblings on #607. The propositional-basis choice (#607's derived `⊥` vs #648's primitive `⊥`) is a separate discussion; nothing here forces it.
- **Out of scope (follow-ups):** the proof system + soundness, MCS/canonical-model completeness, `FromPropositional`, and the inter-system/tableau development are deliberately excluded and will come as separate, smaller PRs.

## Verification

- Diff confined to `Logics/Modal/{Basic,Cube,Denotation,LogicalEquivalence}.lean`, `references.bib`, and one `CslibTests/GrindLint.lean` skip entry.
- Zero `sorry`, zero new axioms (new theorems use only `propext` / `Classical.choice` / `Quot.sound`).
- Full `lake build` (2759/2759), `lake test` (8790/8790), `checkInitImports`, `lint-style`, `lint`, and `shake` green.
- **Diff: +233 / −56 across 6 files** — `Modal/Basic.lean` (~120), `Modal/Cube.lean` (+124: validity + canonicity + correspondence), `Modal/LogicalEquivalence.lean` (+21), `references.bib` (+11), `Modal/Denotation.lean` (+9), `CslibTests/GrindLint.lean` (+4).
