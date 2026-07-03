## Summary

Adds the modal-logic layer with formula primitives `{atom, bot, imp, box}`, **stacked on #648** (`feat/propositional-v2`) and slimmed to a single commit touching only the seven modal files below. All propositional files are inherited unchanged from #648.

**Review order:** GitHub can't base a PR on a fork branch, so this still targets `main` and shows the *combined* #648 + modal diff until #648 merges. Please **merge #648 first** — this PR's diff then collapses to just the modal contribution (7 files, +426/−189, one commit). A short rebase may be needed if #648 is squash-merged.

### Files

- `Cslib/Logics/Modal/Basic.lean` — primitives; K/T/B/4/5/D validity + canonicity
- `Cslib/Logics/Modal/LogicalEquivalence.lean` — parametric `Proposition.Equiv S` (task 472)
- `Cslib/Foundations/Logic/Connectives.lean` — operator typeclasses (`HasBox`, …)
- `Cslib/Logics/Modal/Denotation.lean` — semantics for the new primitives
- `CslibTests/GrindLint.lean`, `Cslib/Logics/Modal/Cube.lean`, `Cslib.lean` — grind-lint skips + wiring

## Design notes

- **Box primitive, diamond derived** (`◇φ := ¬□¬φ`): keeps necessitation and K as pure rules on a single operator. The derivation is classical-only, so a primitive `HasDia` is deferred (TODO noted) for intuitionistic/minimal modal logic.
- **`Connectives.lean` is self-owned**, following @fmontesi's #607 direction. Since #607 is unmerged and lacks `HasBot`/bundled classes, decoupling onto it is deferred to a follow-up — intentional, temporary duplication rather than a dependency on unmerged work.
- **K/T/B/4/5/D**: each axiom proved valid under its frame condition, with canonicity (the condition is also necessary) for T/B/4/5/D. Mostly `grind`; `four` is written out explicitly. `Cube.lean` assembles the 15 cube logics and the standard inclusions.
- **Logical equivalence**: `Proposition.Equiv S` is parametric in the model class `S` (previously fixed to `univ`), proved an equivalence relation and a congruence over one-hole contexts, and registered into the shared `LogicalEquivalence` framework.

## AI disclosure

Claude (Anthropic) assisted with the rebase, file transplantation, and CI verification. The Lean proofs are by the contributors listed in the file headers; AI use was limited to mechanical git work and drafting this description.
