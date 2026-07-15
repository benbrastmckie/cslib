# Execution Summary: Task #517 — Track C C4 (tree surgery, the unfolding identity)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Plan**: plans/02_decomposed-track-a-b-c.md
- **Session**: sess_1784145761_061228
- **Phases executed**: Track C C4 (`LTree`/`star`/`fullSubtree`/`prune` + the unfolding identity)
  — [COMPLETED]. C5 explicitly NOT opened (H8 phase sizing / hard stop per dispatch
  instruction; C5 is the TRUE crux, HIGH risk, its own dispatch).
- **Type**: cslib

## What was done

All work lives in `probes/lemma612-scaffold.lean` (extended in place — the resume pointer left
this choice open at C4 dispatch time; extending in place avoided re-declaring `LTree`/`Label`/
`GeomAxiom`/`IKAx` in a new file).

### `star`, FIXED

The pre-existing `star` used a double-`bigAnd`: `(bigAnd labels).and (bigAnd children)`. Hand
computation against Simpson's own worked example (p.101: `(x:◇A⊃□□B, y:A ⊢_G z:◇B)* =
((◇A⊃□□B)∧◇A) ⊃ □(◇⊤⊃◇B)`) showed this produces a spurious `⊤∧(◇(⊤∧⊤))` at a label-less,
single-childed node instead of the source's plain `◇⊤` — the double-`bigAnd` version would have
**failed** the C4 success criterion. Fixed to a single `bigAnd` over the CONCATENATED list
(labels-at-the-node ++ all children's `◇`-wrapped stars); `bigAnd`'s own `[]`/singleton
short-circuiting (unchanged, pre-existing) is what collapses label-less/childless nodes to bare
`⊤` and singleton nodes to a bare conjunct — both needed for the verbatim match.

**Regression check, done before editing**: grepped the whole file for every other use of `star`;
it is referenced ONLY opaquely as `star Γ t` (applied to a variable, never pattern-matched or
`simp`-unfolded) everywhere else (`Star`, `Star_imp1`, `Star_imp2`, `wrapClosed`,
`box_mono1`/`box_mono2`). Confirmed by re-compiling the whole file clean after the fix — no
other proof needed touching.

### `prune`/`fullSubtree`, new

```lean
def prune (l : Label Atom) (pre : List (LTree Atom)) : LTree Atom := node l pre
def fullSubtree (l : Label Atom) (pre : List (LTree Atom)) (c : LTree Atom) : LTree Atom :=
  node l (pre ++ [c])
```

Children are split as `pre ++ [c]` (continuation child `c` LAST), deliberately matching
`addChild`'s pre-existing append-at-end convention (`node l (cs ++ [leaf y])`) — chosen so C5's
`addChild`/`pathSpine` commutation lemma has a consistent convention to work with, rather than
introducing a second, conflicting ordering.

### The unfolding identity — proved as `Derivable`-Iff, NOT raw `Eq`

Report 02 §2.3 states the identity informally with "=": `Γ@(fullSubtree v) = Γ@(prune v c) ∧
◇Γ@(fullSubtree c)`. **Before writing any Lean**, checked by hand whether this can be a literal
Lean `Eq`: `bigAnd`'s own definition is a right-fold peeling from the HEAD
(`φ::rest => φ.and(bigAnd rest)`), so `bigAnd(xs++[y])` and `(bigAnd xs).and y` are literally
different TERMS once `xs` has 2+ elements (`a.and(X.and y)` vs `(a.and X).and y` — an
associativity mismatch, not resolvable by `rfl`, even though they are logically equivalent).
**Conclusion**: the identity is proved as a genuine IK-derivable two-way implication
(`star_unfold_imp1`/`star_unfold_imp2`), which is also the mathematically more useful form —
Lemma 6.1.2's actual truth-lemma cases (C6-C8) will reason about `NIKAx`-derivability, not
meta-level term equality.

**New reusable infrastructure** (all generic over `𝒯 : Set GeomAxiom`, all sorry-free):
- `andI_deriv` / `andE1_deriv` / `andE2_deriv` — `AndI`/`AndE1`/`AndE2` lifted to an arbitrary
  `Deriv`-context (weakened from the closed `IKAx 𝒯` axiom instance, applied via `mp_deriv`).
- `top_deriv` — `⊢⊤` in any context (`⊥⊃⊥`, an `implyK`+`implyS` instance).
- `bigAnd_cons_of_ne_nil` — `bigAnd`'s cons-equation restated for a `rest` known
  *propositionally* nonempty (not syntactically `_::_`), needed because the induction below
  produces `rest`s of shape `xs++[y]` (always nonempty, not always syntactically cons-headed).
- `bigAnd_append_singleton_imp1`/`imp2` — **the algebraic core**: `⊢bigAnd(xs++[y]) ↔
  (bigAnd xs).and y`, by induction on `xs`, using `andI_deriv`/`andE1_deriv`/`andE2_deriv` to
  re-associate at each cons step. This is the general fact the report's "near-trivial" framing
  was gesturing at — genuinely near-trivial ONCE the AND-combinators exist, but not `rfl`.
- `star_unfold_imp1`/`star_unfold_imp2` — the tree-level identity, direct corollaries of the
  `bigAnd` lemma once `star`/`fullSubtree`/`prune`'s definitions are unfolded via
  `simp only [LTree.fullSubtree, LTree.prune, star, List.map_append, List.map_singleton,
  ← List.append_assoc]` and the `xs := labels ++ pre.map ds`, `y := ◇(star Γ c)` instantiation
  applied.

### `pathTo`/`pathToList`/`Star_append` DELETED

Per the plan's C4 entry. `pathTo`/`pathToList` (a `mutual` block) returned the FULL, unpruned
subtree at a target label — confirmed defective against Figure 6-1's caption (`i<m` nodes
exclude their path-continuation child). `Star_append` tried to solve the "peel one more path
level" problem by wrapping the appended tree in its FULL `star Γ t`, which is exactly the wrong
shape the unfolding identity now shows: pruning must happen at the NODE the continuation child
attaches to, not be deferred to a `Star`-level append lemma. Grepped the whole repo (`Cslib/` and
`specs/517_.../probes/`) for any other reference to these three names before deleting — none
found outside this file's own doc comments and other (markdown, non-Lean) task artifacts.

### Success criterion — `star_Star_worked_example`, a real theorem (not `rfl`/`decide`)

The report's suggested check was "`#eval`/`decide` reproduces Simpson's worked example
verbatim". Investigated first: `Label Atom` has no `deriving DecidableEq` anywhere in the
codebase, and the file's only decidability source is the classically-opaque
`Classical.propDecidable` local instance — so `Γ.filter (·.lbl = l)` does not literally *compute*
via `rfl`/`#eval`, even though the underlying label equalities (`Label.var i = Label.var j`) are,
in principle, decidable via `PrefixVar := ℕ`. Verified this diagnosis with a standalone scratch
probe before committing to an approach (`simp [h]` with a supplied inequality closes
`List.filter` goals over `Classical.propDecidable`-based predicates fine, regardless of the
instance's opacity, since `if_pos`/`if_neg`-style simp lemmas only need a *proof* of the
(in)equality, not a computable reduction). `star_Star_worked_example` states the exact target
(tree `x→y, x→z→w`, target `z`, `Γ = [x:◇A⊃□□B, y:A]`, using `Label.var 0..3` for `x,y,z,w`) as a
genuine `Eq` and proves it via `simp` unfolding `star`/`Star`/`bigAnd` plus the `Γ.filter`
computations — `simp [hΓ]` alone closed all four filter sub-goals (the explicit inequality
`have`s originally scaffolded for this turned out unnecessary and were removed after a
warning-driven cleanup pass; `simp`'s built-in numeral-disequality simprocs handle
`Label.var i ≠ Label.var j` directly via `injEq`). Confirms the `star` fix: with the OLD
double-`bigAnd` convention this theorem's statement would not hold (the old `T1`-formula would
have been `⊤∧(◇(⊤∧⊤))`, not `◇⊤`).

## Plan Deviations

- **`star`'s definition changed**, beyond the plan's literal "define `LTree`/`star`/
  `fullSubtree`/`prune`" wording — necessary: the pre-existing `star` (double-`bigAnd`) fails the
  plan's own stated success criterion (verbatim worked-example match), diagnosed by hand
  computation before writing any Lean. Documented in-file at `star`'s definition site and in the
  plan table.
- **Unfolding identity proved as `Derivable`-Iff, not literal Lean `Eq`** — a scope
  clarification, not a scope reduction: literal `Eq` is mathematically impossible in general
  (associativity), confirmed by hand before starting, and the `Derivable`-Iff form is what C6-C8
  will actually need (`NIKAx`-derivability reasoning, not term equality).
- **Worked-example check delivered as a real `simp`-based theorem, not `#eval`/`decide`** — the
  report's suggested mechanism does not apply given `Label`'s lack of computable `DecidableEq`;
  this was verified (not assumed) via a standalone scratch probe before committing to the
  `simp`-based route.
- C5 NOT opened, per the explicit HARD STOP instruction and H8 phase sizing.
- No `Cslib/` file was touched. Everything lives in `probes/lemma612-scaffold.lean` (pre-existing
  probe file, extended in place), honoring the zero-debt invariant. `probes/track-c-c1-tele-conj.lean`
  (C1/C2/C3) was not touched; reverified compiling clean.

## Verification

- `lake env lean specs/517_.../probes/lemma612-scaffold.lean` — exit 0, zero errors, zero
  warnings (after cleaning up unused-simp-arg lint noise in the worked-example proof).
- `lake env lean specs/517_.../probes/track-c-c1-tele-conj.lean` — exit 0 (C1-C3, unchanged,
  reverified).
- `grep -n '\bsorry\b'` on `lemma612-scaffold.lean` — zero hits (excluding doc-comment prose).
- `grep -c '^axiom'` — 2 hits, both inside doc-comment prose (`"axiom schemata..."`,
  `"axiomatization rather than..."`), zero real `axiom` declarations.
- `#print axioms` on `star_unfold_imp1`, `star_unfold_imp2`, `star_Star_worked_example`,
  `bigAnd_append_singleton_imp1`, `bigAnd_append_singleton_imp2` — all report exactly
  `[propext, Classical.choice, Quot.sound]` (the standard CSLib Metalogic/DerivationTree
  footprint via `deductionTheorem`; no new axioms).
- `git status --porcelain` — only `specs/517_.../probes/lemma612-scaffold.lean` (this dispatch's
  edit) plus task-state bookkeeping files changed under the 517 tree. `Cslib/Logics/Modal/Tableau/
  FrameSoundness.lean` and the 515-task files also show as modified in `git status`, but these
  are task-515's concurrent, unrelated, already-in-flight work (per the resume doc) — untouched
  by this dispatch. No regression risk to landed CK/CT/CS4/CS5 soundness or task-509's `cs5FC''`.

## Artifacts

- `specs/517_labelled_bounded_context_cs5_completeness/probes/lemma612-scaffold.lean` (modified:
  `star` fixed; `pathTo`/`pathToList`/`Star_append` deleted; `prune`/`fullSubtree`,
  `andI_deriv`/`andE1_deriv`/`andE2_deriv`/`top_deriv`/`bigAnd_cons_of_ne_nil`/
  `bigAnd_append_singleton_imp1`/`imp2`/`star_unfold_imp1`/`imp2`/`star_Star_worked_example`
  added; all sorry-free)
- `specs/517_labelled_bounded_context_cs5_completeness/plans/02_decomposed-track-a-b-c.md`
  (updated: C4 marked `[COMPLETED]` with the `star`-fix / `Derivable`-Iff / worked-example notes)
- `specs/517_labelled_bounded_context_cs5_completeness/handoffs/00_RESUME-HERE.md` (updated
  resume pointer, now pointing at C5 — the true crux)
- `specs/517_labelled_bounded_context_cs5_completeness/summaries/06_c4-tree-surgery-unfolding-identity-summary.md`
  (this file)
