# Continuation Handoff 03: Necessity-Transfer Conjecture Attempted, Insufficient

## State at end of this dispatch

- Phases 1-2: landed, committed, CI-green (unchanged).
- Phase 3 (`cs5Combined_seed_excludes`): still `[PARTIAL]`. This dispatch attempted the
  continuation handoff's (02) recommended first lead — the "necessity transfer" conjecture — per
  the resume instructions. **The conjecture, as literally stated (`⊢CS5Combined τLΨ → τRA` implies
  `⊢CS5 Ψ → □A`), was NOT proved or refuted. A concrete, sorry-free, weaker byproduct was proved
  instead (`cs5Combined_necTransfer`), and shown to be provably INSUFFICIENT for closing the
  obligation** — see below. Phases 4-5 remain `[NOT STARTED]`.

## What was landed (sorry-free, axiom-clean: only `propext`/`Classical.choice`/`Quot.sound`)

**`cs5Combined_necTransfer`** (`CS5Canonical.lean`, appended after the box-equivalence lemmas):

```lean
theorem cs5Combined_necTransfer {Ψ A : Proposition Atom}
    (h : Deriv (@CS5Combined Atom) [] ((Ψ.map Sum.inl).imp (A.map Sum.inr))) :
    Deriv (@CS5ModalAxiom Atom) [] ((Proposition.box Ψ).imp (Proposition.box A))
```

Derivation: necessitate the hypothesis (`⊢Combined τLΨ → τRA`, empty context, so `necessitation`
applies), `K`-distribute (`.base (.k _ _)`) to get `⊢Combined □τLΨ → □τRA`, chain with the
already-landed box-equivalence lemma `cs5Combined_boxR_imp_boxL A` (`□τRA → □τLA`) via
`cs5Combined_impTrans`, giving `⊢Combined □τLΨ → □τLA` — both sides purely `τL`-tagged (box
commutes with `.map`, `Proposition.map_box`/`map_imp` are `rfl`), so this collapses via the
already-landed `cs5_collapse_of_L_deriv` (`Γ := []`) to `⊢CS5 □Ψ → □A`.

**Why this is INSUFFICIENT** (documented in the theorem's docstring in `CS5Canonical.lean`):
taking `Ψ := A` — exactly the hardest / most relevant case (`A ∈ H ∧ □A ∉ H` is the whole
difficulty of the obligation) — makes the conclusion `⊢CS5 □A → □A`, which is **trivially true**
(reflexivity of `→`, an `implyK`/`implyS`-derivable tautology) regardless of `A` or `H`. So this
consequence can never rule out `Ψ := A`, and hence cannot by itself refute
`cs5Combined_seed_excludes`.

## Why the algebraic route cannot be strengthened further (root-cause finding)

`necessitation` in `CS5Combined`'s derivation system only fires on EMPTY-CONTEXT derivations and
boxes the WHOLE hypothesis `τLΨ → τRA` uniformly. There is no way, using only
`necessitation`/`K`/`crossLR`/`crossRL`/the box-equivalence lemmas, to introduce a box on `Ψ`
alone while leaving `A` unboxed (or vice versa) — every combination explored this dispatch
(chaining through `crossRL A` directly to get `⊢CS5 □Ψ → A`; chaining through the box-equivalence
lemmas to get the landed `⊢CS5 □Ψ → □A`; applying the `Sum.inl ↔ Sum.inr` swap-duality
automorphism to (i) to get `⊢Combined τRΨ → τLA`) lands on a **boxed-antecedent** consequence,
never on a bare-`Ψ` (unboxed) consequent. This is a structural fact about the proof system, not a
failure of cleverness in chaining — the *only* introduction rule for `□` is `necessitation`
(applies to the whole current goal) and the two cross axioms (both require a *boxed* premise).
**Conclusion: the necessity-transfer conjecture, if true, requires a fundamentally different
technique** — the derivation-height induction of report 02 §5 (structural induction on the actual
`DerivationTree`, which can exploit information beyond "provable-in-the-axiom-algebra", e.g.
exactly which assumptions/subformulas were used), or equivalent canonical-scale semantics.
**Do not re-attempt the necessitation/K/cross-axiom/box-equivalence algebraic route in a future
dispatch — it is exhausted and provably capped at boxed-antecedent consequences.**

## Additional finding: semantic/model routes need theory-level, not atom-level, correlation

Independently (pen-and-paper, not mechanized — no Lean code attempted for this, since it would be
a separate large "no model of any kind can validate this" universally-quantified impossibility
proof, out of scope for this dispatch): confirmed that **any** semantic route (not just
homomorphic-translation models, which report 02 §5 already ruled out) requires the two-sorted
correlation between "necessary L-content" and "R-content" (and vice versa) to be validated at
EVERY world for EVERY compound formula `B` (not just atoms), since `crossLR`/`crossRL` are axiom
SCHEMAS ranging over all `B : Proposition Atom`. Checking this at the atom level and hoping it
extends compositionally to compound `B` fails already at `B = p ∨ q`-style formulas (box does not
distribute over `∨`, matching report 02 §5's `□(p∨q) → (□p∨□q)` non-theorem finding, but here
arising from semantic-model-construction directly, not from a translation function). This means
**any adequate semantic model needs a genuinely canonical (theory-based, Lindenbaum-scale)
construction, not an atom-indexed valuation** — sharpening report 02 §4's conclusion (which
focused on single-witness models) to rule out ANY finite/atom-based model attempt, not just the
specific ones already tried. This strengthens the case that route 1 (semantic) is a dead end at
anything short of full canonical-model scale, which report 02 already flagged as circular
("adjacent to the very box-backward completeness that is open").

## What remains open

Exactly as before: `τR A` excluded from `modalDeductiveClosure CS5Combined (τL '' H)`, reducing to:
for all `Ψ ∈ H`, `⊬CS5Combined τL(Ψ) → τR(A)`. **Both pre-specified routes (report 02 §4 semantic,
§5 proof-theoretic-projection/algebra) are now exhausted at the "easy" level; only the full
derivation-height induction on `CS5Combined`'s 5 `DerivationTree` rule cases (`ax`, `assumption`,
`modus_ponens`, `necessitation`, `weakening`) remains untried**, per report 02 §5's sketch
(designing an invariant `Φ` that is closure-stable and gives: `φ` R-pure ⟹ underlying formula in
`HR`; `φ` L-pure ⟹ underlying formula in `H`; covering the MIXED case via the
`crossRL`-conservativity lever `HR ⊆ H`). This was not attempted directly this dispatch (budget
was spent confirming the necessity-transfer lead was a dead end, and mapping the semantic-route
impossibility more precisely) — report 02's own estimate (~150-220 GENUINELY NOVEL lines, "not
sketched in enough detail to mechanize directly") stands, and a THIRD dispatch's failure to close
this via either of the two "cheaper" routes raises the empirical estimate of the remaining
difficulty; it is now clearer that **only** the derivation-height induction can close this,
not any shortcut.

**Fallback still available** (per plan, if genuinely exhausted after a good-faith attempt at the
derivation-height induction): a PROVED mechanized obstruction theorem showing the sorts DO
collapse. Per report 02's ~85-90% confidence the underlying CLAIM is TRUE, and this dispatch's own
failure to find ANY leak (in fact, actively confirming several NEW reasons the sorts do NOT
trivially collapse — the necessitation-transfer byproduct itself only ever produces TRUE
statements like `□A→□A`, never a false/contradictory one, which is itself weak evidence FOR
non-collapse, not against it), this remains assessed as UNLIKELY to be the right outcome.

## Files touched this dispatch

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — added `cs5Combined_necTransfer`
  plus its documenting section header, appended after the box-equivalence lemmas.
- `specs/512_cs5_box_backward_atom_sum_completeness/handoffs/03_necessity-transfer-attempted.md`
  (this file).

## Verification commands (all run this dispatch, all green)

```bash
cd ~/Projects/cslib
lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical   # green
lake build                                                          # full project green
lake test                                                           # green
lake exe checkInitImports                                           # clean
lake exe lint-style Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean  # clean
grep -n "\bsorry\b" Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean  # none (only in prose)
# lean_verify Cslib.Logic.Modal.cs5Combined_necTransfer -> propext, Classical.choice, Quot.sound (clean)
```

## Next dispatch instructions

1. Read this handoff, handoff 02, and report 02 in full before writing any code.
2. Do NOT re-attempt: the necessitation/K/cross-axiom/box-equivalence algebraic route (exhausted,
   provably capped at boxed-antecedent consequences — see above); any homomorphic/compositional
   translation; any atom-indexed semantic model (mirrored, L-uniform, naive 2-point, naive
   identify-both-copies) — all confirmed dead ends across three dispatches now.
3. Attempt the derivation-height induction on `CS5Combined`'s `DerivationTree`/`Deriv` structure
   directly (5 rule cases: `ax`, `assumption`, `modus_ponens`, `necessitation`, `weakening` — see
   `Cslib/Logics/Modal/Metalogic/DerivationTree.lean:134-152` for the exact constructors). Budget
   ~150-250 lines; report 02 §5 gives the invariant sketch (`Φ` closure-stable across mixed
   `modus_ponens`, using `HR ⊆ H` as the `crossRL`-conservativity lever for the cross-axiom
   cases). This is now the ONLY unexplored route.
4. Zero-debt holds throughout: no `sorry`, no new axiom. If this dispatch's budget is exhausted
   again without closing the obligation, land whatever builds green, update this handoff, and
   keep Phase 3 `[PARTIAL]` (not `[BLOCKED]` unless a genuine obstruction is PROVED — and per
   accumulating evidence across three dispatches, a proved obstruction looks increasingly
   unlikely to be the correct outcome; do not manufacture one).
