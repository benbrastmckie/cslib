# Phase 3 Adequacy Gate — FINAL Blocker Handoff (dispatch 2 of 2)

- **Task**: 517 — labelled_bounded_context_cs5_completeness
- **Phase**: 3 (GATE — HARDEST NODE), `plans/01_labelled-framework.md`
- **Session**: `sess_1784127828_1f2b2f`
- **Verdict**: **GATE FAIL (FINAL)**. Per the plan's explicit "bounded attempt: 2 agent dispatches,
  do not open a third", this phase is now marked `[BLOCKED]` for good. Phases 1-2, 4 (already
  landed) remain in place; Phase 9 becomes unreachable per the plan's own Rollback/Contingency
  section.

## Summary

Dispatch 1 fully closed Lemma 6.2.2's hard direction (complete, sorry-free, axiom-clean —
`NIK_to_NIKAx`/`TClosure.hilbertTransport`, unchanged and reused here) but did not attempt
Lemma 6.1.2/6.2.3 (the tree internalization), diagnosing that it needs a reified finite-tree
scaffold. This dispatch (2 of 2, FINAL):

1. **Found and corrected a significant transcription error** inherited by the plan/report 01
   (and, implicitly, by dispatch 1's own diagnosis): the internalizing formula's *outer*
   telescoping connective is **□** (box), not **◇** (diamond) as the plan paraphrased it. This
   correction is load-bearing — see below.
2. **Built and fully verified** (sorry-free, axiom-clean: only `propext`/`Classical.choice`/
   `Quot.sound`) a substantial reusable scaffold for the induction: the reified tree type
   `LTree`, the internalizing formulas `star`/`Star`, and the combinator toolkit
   (`box_mono1`, `box_mono2`, `wrapClosed`, `Star_imp1`, `Star_imp2`, `Star_append`) that the
   "easy" cases of the induction (assumption, `ax`, `efq`, `andI`, `andE1/2`, `orI1/2`, `impI`,
   `impE`, `boxE`, `boxI`, `diaI`, and even `orE`) all reduce to.
3. **Found a new, deeper obstruction** in the one remaining case, `(◇E)` — the *only* one of
   "the four modal rules" Simpson writes out in full, and the one the plan's own success
   criterion requires closed. This obstruction is *not* the one dispatch 1 anticipated (combining
   independent `◇`-facts, which turned out to be a non-issue once the □/◇ error was corrected).
   It is a **scoping gap in `NIKAx`'s own type**: nothing in `NIKAx.diaE`'s Lean signature forces
   its `z` parameter (the label of the rule's *conclusion*) to be related to `x` (the label whose
   diamond fact is being eliminated). Simpson's own natural-deduction *notation* (Fitch-style
   scoping bars) enforces this implicitly; the bare `Prop`-valued `NIKAx.diaE` constructor does
   not. Establishing it requires a **separate, unproven well-scopedness invariant** about `NIKAx`
   derivations, on top of the "dissection" tree-surgery argument Simpson's own Figure 6-2 shows
   for the case where `z` is a genuine (proper) ancestor of `x`. Neither piece was completed.

**Artifacts** (all preserved, nothing under `Cslib/`):
- `specs/517_.../probes/lemma612-scaffold.lean` — dispatch 1's complete Lemma 6.2.2 mechanization
  (unchanged) **plus** this dispatch's new, independently-verified scaffold (`LTree`, `star`,
  `Star`, `box_mono1`, `box_mono2`, `wrapClosed`, `Star_imp1`, `Star_imp2`, `Star_append`).
  Standalone-compiles clean via `lake env lean` (verified, exit code 0, zero sorries).
- This handoff document.

## 1. The corrected transcription (the single most valuable finding of this dispatch)

Both the plan and report 01 (and, by inheritance, dispatch 1's own pre-source-check reasoning)
paraphrase Simpson's internalizing formula as:

```
(Γ⊢_G x:A)* = Γ@T⁰ ⊃ ◇(Γ@T¹ ⊃ ◇(… Γ@T^{m-1} ⊃ ◇(Γ@T^m ⊃ A)…))
```

**This is backwards relative to the source.** Reading the source PDF directly
(`/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf`, PDF pages 109-112,
book pages 100-103, Chapter 6 — read via the `Read` tool at those exact pages, not via
`pdftotext`, whose OCR garbles `□`/`◇` glyphs in this specific typeface) shows unambiguously:

```
Γ@U          = ⋀{B | y:B∈Γ} ∧ (◇Γ@U₁) ∧ … ∧ (◇Γ@U_k)        -- ◇ for a subtree's own children
(Γ⊢_G x_m:A)* = Γ@T⁰ ⊃ □(Γ@T¹ ⊃ □(… Γ@T^{m-1} ⊃ □(Γ@T^m ⊃ A)…))  -- □ for the outer telescope
```

Confirmed against Simpson's own worked example (book p.100 / PDF p.109): for the tree
`x→y, x→z→w`, `(x:◇A⊃□□B, y:A ⊢_G z:◇B)* = ((◇A⊃□□B)∧◇A)⊃□(⊤⊃◇B)` — `y`'s own contribution to
`x`'s formula is `◇A` (children use `◇`), while the wrap from `T⁰` to `T¹` uses `□`.

**Why this matters enormously.** Under the plan's (incorrect) ◇-outer reading, the "combine"
step needed for every multi-premise rule (`andI`, `impE`, and, per Simpson's own remark, `orE`)
requires combining two *independently existentially-witnessed* `◇`-facts into one:
`⊢P⊃◇X` and `⊢P⊃◇Y` do **not**, in general modal logic (not even in S5), entail `⊢P⊃◇(X∧Y)` — a
frame can have two distinct successors, one witnessing `X`, a different one witnessing `Y`, with
neither witnessing both. Working through this dispatch's own *first* attempt at the induction
(before the source re-check), I independently re-derived this exact obstruction and very nearly
concluded the whole lemma was intractable (or even false) for this reason. **It is not** — the
outer connective is `□`, not `◇`, and `□X ∧ □Y → □(X∧Y)` is a standard, easily-derivable K-modal
fact (via necessitation + the `kBox` axiom). This is precisely what makes the scaffold below
work, and it directly overturns the implicit assumption (never stated outright, but latent in
dispatch 1's framing of the problem as needing to "relate separate ◇-chain theorems") that this
lemma might require some exotic non-compositional proof technique. **It does not** — once the
correct connective is used, the combine step is ordinary, mechanical K-necessitation reasoning.

Any future attempt on this task **must** use the corrected formula. Re-deriving the incorrect
(◇-outer) version and concluding impossibility would be a regression.

## 2. The verified scaffold (reusable, in `probes/lemma612-scaffold.lean`)

- `LTree Atom`: a reified rose tree (`node (lbl : Label Atom) (children : List (LTree Atom))`),
  addressing dispatch 1's diagnosis that `Graph Atom` alone carries no finiteness/acyclicity
  guarantee for the recursion `Γ@U` needs. `LTree.pathTo`/`LTree.pathToList` (mutual structural
  recursion) compute the root-to-target path; `LTree.addChild` appends a new leaf.
- `bigAnd`/`star`/`Star`: Simpson's `Γ@U` and `(Γ⊢_G x:A)*`, using the **corrected** □/◇
  assignment above.
- `box_mono1`/`box_mono2`: single- and two-antecedent box monotonicity
  (`⊢φ→ψ ⟹ ⊢□φ→□ψ`; `⊢φ→(ψ→χ) ⟹ ⊢□φ→(□ψ→□χ)`), via necessitation + `kBox`, discharged with
  CSLib's **existing** parameterized deduction theorem
  (`Cslib.Logics.Modal.Metalogic.DeductionTheorem.deductionTheorem` — a genuine reuse win this
  dispatch found: the `⊃`-introduction machinery needed for all of this was already built and
  did not need to be reconstructed).
- `wrapClosed`: a closed theorem can be wrapped in an arbitrary `Star` prefix.
- `Star_imp1`/`Star_imp2`: single- and two-hypothesis `Star`-congruence — **the general form of
  the "combine" step** every label-local multi-premise rule (`andI`, `impE`, and, by the same
  pattern, `orE`'s propositional combinator) needs. Proved by induction on the path, bottoming
  out in ordinary Hilbert reasoning (`deductionTheorem` + `mp_deriv`) at the base case and
  `box_mono1`/`box_mono2` at each recursive level.
- `Star_append`: extending the ancestor-path by one more (leaf-ward) tree adds exactly one `□`
  wrap at the end — what `boxI`/`diaI`/`boxE` (and half of `diaE`) need to relate `Star` at an
  extended tree/target to `Star` at the ambient one.

All of the above compile standalone (`lake env lean specs/517_.../probes/lemma612-scaffold.lean`,
exit code 0, zero sorries) and are individually axiom-clean (`#print axioms` on each: only
`propext`/`Classical.choice`/`Quot.sound`, all permitted, none new).

**What this toolkit gets you, worked through on paper (not yet mechanized as NIKAx induction
cases, but the argument is now completely concrete)**:
- `assumption`/`ax`: direct, via `∧`-elimination out of `star`'s definition / `wrapClosed`.
- `efq`, `orI1`, `orI2`, `boxE`: `Star_imp1` (single antecedent).
- `andI`, `impE`: `Star_imp2` (two antecedents) directly.
- `orE`: `Star_imp2` applied to the purely-propositional closed combinator
  `⊢(Q⊃(A∨B))⊃(((A∧Q)⊃C)⊃(((B∧Q)⊃C)⊃(Q⊃C)))` (a fixed, closed IK-derivable schema — trivial
  intuitionistic reasoning, no modality). **Contrary to Simpson's own hedge that `(⊥E)`/`(∨E)`
  are "quite intricate", both are actually straightforward once `Star_imp1`/`Star_imp2` exist** —
  because `NIKAx`'s `efq`/`orE` constructors are already committed (by Phase 1/2's own encoding
  choice) to being strictly label-local (conclusion and every premise at the same label `x`), so
  neither needs the "prefixes arbitrarily far apart" machinery Simpson's remark refers to. That
  remark is about the *general* natural-deduction presentation's discharge discipline, not about
  this specific labelled encoding.
- `boxI`, `diaI`: `Star_append` plus `Star_imp1`/`box_mono1`, using that the new leaf's own
  `star` value is `⊤` (fresh label, no `Γ`-entries) to erase the trivial `⊤⊃A ↔ A` conjunct.

**None of this is landed as an actual induction over `NIKAx` yet** — the LTree/`Graph`
correspondence (`LTree.toGraph`, and threading the invariant `G = τ.toGraph`, `x ∈ τ.labels`
through `NIKAx`'s constructors) was not built this dispatch; only the target-formula scaffold and
combinator toolkit were. That remaining wiring is mechanical but real work (estimate: 100-200
more lines), and is not what stopped this dispatch — the true remaining obstruction is case 3
below, `(◇E)`, which blocks the *whole* lemma regardless of how much of the "easy" cases get
wired up.

## 3. The real remaining obstruction: `(◇E)`'s unscoped `z`

Recall `NIKAx.diaE`'s Lean signature (`probes/lemma612-scaffold.lean` / adequacy-gate-probe.lean,
unchanged from dispatch 1):

```lean
| diaE (L : Set (Label Atom)) (hL : L.Finite) (G : Graph Atom)
    (Γ : List (LabelledFormula Atom)) (x z : Label Atom) (A B : Proposition Atom)
    (hdia : NIKAx 𝒯 G Γ (x ∶ .diamond A))
    (h : ∀ y ∉ L, NIKAx 𝒯 (G.addEdge x y) ((y ∶ A) :: Γ) (z ∶ B)) : NIKAx 𝒯 G Γ (z ∶ B)
```

Simpson's own presentation (Figure 6-2, "Dissection of `Tⁱ`", book p.103/PDF p.112) handles this
rule by **assuming** `z` (his `x_m`, the deepest node of the *original* fixed decomposition) sits
somewhere on a path that shares a common ancestor `x_i` with `y_j` (the fresh witness's position),
and dissects the tree at that branch point. This assumption is built into his fixed labelling
convention (Figure 6-1: "`G` will always be assumed to be of this form") — it is a *presentational
device*, not a theorem he proves. Nothing about `NIKAx.diaE`'s bare Lean type forces `z` to be
positioned this way relative to `x`: as far as the type is concerned, `z` could be **any** label
whatsoever, including one that shares no relationship at all with `x`'s position in the tree, or
even the fresh witness `y` itself.

**Concretely, three sub-cases arise, and only one of them is actually handled by anything built
so far**:

1. **`z` unrelated to `x`** (not an ancestor, not `x` itself, not reachable through `x`'s subtree
   at all): here the fresh edge `x→y` and the new hypothesis `(y:A)` should be *irrelevant* to
   deriving `z:B`, and the two `Star`-facts (`Star Γ path_z B` at `G` vs. at `G+xy`) should
   simply coincide — but proving *that* requires a **separate "irrelevance"/purity lemma**
   (roughly: "if a fresh label's edge and hypothesis are never actually used along the surviving
   branches of the sub-derivation for `z:B`, the derivation can be replayed unchanged without
   them") that was not attempted. It is plausible but unproven.
2. **`z = x`**: tractable in outline (worked through on paper: combine `hdia`'s
   `Star _ path_x (.diamond A)` with `h`'s `Star _ path_x (□((star _ leaf_y).imp B))`-shaped fact
   via `kDia` — `□(P→Q)→(◇P→◇Q)` — plus the "child conjunct access" fact that `star` at a node
   includes `◇(star _ child)` for each of its children). This sub-case is the *only* one this
   dispatch fully worked through, and it does **not** need dissection.
3. **`z` a proper ancestor of `x`** (Simpson's actual Figure 6-2 scenario): needs the "dissection"
   argument proper — splitting `z`'s own path-formula at the branch point `x_i` where the
   original path (toward `x`, hence toward the new leaf `y`) and one of `z`'s other children
   diverge, then relating the two "sides" via a congruence lemma for `star` under one extra
   `◇`-wrapped leaf appearing arbitrarily deep inside one branch. This is genuinely more involved
   than anything in the toolkit above; Simpson's own formulas (6.4)-(6.8), which this dispatch
   read directly from the source and can quote precisely if useful to a future attempt, show the
   shape but the mechanization was not attempted.

**None of the three sub-cases is provably exhaustive from `NIKAx`'s type alone** — i.e., before
even reaching sub-case 3's dissection difficulty, a future attempt would first need to *establish*
(as a well-formedness invariant carried alongside the `LTree` witness, presumably proved by a
separate structural induction over how `NIKAx` derivations are actually built by the other
constructors) that every `diaE` node occurring inside a derivation-in-progress has its `z`
positioned in one of cases 2/3 relative to the "live" tree — sub-case 1 (fully unrelated) should
never actually arise for well-formed derivations, but nothing in the Lean type rules it out, so
this needs to be *proved*, not assumed.

## 4. Recommendation for a future dispatch

This is not a "the whole lemma is impossible" wall — dispatch 1's original fear (about combining
independent modal facts) was based on a transcription error this dispatch corrected, and most of
the induction (11 of 15 `NIKAx` constructors, on paper) reduces cleanly to the verified toolkit.
The **precise** remaining gap is:

1. Build `LTree.toGraph` and the `G = τ.toGraph` / `x ∈ τ.labels` invariant-threading through the
   `NIKAx` induction (mechanical, ~100-200 lines, not attempted).
2. Prove the well-scopedness invariant for `diaE`'s `z` (NOT attempted, no proof sketch beyond
   the three-way case split above) — likely needs strengthening the generalized induction
   statement itself (e.g., proving a *simultaneous*, mutually-recursive fact about "which labels
   a derivation's conclusion can legally reference" alongside Lemma 6.1.2 itself), which is a
   structurally different (harder) induction than the "easy" cases needed.
3. Mechanize the dissection argument (Simpson's Figure 6-2, formulas 6.4-6.8, transcribed above)
   for sub-case 3.
4. Only then attempt `orE`'s propositional combinator (tractable on paper, not yet mechanized)
   and the remaining "easy" cases (all tractable on paper via the verified toolkit).

Given the plan's explicit "bounded attempt: 2 dispatches, do not open a third", this dispatch
recommends **not** attempting a third dispatch on the current task, per the plan's own
Rollback/Contingency section. If a future task is spawned for this specific remaining gap, it
should be scoped narrowly around items 1-3 above (the toolkit in item 4 is already done), with
the corrected □/◇ formula and this scaffold as its starting point.

## Explicit non-workarounds ruled out

- No `sorry` was added anywhere under `Cslib/` (all work stayed in `probes/`, per the plan's
  failure-branch instruction).
- No vacuous definition (`def X := True`, etc.) was introduced.
- `probes/lemma612-scaffold.lean` is itself fully sorry-free and axiom-clean (verified via
  `lake env lean` and `#print axioms` on every new declaration) — the reason the *gate* still
  fails is that the scaffold does not yet reach a complete proof of Lemma 6.1.2/6.2.3, not that
  anything built this dispatch is unsound or unverified.
