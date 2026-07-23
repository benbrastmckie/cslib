# Phase 3 Adequacy Gate — FINAL Blocker Handoff (dispatch 3 of 3, FINAL — no dispatch 4)

- **Task**: 517 — labelled_bounded_context_cs5_completeness
- **Phase**: 3 (GATE — HARDEST NODE), `plans/01_labelled-framework.md`
- **Session**: `sess_1784127828_1f2b2f`
- **Verdict**: **GATE FAIL (FINAL).** Per explicit user authorization this was a third, extra
  bounded attempt beyond the plan's original "2 dispatches" cap. No further dispatch will be
  opened on this task. Phase 3 is `[BLOCKED]` for good; Phases 1, 2, 4 remain landed; Phase 9 is
  unreachable (confirmed by re-reading Phase 9's own dependency chain — see §4 below).

## Summary

This dispatch did **not** attempt new Lean mechanization. Instead, given the depth of subtlety
already found by two prior dispatches, it invested its entire budget in **re-deriving the
mathematics from the primary source with maximum rigor**, specifically re-reading Simpson's
Figure 6-1, the worked example, and Figure 6-2 directly from the source PDF pages (109-112,
book pp. 100-103) via the `Read` tool (not `pdftotext`, which garbles `□`/`◇` in this typeface).
This surfaced **two further, genuine corrections** to dispatch 2's scaffold that neither prior
dispatch found, **and** a clarification that **resolves** (in the sense of "shown not to be an
issue", not "mechanized") dispatch 2's own diagnosed crux (the `diaE` "z-scoping" gap). Net
effect: the problem is now understood with much greater precision than after dispatch 2, but the
remaining mechanization is **larger and more delicate** than dispatch 2's "100-200 mechanical
lines" estimate, not smaller. Given the plan's explicit "prefer an honest wall to a forced proof"
instruction (repeated verbatim by the user for this dispatch), no attempt was made to force a
proof past this point.

**Nothing new was written under `Cslib/`.** `probes/lemma612-scaffold.lean` is left exactly as
dispatch 2 produced it (still sorry-free, still axiom-clean, still a **valid but incomplete**
scaffold) — this document supersedes its "verified against the worked example" claim with a
precise correction (§1 below) rather than editing the scaffold's Lean source, to avoid leaving a
half-migrated file that could mislead a future reader into thinking the correction was applied.

## 1. NEW FINDING: `T^i` in Simpson's telescope is a *pruned* subtree, not the full one

Dispatch 2's scaffold defines `star`/`Star` using `LTree.pathTo`/`pathToList`, which return, for
each level `T^i` along the root-to-target path, the **entire, unmodified subtree** rooted at
`x_i` (all of `x_i`'s actual children, including the one continuing toward the target). Reading
Figure 6-1 directly (PDF p.109, book p.100) shows this is **wrong**:

> "`𝒢` has the form displayed in Figure 6-1 where `m ≥ 0` is the depth of `x_m` and each `T^i`
> (`0 ≤ i ≤ m`) is the finite tree with root `x_i` and `n_i` immediate subtrees `T^i_1, …,
> T^i_{n_i}` (`n_i ≥ 0`). Note that, **for `i < m`, the node `x_i` actually has `n_i + 1`
> immediate successors** for, in addition to the `n_i` apices of `T^i_1, …, T^i_{n_i}`, **there
> is also the node `x_{i+1}`**."

I.e. for `i < m`, `T^i` is **defined to exclude** the child that continues toward the target
(`x_{i+1}`) — `T^i` is `x_i`'s subtree *minus* the path-continuation branch. Only `T^m` (the
last, deepest level, at the target itself) uses **all** of its children unpruned (there being no
`x_{m+1}` to exclude).

**Confirmed numerically against the worked example** (PDF p.109, book p.100: tree `x→y, x→z→w`,
target `z`, `m=1`):
- `T^0` = `x`'s subtree **minus** the `z`-branch = `x` with only child `y`. `Γ@T^0 = (◇A⊃□□B) ∧
  ◇A` — **exactly** the given first conjunct, with **no** third `◇(Γ@z-subtree)` term. If `T^0`
  were used unpruned (as the scaffold's `pathTo` computes it), it would include `z`'s own branch
  too, giving `(◇A⊃□□B) ∧ ◇A ∧ ◇(⊤∧◇⊤)` — **not** what Simpson gives.
- `T^1 = T^m` (the target level, `i=m=1`) = `z`'s subtree **in full** (child `w` included):
  `Γ@T^1 = ⊤ ∧ ◇⊤`, matching "`the ⊤ arises from the empty conjunction of {…}@w`" and the given
  `◇⊤ ⊃ ◇B` telescoping slot.

**Why this matters, precisely**: the scaffold's `star`/`Star`, as literally written, is not
merely "differently normalized" — it produces a **strictly stronger** intermediate antecedent at
every level `i<m` (an extra `◇(Γ@(x_{i+1}'s own subtree))` conjunct). This does **not** make the
lemma false (a stronger antecedent only makes each individual `⊢antecedent⊃B` fact *easier*, via
plain `andE`-weakening: `(P⊃C) ⊢ (P∧Q)⊃C` is an IK triviality) — the risk is entirely on the
**induction's internal consistency**, not on soundness of any single instance. See §3.

## 2. RESOLVED (clarified, not mechanized): the `diaE` "z-scoping" gap dispatch 2 found

Dispatch 2's handoff (`handoffs/lemma612-final-blocker.md` §3) diagnosed `NIKAx.diaE`'s `z`
parameter as unconstrained by the bare Lean type relative to `x`, worrying about a "`z` unrelated
to `x`" sub-case with no proof strategy. Re-reading the `(◇E)` proof directly (PDF p.111-112,
book p.102-103) shows Simpson's own argument **already assumes** exactly this relationship, and
explains *why* it is licensed:

> "Suppose that the (unique) path from `x_0` to `y_j` in `𝒢` is given by `x_0Rx_1 … x_iRy_1 …
> Ry_j` where if `j>0` and `i<m` then `y_1` is different from `x_{i+1}`, and if `j=0` then by
> `y_j` we mean `x_i`."

This is licensed by the **module docstring's own convention**, restated at the top of the Lemma
6.1.2 proof (PDF p.110, book p.101): *"Notation will be kept consistent with Figure 6-1, i.e.
`𝒢` will always be assumed to be of this form."* Crucially, `NIKAx.diaE`'s two premises
(`hdia : NIKAx 𝒯 G Γ (x∶.diamond A)` and the outer conclusion `NIKAx 𝒯 G Γ (z∶B)`) use **the
same, unextended `G`** — so if the generalized induction is set up with an explicit companion
`LTree` witness `τ` satisfying `G = τ.toGraph`, `x ∈ τ.labels` (obtained from the IH applied to
`hdia`, which is a derivation over the *same* `τ`) **and** `z ∈ τ.labels` (an outer hypothesis of
the very statement being proved at this step), then **`x` and `z` are both nodes of the same
single finite tree `τ`, and therefore always have a well-defined lowest-common-ancestor (LCA)
decomposition** — this is *exactly* Simpson's assumed `x_0 … x_i, y_1 … y_j` path-with-common-
prefix, not a separate hypothesis to prove. Dispatch 2's "case 1 (`z` totally unrelated to `x`,
no proof strategy)" **cannot actually arise** once the induction is set up this way (with `τ`
threaded as an explicit generalized parameter, not inferred after the fact from `G`). This is a
genuine simplification relative to dispatch 2's diagnosis — the "three sub-cases" collapse to
**one** general dissection-at-LCA argument, parameterized uniformly by the LCA depth `i`
(`i = m` recovers dispatch 2's tractable "`z` an ancestor of `x`, or equal" cases; `i < m`
recovers Simpson's Figure 6-2 as literally drawn).

**This is progress, but it is a conceptual simplification, not a mechanization.** The LCA-based
dissection argument (Figure 6-2) still needs to be built, and — per §1 — needs to be built
against the **corrected, pruned** `T^i` representation, which the existing scaffold does not
have.

## 3. NEW FINDING: `Star_append` does not model what `boxI`/`diaI`/`diaE` actually need

Dispatch 2's `Star_append` (`probes/lemma612-scaffold.lean:577-593`) proves, as a **definitional
equality** over abstract `path : List (LTree Atom)` and a **separately-supplied** tree `t`:

```
Star Γ (path ++ [t]) A = Star Γ path (Proposition.box ((star Γ t).imp A))
```

This is true **as stated**, but it does not correspond to what `boxI`/`diaI`/`diaE` actually do
to the tree. Those rules extend the graph via `G.addEdge x y`, i.e. **attach `y` as a new child
of the existing node `x`** (`LTree.addChild t x y`). If `x` is the root of the *current* deepest
path element (`t.getLast!`), then `(t.addChild x y).pathToList y` does **not** equal
`t.pathToList x ++ [leaf y]` with the **existing** value of `t.pathToList x`'s last element
unchanged — the node representing `x` **in the new tree** now has an *extra* child (`y`), so its
value inside the path differs from its old value. Concretely: `pathTo (node x (cs ++ [leaf y]))
y` recurses into the extended children list and returns the path
`[node x (cs ++ [leaf y]), leaf y]` — the *first* entry is the **new, extended** `x`-node, not
the **old** one `Star_append`'s statement assumes. Compounding this with §1's pruning
correction: in the *correctly pruned* representation, this `x`-node, when it stops being the
last path element (because `y` is now one more level down), must have its children list
**pruned of the `y`-branch** (exactly as `T^i`, `i<m`, excludes `x_{i+1}`'s branch) — so the
"old" and "new" values of the `x`-level entry are **triply** different: (a) unpruned-with-`y`
(literal `addChild` result), (b) unpruned-without-`y` (`Star_append`'s implicit assumption), (c)
pruned-without-`y` (Simpson's actual convention). None of dispatch 2's combinators relate these.

**A correct treatment needs a genuinely new lemma** relating `pathToList` before/after
`addChild` at exactly the node being extended, phrased against the pruned representation from
§1 — this is **not** the "mechanical wiring" dispatch 2's handoff estimated at 100-200 lines; it
is itself a nontrivial structural lemma requiring its own induction (on the position of `x`
within the path/tree), on top of which the LCA-dissection argument (§2) for `diaE` specifically
must *also* be built.

## 4. Confirmed: there is no smaller target that avoids Lemma 6.1.2's full generality

Checked directly against Phase 9's own dependency chain (`plans/01_labelled-framework.md:711-714`,
re-read this dispatch): the contrapositive assembly step "`⊬_{IK+Ax(𝒯_S5)} φ ⟹
⊬_{N_IK(𝒯_S5)} x:φ`" is exactly Lemma 6.1.2's contrapositive, specialized (only externally) at
the **trivial graph**. But the specialization is only in what gets *fed in* at the top —
Lemma 6.1.2's own **proof** is by induction over arbitrary derivations, and any nontrivial
`NIKTheorem`-instance derivation will, in general, contain nested `boxI`/`diaE` applications that
grow the tree arbitrarily within their own sub-derivations even though the top-level graph
starts trivial. **The full general-`G` induction (with the corrections in §1-3) is unavoidable**;
there is no shortcut through only the trivial-graph case. Phase 9 is confirmed unreachable.

## 5. Recommendation for a hypothetical future task (if ever authorized)

This is **not** a "the theorem is false" wall — every correction found this dispatch *strengthens*
confidence the theorem is true (Simpson's own worked example checks out exactly once `T^i` is
pruned correctly, and the "z-scoping" gap dispatch 2 flagged turns out to be a non-issue given the
right induction setup). But the mechanization is larger than previously estimated. A future
attempt, if ever authorized, should:

1. **Redefine `LTree.pathTo`/`pathToList`** to return `T^i` = the *pruned* subtree (root `x_i`,
   children = all of `x_i`'s children **except** the one leading toward the target) for `i < m`,
   and the *full* subtree only at `i = m`. (Concretely: thread an "excluded child" parameter
   through the recursion, or build the pruned `LTree` value explicitly at each step.)
2. **Re-verify `star`/`Star`** against Simpson's own worked example (§1) using the corrected
   definition, by direct computation (e.g. `#eval`/`decide` on a small concrete instance, or by
   hand unfolding as done in §1) *before* re-proving any combinator.
3. **Rebuild `Star_imp1`/`Star_imp2`/`wrapClosed`** against the corrected `star`/`Star` — likely
   still provable by the same induction-on-path-list technique dispatch 2 used, since those
   lemmas are agnostic to *how* each path element's value was constructed, only to the abstract
   `star`/`Star` recursion. Re-verify this agnosticism holds under the corrected definitions
   rather than assuming it carries over.
4. **Build the `pathToList`-vs-`addChild` commutation lemma** (§3) against the corrected, pruned
   representation — this is new, nontrivial work, not "wiring."
5. **Build `LTree.toGraph`** and the generalized, `τ`-parameterized induction statement
   (`∀ τ G Γ z B, G = τ.toGraph → z ∈ τ.labels → (∀ψ∈Γ, ψ.lbl ∈ τ.labels) → NIKAx 𝒯 G Γ (z∶B) →
   IKDerivable 𝒯 (Star Γ (τ.pathToList z) B)`), proved by induction on the `NIKAx` derivation,
   `generalizing τ`.
6. **For `diaE`**: use the LCA-based dissection (§2) — obtain `x ∈ τ.labels` from the IH applied
   to `hdia` (same, unextended `τ`), compute the LCA depth `i` between `x`'s and `z`'s paths in
   `τ`, and dissect at that depth using the commutation lemma from step 4, generalized to depth
   `i` rather than dispatch 2's three separate ad hoc sub-cases.
7. **`(⊥E)`/`(∨E)`**: dispatch 2's `Star_imp2`-based tractability argument likely survives the
   corrections (it only uses the abstract path-list induction), but must be re-verified against
   the corrected `star`/`Star`, not assumed.
8. Only once all of the above compiles sorry-free should `boxI`/`diaI`/`boxE` (the remaining
   "easy" cases) be wired up — they are genuinely easy *given* step 4's commutation lemma, but
   not before it exists.

**Effort estimate for a future dispatch**: given the compounding of three independent, delicate
tree-structural corrections found across three dispatches (this one included), a realistic budget
is **at least 2-3 full dispatches** of focused mechanization, not the "1-2 dispatches" originally
budgeted by the plan — and each of steps 1-2 and 4-6 above should be dispatched and verified
**separately**, not attempted in one pass, given how much subtlety has been hiding at each layer.

## Explicit non-workarounds ruled out

- No `sorry` was added anywhere under `Cslib/` (no new Lean code was written this dispatch;
  analysis only).
- No vacuous definition was introduced.
- `probes/lemma612-scaffold.lean` is unchanged from dispatch 2 (still sorry-free, still
  axiom-clean, still a valid **partial** scaffold whose limitations are now precisely documented
  above rather than papered over).
- Nothing under `Cslib/` was modified. No `public import` line for `Labelled.Adequacy` was added
  (Phase 3 gate did not close).

## Artifacts

- This handoff document (supersedes nothing already written; dispatch 1's and dispatch 2's
  handoffs remain accurate historical records of their own findings).
- `specs/517_.../probes/lemma612-scaffold.lean` (unchanged, dispatch 2's).
- `specs/517_.../probes/adequacy-gate-probe.lean` (unchanged, dispatch 1's, still the complete
  Lemma 6.2.2 mechanization — fully reusable by any future attempt).

## Final recommendation to the orchestrator

**GATE FAIL (FINAL).** Per explicit instruction, no dispatch 4 will be opened on this task by this
agent. Phases 1, 2, 4 remain landed and valid. Phases 5-8 (the semantic spine: Prime Lemma,
canonical model, birelation, frame-class match) were **not** attempted by this dispatch (out of
this gate's scope — Phase 3 is a prerequisite-free, independently-gated node per the plan's own
wave structure; Phases 5-8 depend on Phase 4, already landed, and remain independently dispatchable
in a future task if ever authorized, *regardless* of Phase 3's fate, since they do not depend on
Phase 3). Phase 9 is unreachable and the task returns to `[BLOCKED]`, per the plan's own
Rollback/Contingency section.
