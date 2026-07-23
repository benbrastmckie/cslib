# Phase 3 Adequacy Gate — Blocker Handoff (dispatch 1 of 2)

- **Task**: 517 — labelled_bounded_context_cs5_completeness
- **Phase**: 3 (GATE — HARDEST NODE), `plans/01_labelled-framework.md`
- **Session**: `sess_1784127828_1f2b2f`
- **Verdict**: **GATE FAIL** (this dispatch; plan allows one further dispatch, 2 of 2)

## Summary

This dispatch fully closed **Lemma 6.2.2's hard direction** (the `(R_χ)`-elimination /
Hilbert-axiom-transport step) — complete, sorry-free, axiom-clean (only `propext`). It did **not**
close **Lemma 6.1.2 / 6.2.3** (the tree internalization `(Γ⊢_G x:A)*`), which remains exactly the
node report 01 and the plan flagged as the hardest in the whole 9-phase task. Per the plan's
explicit Phase 3 failure branch, nothing is landed under `Cslib/`; the complete, sorry-free
Lemma-6.2.2 work is preserved at
`specs/517_labelled_bounded_context_cs5_completeness/probes/adequacy-gate-probe.lean` for reuse by
the next dispatch.

## What was accomplished (COMPLETE, sorry-free, reusable)

### 1. The mandated Phase-2 TClosure re-check — RESOLVED, no correction needed

Phase 2 (`Deduction.lean`) encoded Simpson's geometric rules `{(R_χ) | χ ∈ 𝒯}` via a `TClosure`
closure operator on the graph relation, flagged because report 01 cited Figure 4-3 (`:4940`) only
by location. This dispatch re-read Figure 4-3/4-4 directly from the source PDF (pages 74, via
`pdftotext -layout` and cross-checked against the OCR'd `simpson.txt`): the literal `(R_χ)` rule is
a natural-deduction rule with a **locally discharged** relational assumption (structurally like
`(⊃I)`) — e.g. for `χ_B` (symmetry): `xRy, [yRx] ⊢ w:A` discharges to `xRy ⊢ w:A` — **not** a
permanent graph extension the way `TClosure` bakes it in.

**Verdict: `TClosure` is *not* the literal Figure 4-3 rule shape, but it *is* adequate** for
Lemma 6.2.2's purposes. This was proved, not asserted: `TClosure.hilbertTransport` (see below)
shows every `TClosure`-derived edge consumed by `(□E)`/`(◇I)` can be replaced by a genuine Hilbert
derivation using the matching Figure 3-7 axiom schema plus modus ponens — exactly the content
Lemma 6.2.2 needs. The literal discharge-style `(R_χ)` rule would prove the same theorem set;
`TClosure` merely front-loads the closure into the graph instead of discharging it rule-by-rule,
and the mechanized translation shows that front-loading is harmless. **No correction to Phase 2's
`Deduction.lean` is required or recommended.**

Figure 3-7 (p. 56 of the source PDF, read directly via the `Read` tool at PDF page 65, since the
OCR text extraction garbles the box/diamond glyphs in this specific table) gives, verbatim:

```
D    ◇⊤
T    (□A ⊃ A) ∧ (A ⊃ ◇A)
B    (◇□A ⊃ A) ∧ (A ⊃ □◇A)
4    (□A ⊃ □□A) ∧ (◇◇A ⊃ ◇A)
5    (◇□A ⊃ □A) ∧ (◇A ⊃ □◇A)
```

This exactly matches (for T/B/4) `CS5ModalAxiom`'s `tBox/tDia`, `bDia/bBox`, `fourBox/fourDia`
pairs (`CS5.lean:182`) and gives the two schemas needed for `5` (Simpson's own IS5 axiomatization,
`𝒯_S5 := {χ_T, χ_5}`, distinct from CS5's `{χ_T, χ_4, χ_B}` — the two are Hilbert-equivalent via
Pacheco's `CS5 ≡ IS5`, Phase 9's job, not this gate's).

### 2. `IKAx 𝒯` — the Hilbert system `IK + Ax(𝒯)`, built via genuine reuse

Rather than a new derivation-tree type, this reuses `Cslib.Logic.Modal.DerivationTree`/`Deriv`/
`Derivable` (`Metalogic/DerivationTree.lean`), already parameterized over an arbitrary axiom
predicate. Only the axiom predicate `IKAx 𝒯` is new (intuitionistic-K base — no `peirce`/DNE —
plus the Figure 3-7 schema per `χ ∈ 𝒯`). This is a genuine reuse win the research report did not
identify (it assumed a new Hilbert system would need to be built).

### 3. `NIKAx` — `N_IK` augmented with unconditional `Ax(𝒯)`-injection

A labelled system mirroring `NIK` (Deduction.lean) exactly, except `(□E)`/`(◇I)` consume only
*literal* graph edges (no `TClosure`), and a new `ax` constructor injects any `IKAx 𝒯` instance at
any label unconditionally. This is the labelled-level target of Lemma 6.2.2.

### 4. `TClosure.hilbertTransport` + `NIK_to_NIKAx` — Lemma 6.2.2, hard direction, COMPLETE

`TClosure.hilbertTransport` proves, by induction on the `TClosure` derivation, that crossing a
`TClosure`-derived edge inside `NIKAx` can always be replaced by the matching Hilbert axiom
instance + modus ponens. The four non-`base` cases (`refl`/`symm`/`trans`/`eucl`, i.e. `T`/`B`/`4`/
`5`) each have a short, self-contained combinator argument:

- `T` (`refl`): direct application of `tBox`/`tDia` (no recursion).
- `B` (`symm`): the *dual* transport lemma to the inner edge, composed with `bDia`/`bBox`.
- `4` (`trans`): compose `fourBox`/`fourDia` with the *same-polarity* transport lemma across both
  sub-edges, chaining through the intermediate label.
- `5` (`eucl`): compose the *dual* transport across the first sub-edge with `fiveA`/`fiveB`, then
  the *same-polarity* transport across the second sub-edge.

`NIK_to_NIKAx` then translates every `NIK 𝒯 G Γ φ` derivation to `NIKAx 𝒯 G Γ φ` by structural
induction, using `hilbertTransport` at exactly the `(□E)`/`(◇I)` cases and a 1-1 constructor map
everywhere else (verified: `NIKAx` was deliberately built with the same constructor shape as `NIK`
minus `TClosure`, so this induction is a clean, total case match — no "administrative" cases were
skipped or hand-waved). **`#print axioms` reports only `propext` on both results.**

## What is BLOCKED: Lemma 6.1.2 / 6.2.3 (tree internalization)

### The goal

Simpson's Lemma 6.1.2 (`:6512`) defines, for a **finite tree** `G` and its node `x`:

```
Γ@U        = ⋀{B | y:B ∈ Γ} ∧ (□Γ@U₁) ∧ … ∧ (□Γ@U_k)   (y = root of subtree U, U₁..U_k its
                                                          maximal proper subtrees)
(Γ⊢_G x:A)* = Γ@T⁰ ⊃ ◇(Γ@T¹ ⊃ ◇(… Γ@T^{m-1} ⊃ ◇(Γ@T^m ⊃ A)…))   (T⁰..T^m = subtrees along the
                                                                    root-to-x path)
```

and proves `NIKAx 𝒯 G Γ (x∶A) → IKDerivable 𝒯 ((Γ⊢_G x:A)*)` by induction on the derivation, with
the trivial-graph specialization `(⊢_𝒯 x:A)* = ⊤ ⊃ A` closing the bridge. Simpson himself
**omits** the `(⊥E)` and `(∨E)` cases as "quite intricate because their premises and conclusion
may have prefixes arbitrarily far apart in `G`" (`:6544`), and never states the treeness invariant
as a lemma.

### Why this dispatch did not complete it (mechanized diagnosis, not a hand-wave)

I worked through what the induction actually requires, concretely, before concluding it needs
infrastructure this dispatch did not build:

1. **`Γ@U` needs the tree structure reified, not just threaded through `Graph`.** `Graph Atom` (as
   landed in `Syntax.lean`) is a bare `(X : Set (Label Atom), R : Label Atom → Label Atom → Prop)`
   pair with no finiteness or acyclicity guarantee at the type level — it is only a tree "in
   practice" for the graphs that actually arise from `Graph.trivial` + a finite chain of
   `Graph.addEdge` calls (which is what `boxI`/`diaE` do). Recursing over "all of `x`'s children in
   the FINAL tree" (needed for `Γ@U`'s `□Γ@U₁ ∧ … ∧ □Γ@U_k` conjunction) requires either (a) a
   separate reified tree/child-list data structure carried alongside each `NIKAx` judgement, with
   its own well-founded recursion, or (b) a finiteness/acyclicity typeclass on `Graph` proved
   invariant across every constructor — neither exists yet, and building either is itself a
   multi-hour undertaking (a new inductive type, or a substantial refactor of `Graph`).

2. **The "outer graph does not see inner extensions" fact makes the bookkeeping subtler than it
   first looks, not simpler.** `NIKAx`'s binary rules (`andI`, `impE`, …) type both premises
   against the *same* ambient `G` — any `boxI`/`diaE`-introduced edge inside one premise's own
   sub-derivation is invisible to the other premise and to the ambient judgement. This means a
   single label `x` can, across *different, unrelated branches* of one derivation, be the source of
   several *distinct* fresh children that never coexist in one `Graph` value — so the "tree" that
   `Γ@U` needs is best understood as attached to *each specific sub-derivation*, not as one global
   object inferred from `G` after the fact. Representing this correctly (so that `(⊥E)`/`(∨E)`,
   whose premises are typed against a context `Γ` that can carry contributions from *several*
   independently-introduced descendant labels at once) is precisely the "prefixes arbitrarily far
   apart" difficulty Simpson names, confirmed here by attempting the construction rather than
   assumed from his hedge.

3. **A concrete attempt at a shortcut failed.** I attempted to read `Γ`'s list structure directly
   as a root-to-`x` ancestor path (avoiding a separate tree type), reasoning that `diaE` only ever
   *prepends* one new-label entry `(y∶A) :: Γ`. This works *locally* for a single unbranched chain
   of `diaE` applications, but breaks as soon as `orE`/`impI`'s *same-label* local discharge
   entries (`(x∶A) :: Γ`) interleave with `diaE`'s *different-label* entries in an order that
   depends on which branch of the derivation is being examined — there is no way to tell, from `Γ`
   alone, which entries are "tree ancestors" (needing `□`/`◇` wrapping) and which are "ordinary
   local hypotheses" (needing ordinary implication discharge) without also carrying explicit
   provenance/tree data. This confirms the difficulty is structural, not a matter of finding the
   right combinator.

### What would unblock it (concrete, for the next dispatch)

- Define a small dedicated finite-tree type (e.g. `LTree Atom := node (lbl : Label Atom)
  (local : List (Proposition Atom)) (children : List (LTree Atom))`), and **co-index** every
  `NIKAx` judgement relevant to the induction with an explicit `LTree` witness (built alongside the
  derivation, not derived from `Graph` after the fact) recording, for the *specific* sub-derivation
  in view, which descendant labels its `Γ` entries came from and where they sit.
- Prove `Γ@U`/`(Γ⊢_G x:A)*` as structural recursion on that `LTree`, not on `Graph`.
- Attempt `(⊥E)`/`(∨E)` **last**, after every other case is closed against the `LTree` scaffold —
  Simpson's own remark that their difficulty resembles `(◇E)`'s (which *is* written out, `:6544`)
  suggests the scaffold, once built, may make them tractable rather than intractable.
- `TClosure.hilbertTransport`/`NIK_to_NIKAx` (this dispatch's complete result) compose directly
  with whatever `NIKAx`-level internalization the next dispatch builds — no rework needed there.

### Explicit non-workarounds ruled out

- No `sorry` was added anywhere under `Cslib/` (the file was removed from `Cslib/` entirely rather
  than left partially complete there).
- No vacuous definition (`def X := True`, etc.) was introduced.
- The `probes/adequacy-gate-probe.lean` file is itself sorry-free — it simply lives outside
  `Cslib/` because the *whole* Phase 3 gate did not close this dispatch, per the plan's explicit
  failure-branch instruction ("Land NOTHING under `Cslib/` for this phase").

## Artifacts

- `specs/517_labelled_bounded_context_cs5_completeness/probes/adequacy-gate-probe.lean` — the
  complete, sorry-free Lemma 6.2.2 mechanization (`IKAx`, `NIKAx`, `TClosure.hilbertTransport`,
  `NIK_to_NIKAx`). Standalone-compiles clean via `lake env lean` (verified).
- This handoff document.

## Recommendation to the orchestrator

**GATE FAIL (dispatch 1 of 2).** The plan permits one further dispatch. Given the concrete
diagnosis above (a dedicated `LTree` scaffold is the missing piece, not a vague "needs more
thought"), a second dispatch has a clear, bounded starting point. If the orchestrator judges the
`LTree` scaffold + `(⊥E)`/`(∨E)` reconstruction to exceed a second bounded attempt's budget, the
plan's Rollback/Contingency section is explicit: Phases 4-8 (the semantic spine) remain
independently valuable and should proceed; Phase 9 becomes unreachable; the task returns to
`[BLOCKED]` with this handoff as the documented obstruction.
