# Phase 1 GATE-C [BLOCKED] Handoff — `nik_TS5_soundness` direct route

- **Task**: 537 — Prove the general labelled soundness direction completing Simpson 1994
  Thm 8.1.4's biconditional
- **Phase**: 1 (Decisive symmetry/clique-closure probe with hard pivot gate) — outcome
  **GATE-C**
- **Written by**: Phase 4 (BLOCKED handoff + Strategy-3 scope-reopening recommendation)
- **Date**: 2026-07-19
- **Plan**: `specs/537_labelled_cs5_general_soundness_biconditional/plans/01_general-soundness.md`

## Status: `[BLOCKED]`

Phase 1's decisive probe exhausted its bounded budget across **four independent dispatches**
(three under parent task 517, one under this task) without landing either a sorry-free proof
of exact `r`-symmetry on `cs5FCIncest` models or a concrete countermodel refuting it. Per the
plan's pre-wired pivot gate, this is a **sanctioned non-failure terminal state**, not a defect:
the direct route remains genuinely open, and the plan explicitly forbids both a fifth undirected
attempt and a strategic `sorry` as responses. The correct response is this documented `[BLOCKED]`
handoff plus a scope-escalation recommendation (below), which is what this phase records.

## The exact blocker

**Goal that could not be closed** (from `TClosure.symm` in the labelled-clique-closure
induction, on `cs5FCIncest` models):

```
cs5FCIncest r → r a b → r b a
```

i.e. exact symmetry of the accessibility relation `r`, restricted to the finitely-generated
incest-closed substructure `cs5FCIncest`, is required to discharge the `TClosure.symm`
edge-validation case en route to `nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ`.

### Wall A — exact `r`-symmetry on `cs5FCIncest` (the blocking wall, this dispatch)

Budget-exhausted probe, **not** a concrete refutation. Evidence accumulated across the fourth
dispatch (this task) on top of three prior dispatches (parent task 517):

1. **Direct proof attempt** (live `lean_goal` + `lean_multi_attempt` state, not hand analysis):
   the `hincest`/`hfour`/`hsymbox` cascade never re-pins the two original fixed points `a, b`.
   E.g. `htrans`-chasing `hab`/`hincest` produces `h7 : r b2 a` (`b ≤ b2`, a *raised* witness)
   instead of `r b a`; `hfour hab hb_b1 h1` produces `hvt : r v a` (`v ≥ a`, raised) instead of
   `r b a`. `aesop` and `tauto` both fail outright. This independently reproduces the third
   (task-517) dispatch's documented finding.

2. **Countermodel attempt 1** (hand-built, `ℕ`): `r n m := (n≥2 ∨ m≥2) ∨ n=m ∨ (n=0 ∧ m=1)`,
   checked by hand against all five `cs5FCIncest` conjuncts — **fails `htrans`**: `r 1 2` and
   `r 2 0` both hold via the `≥2` clause, forcing `r 1 0` by transitivity, which collapses the
   intended asymmetry. This is an independent construction reproducing the documented
   `hsymbox`+`htrans` collapse pattern: any naive finite/small countermodel that tries to keep
   two points asymmetric gets absorbed into symmetry once `htrans` and the box-clause
   `hsymbox` interact.

3. **Countermodel attempt 2 — NEW this dispatch (translation-invariant difference-semigroup
   argument over ℤ)**: model `r n m := (m - n) ∈ D` for a difference set `D ⊆ ℤ`. The
   `cs5FCIncest` conjuncts translate into requirements that `D` (a) contains `0` (reflexivity),
   (b) is closed under addition (transitivity: `(m-n) ∈ D ∧ (k-m) ∈ D → (k-n) ∈ D`), and (c) is
   unbounded both above and below (the `SB`/`IN` — successor/incest — requirements, translated
   into difference-set language). **Result: any additive sub-semigroup `D ⊆ ℤ` containing `0`
   that is unbounded both above and below is forced, by a Bézout-plus-scaling argument, to equal
   `g·ℤ` for some `g ≥ 1` — i.e. `D` is necessarily a full subgroup, hence symmetric
   (`d ∈ D → -d ∈ D`).** Consequence: **no translation-invariant countermodel exists** in this
   entire natural infinite family. This is a genuine new negative result ruling out one whole
   class of candidate refutations, but by construction it does **not** address the fully general
   (non-translation-invariant, arbitrary-preorder) claim — translation-invariance was an
   assumption of convenience for this construction, not a property `cs5FCIncest` forces.

4. **Zorn/chain-union pattern** (reused from `PrimeLemma.lean`'s Lindenbaum construction):
   assessed and found **structurally infeasible** within this probe's budget. `hfour`/`hsymbox`
   take their raised witness `u'` as a *hypothesis* (not an axiom-supplied existential — only
   `hincest`'s witness is existential), so there is no direct "set of reachable pairs" poset whose
   maximal element pins the two *original* fixed points `a, b` exactly. Building one from scratch
   is genuinely new, multi-dispatch-scale infrastructure (the plan's own ~150-300+ line estimate
   for Phase 2/3-sized work), not a bounded-probe-sized task.

**Net assessment of Wall A**: the exact-symmetry claim is neither proven nor refuted. The
probe closed off one infinite countermodel family (translation-invariant / difference-semigroup)
and one proof strategy (Zorn/chain-union transplanted from `PrimeLemma.lean`), narrowing but not
resolving the open question.

### Wall B — box-introduction adversarial-`u` exactness (secondary, still standing)

Independent of Wall A, `Forcing.lean:75`'s box-introduction clause quantifies the adversarial
successor `u` **universally**, so clique closure (which Wall A would supply if closed) is
**necessary but not sufficient** for the `(□I)`/`(□E)` NIK-induction cases (Phase 2's target).
Even a fully general proof of Wall A would leave Wall B — a distinct exactness gap — open. This
was established by the original H4-verified research (unchanged across a divergence audit) and
is unaffected by this dispatch's findings; it is recorded here for completeness since it means
closing Wall A alone would not complete the direct route.

## Current state: GREEN, ZERO DEBT

- **Build**: `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` —
  **green**. Phase 1's dispatch verified 732/732; this Phase-4 dispatch re-verified green at
  734/734 (job count grew due to unrelated concurrent work elsewhere in the tree; no error, only
  pre-existing lint info/warnings in `Basic.lean` unrelated to this task).
- **`sorry`**: zero tactic-level `sorry` in `Soundness.lean`. (Three textual occurrences of the
  word "sorry" in the file are docstring prose — e.g. "sorry-free `cs5_soundness_derivable_incest`"
  — not tactic uses.)
- **New axioms**: none.
- **`cs5FCIncest`**: unweakened — the definition used by the landed `cs5_soundness_derivable_incest`
  (parent task 517, `CS5Canonical.lean:373`) is untouched.
- **Preserved assets**: `cs5_soundness_derivable_incest` and all other task-517 deliverables
  (completeness direction, anti-vacuity certificate) remain sorry-free and unregressed.
- **Docstring**: the probe's findings are recorded in
  `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` under the "Fourth dispatch
  (task 537 Phase 1 probe, GATE-C)" section (already landed by Phase 1; unchanged by this
  documentation-only Phase 4).

## Recommendation: authorize Strategy 3 as a SEPARATE FOLLOW-UP TASK

Per the plan's pre-wired GATE-C routing, this Phase-4 dispatch does **not** start Strategy 3. It
recommends that the orchestrator/user authorize it as new scope:

**Strategy 3 — Simpson Ch.6 Hilbert-labelled adequacy bridge**:
`NIKTheorem TS5 φ → Derivable CS5ModalAxiom φ`, after which `nik_TS5_soundness` follows as a
one-line corollary of the already-landed, sorry-free `cs5_soundness_derivable_incest`.

- **Why a new task, not a continuation here**: parent task 517 deliberately avoided this scope
  (a labelled→Hilbert adequacy bridge is materially larger than the direct-route closure this
  plan was sized for). Authorizing it is a genuine scope escalation and a user/orchestrator
  decision, not something an implementation dispatch should decide unilaterally.
- **What it requires**: building the currently-absent `Adequacy.lean` module (the plan's Phase 5
  scaffolding: `pathSpine`/`addChild` translation machinery) plus the Phase 6 C5 commutation
  lemma, rated by the original research as the "TRUE CRUX" of the bridge at roughly **25-30%**
  success probability (source deliberately informal per the research report).
- **Do NOT start it here.** This phase's scope is documentation only.

## What this handoff is NOT

- Not a claim that exact `r`-symmetry is false — Wall A remains genuinely open.
- Not a claim that the direct route is dead — that would be GATE-B (countermodel lands), which
  did not occur. GATE-C is explicitly the "neither outcome within budget" terminal.
- Not an authorization to begin Strategy 3 — that is a follow-up task decision.
- Not a debt-introducing shortcut — no `sorry`, no axiom, no weakened definition was used to
  reach this state.

## Downstream plan phases

Phases 2, 3, 5, 6, 7 of `plans/01_general-soundness.md` remain `[NOT STARTED]`. Phase 4's own
documentation work (this handoff) is `[COMPLETED]`.
