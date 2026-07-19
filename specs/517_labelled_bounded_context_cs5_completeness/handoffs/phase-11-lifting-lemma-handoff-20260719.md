# Task 517 Continuation Handoff — Phase 11.1 (Interpretation Machinery), 2026-07-19

## Status Summary

- **Phase 10** (`cs5_completeness`, labelled-system completeness, Option B): **[COMPLETED]**,
  landed, committed (`a7830559`), sorry-free, axiom-clean (`[propext, Classical.choice,
  Quot.sound]`). File: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Completeness.lean`.
- **Phase 11** (full labelled soundness): **[IN PROGRESS]**. Sub-phase 11.1 partially landed: the
  interpretation-lifting building block `cs5FCIncest_lift` is sorry-free and axiom-free, in a new
  file `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`. The main soundness
  induction, Phase 11.2 (TClosure validation), and Phase 11.3 (anti-vacuity) are **not yet
  attempted**.
- **Phase 12** (bookkeeping): correctly **not started** — the plan's own sequencing
  (`Depends on: 10, 11`) explicitly defers it until Phase 11 lands, so its `state.json`
  blockers-rewrite and docstring-fix tasks reflect the *final* result, not an intermediate state.
  Do not attempt Phase 12 before Phase 11 completes.

**Next dispatch should set `next_phase: 11` (sub-phase 11.1 continuation)**, per the
`continuation_context` below and in `.orchestrator-handoff.json`.

## Why Phase 11 is genuinely harder than the plan's original sizing suggested — and why it is
## NOT blocked

The plan (Phase 11's Non-Goals / risk notes) correctly flagged Simpson's own remark that labelled
soundness is "more difficult" than completeness, citing his `(R𝒯)`-rule "non-tree excursions"
(`L1423`). This dispatch did the required `--lit` read of Simpson's actual §8.1.2 soundness proof
(reflowed `L1367-1425`, `simpson_1994_intuitionisticmodallogic.reflowed.md`) and found the
difficulty is **deeper than the plan's phrasing implied**:

1. Simpson's Theorem 8.1.4 is stated **only for `G` a tree** — general-graph soundness is FALSE
   for his system (his Figure 8-1 gives an explicit counterexample for non-tree `G`).
2. His *direct* natural-deduction soundness argument (as opposed to the "easiest proof" detour
   through a separate modified sequent calculus `L_m(𝒯,∅)`, which CSLib does not have and building
   it is a much larger undertaking) needs the **Lifting Lemma** (8.1.3): given any interpretation
   `[-]` of a tree `G`, any `x ∈ G`, and any `w ≥ [x]`, there is a coherently-raised
   reinterpretation `[-]'` with `[x]' = w` and `[z]' ≥ [z]` for every `z ∈ G`.
3. Simpson's own proof of the Lifting Lemma uses his birelational models' `F1`/`F2` confluence
   conditions. **CSLib's target semantics for this task (`CKForces`, `Forcing.lean`) is
   deliberately built WITHOUT `F1`/`F2`** — this is not an oversight, it's why `Forcing.lean`
   exists at all (bare `CK` is otherwise *incomplete* relative to confluent models; see that
   file's own module docstring). So a literal transcription of Simpson's Lifting Lemma proof is
   not available for `CKValidFC`/`cs5FCIncest`.

**The good news, established this dispatch (not merely assumed)**: a forked sub-agent verified,
by direct hand-derivation, that `cs5FCIncest`'s own conjuncts (`cs5Incest` + `r_symBox`, chained
by transitivity of `≤`) derive exactly the single-edge "F2-analogue" the Lifting Lemma needs:

```
cs5FCIncest_lift : ∀ {World} [Preorder World] {r : World → World → Prop},
  cs5FCIncest r → ∀ {w u w'}, r w u → w ≤ w' → ∃ u', u ≤ u' ∧ r w' u'
```

Derivation (landed, sorry-free, in `Soundness.lean`):
1. `cs5Incest hwu : ∃ u₁, u ≤ u₁ ∧ r u₁ w` (apply `cs5Incest` to `hwu : r w u`).
2. `r_symBox hu₁w hww' : ∃ t, r w' t ∧ u₁ ≤ t` (apply `r_symBox` to `hu₁w : r u₁ w` and
   `hww' : w ≤ w'`).
3. `⟨t, hu_u₁.trans hu₁t, hw't⟩ : ∃ u', u ≤ u' ∧ r w' u'`.

This means Phase 11 **is mathematically tractable** — not a research-territory blocker — but the
full construction genuinely requires porting/adapting Simpson's Lifting-Lemma *technique* (not
his proof) to the confluence-free `CKForces` setting, which is substantial proof engineering, not
a one-shot composition like Phase 10 was.

**Decision made this dispatch**: do NOT mark Phase 11 `[BLOCKED]`. Nothing here is stuck, missing
a mathlib lemma, or mathematically unclear — the architecture below is a concrete, executable
plan. This is a scope/budget continuation (matching the plan's own "1-2 dispatches" estimate for
11.1 alone), handled via the orchestrator's normal multi-dispatch continuation path, not the
Escalation Protocol.

## What remains — concrete plan for the next dispatch

### Step 1: Tree-shape invariant

`NIK`'s `(□I)`/`(◇E)` rules (`Deduction.lean:297,309`) quantify cofinitely over the fresh label
`y` (`∀ y ∉ L, ...`) — the rule itself permits instantiating at an *old* (already-present) label,
but nothing forces the soundness proof to do so. Structure the main induction so it **always**
instantiates this cofinite premise at a label fresh to the *entire derivation constructed so far*
(not just the current `L`) — this is a genuine choice available because `Label Atom` is infinite
and any single node's premise only excludes a *finite* set `L`. This keeps the raw graph `G`
(built by repeated `Graph.addEdge` from `Graph.trivial Atom`) a **tree** throughout the induction,
matching Simpson's own restriction of Theorem 8.1.4 (and the Lifting Lemma) to tree `G`. This
likely needs its own small invariant/lemma threaded through the main induction (e.g. an auxiliary
predicate "G is tree-shaped below root" or reuse of `NIK.relabelFresh`/`NIK.oldLabelTransport`-style
fresh-witness infrastructure already landed in `PrimeLemma.lean` for a *different* purpose — that
machinery is a natural first place to look for reusable freshness lemmas).

### Step 2: The graph-lifting lemma (tree analogue of Simpson's 8.1.3)

Given a tree `G`, an interpretation `ρ` satisfying:
- edge-cond: `∀ a b, G.R a b → r (ρ a) (ρ b)`
- Γ-cond: `∀ ψ ∈ Γ, CKForces r val botForces (ρ ψ.lbl) ψ.prop`

and a raise `w' ≥ ρ x` for one label `x` of `G`, produce `ρ'` such that:
- `ρ' x = w'`
- every descendant `z` of `x` in `G` has `ρ' z ≥ ρ z` (via `cs5FCIncest_lift` applied along each
  edge on the path from `x`, propagated recursively — this is exactly Simpson's own "iterated...
  to find in turn" construction in his Lifting Lemma proof)
- labels not descended from `x` are unchanged (`ρ' = ρ`)
- edge-cond and Γ-cond both re-hold for `ρ'` (Γ-cond via `ckforces_persistence`,
  `Forcing.lean:122`, at every raised descendant whose formula is in Γ)

This is a structural or well-founded recursion over "distance from `x` in `G`" — since only
finitely many labels are ever mentioned in any one finite `NIK` derivation, this recursion
terminates even though `Graph Atom`'s domain type is general/possibly infinite.

### Step 3: Main soundness induction (12 `NIK` constructors)

Generalize over an arbitrary interpretation `ρ` (edge-cond + Γ-cond), concluding
`CKForces r val botForces (ρ x) A`. Most propositional cases (`ax`/`weaken`/`⊃I`/`⊃E`/`∧`/`∨`/
`efq`/`orE`) are routine, following `CKForces`'s clauses directly (see
`Forcing.lean:67-116`,`ckforces_persistence`). The `(□I)`/`(◇E)` cases use Steps 1+2 to instantiate
the cofinite premise at a fresh label mapped to the semantically required world (mirroring the
worked example in the module docstring — fix `w' ≥ ρ x`, `u` with `r w' u`; pick fresh `y`; set
`ρ'' := ` (Step 2's lift of `ρ` at `x ↦ w'`) `updated further at y ↦ u`; apply the IH to `h y`
under `ρ''`). `(□E)`/`(◇I)` need `TClosure 𝒯 G.R x y → r (ρ x) (ρ y)`, which is NOT yet available
for closed (non-raw) edges — that is Phase 11.2's job (Step 4).

### Step 4: Phase 11.2 — TClosure validation + assembly

Show each `cs5FCIncest` conjunct soundly interprets the matching `TClosure` (T/B/4) edge-closure
rule: `G.R a b → r (ρ a) (ρ b)` (raw, from edge-cond) extends to
`TClosure 𝒯 G.R a b → r (ρ a) (ρ b)` (closed). Likely a straightforward induction on `TClosure`'s
own definition (`Deduction.lean`, check its exact shape — not yet inspected this dispatch), using
`cs5FCIncest`'s reflexivity/transitivity/`r_rebase`/`r_symBox`/`cs5Incest` conjuncts per T/B/4
respectively (mirroring how `cs5_axiom_sound_incest`, `CS5Canonical.lean:278`, already validates
each `CS5ModalAxiom` schema against the matching conjunct). Then assemble
`nik_TS5_soundness : NIKTheorem TS5 φ → CKValidFC cs5FCIncest φ` from Steps 1-4.

### Step 5: Phase 11.3 — anti-vacuity, independently attemptable

`nik_TS5_consistent : ¬ NIKTheorem TS5 (⊥ : Proposition Atom)` via a **one-point reflexive**
`cs5FCIncest` witness model: `World := PUnit`, `r := fun _ _ => True`, `≤` the trivial (single-
point) preorder, `val := fun _ _ => True` (or anything — irrelevant to refuting `⊥`),
`botForces := fun _ => False`. All five `cs5FCIncest` conjuncts and the five `CKValidFC`
side-conditions hold trivially (every quantifier collapses to the single point). **Because there
is only one possible interpretation value, the entire tree-lifting machinery of Steps 1-3 is
unnecessary for this model specifically** — every `ρ` is forced to the constant function, so
"lifting" is trivially the identity. If a future dispatch wants `nik_TS5_consistent` *before* the
general `nik_TS5_soundness` lands, it is a small, self-contained, independently-provable corollary
(the fallback the plan itself documents in Rollback/Contingency for an escalated 11.2 blocker —
here offered as an *optional accelerant* even though 11.2 is not formally blocked, since 11.3's
own proof doesn't route through the general theorem).

## Files touched / landed this dispatch

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Completeness.lean` (new, Phase 10, complete)
- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (new, Phase 11.1 partial —
  `cs5FCIncest_lift` only, plus the full architecture docstring this handoff summarizes)
- `Cslib.lean` (barrel imports for both new files)
- `specs/517_labelled_bounded_context_cs5_completeness/plans/13_labelled-completeness-full-soundness.md`
  (Phase 10 marked `[COMPLETED]`, Phase 11/11.1 marked `[IN PROGRESS]` with detailed annotations)

## Verification (this dispatch)

- `cs5_completeness`: `lean_verify` → `["propext","Classical.choice","Quot.sound"]`, no `sorryAx`.
- `cs5FCIncest_lift`: `lean_verify` → `[]` (axiom-free), no `sorryAx`.
- Full `lake build`: 3247/3247 green.
- `lake exe checkInitImports`: pass.
- `lake lint` / `lake exe lint-style` / `lake shake`: zero warnings/suggestions for both new files.
- `lake test`: green (pre-existing sorries in unrelated Propositional Tableau files unregressed,
  as in every prior phase boundary of this task).
- Sorry inventory (new/modified files): **empty**.
- New axiom count: **zero**.
