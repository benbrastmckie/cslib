# Phase 9 Verdict: Post-Reuse Closure Lemma — COLLAPSED

- **Task**: prove_atom_persistence_upward_closure_for_intexpan
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md`, Phase 9
- **Status**: **COLLAPSED** — proceed to Phase 10 (full origin tracing). This is a planned
  branch per the plan's own Rollback/Contingency table, not a failure.
- **Cslib/ writes this phase**: none. `git status --short Cslib/ CslibTests/` is empty.

## Method

No scratch harness was built this phase (unlike Phases 5/6, which had a concrete computational
question to probe). Phase 9's question is a proof-engineering one: given the exported facts
`IBranchSaturation Atom b`, `IPosPersistRaw rawEdges b` (Phase 7), `IReuseContain lbEdges b`
(Phase 8), and a recorded loop-back edge `(x, l) ∈ lbEdges`, does the cheap route (saturation +
copy-completeness, no fresh provenance tracking) suffice to prove the FULL persistence fact
`∀ χ, T(χ)@l ∈ b → T(χ)@x ∈ b`? This was worked out by direct proof-sketching against the real
declarations (signatures confirmed via `lean_hover_info`/direct source reading, not assumed),
cross-checked against Gate B's own independent prior finding (`handoffs/02_gate-b-verdict.md`).

## The case split requires a fact that does not yet exist

Both enumerated arrival sources (decomposition of a reuse-time premise; copy from a raw
ancestor `y` of `l`) need `y`/the decomposition-premise's world and `x` to be **compared**
first — is the relevant witness world `≤ x` (closes) or does `x` sit strictly between it and
`l` (open)? That comparison itself requires `ForestComparable`-style linearity: any two raw
ancestors of a common world are `isAccessible`-comparable.

**This fact is not yet built or exported.** Grep confirms `ForestComparable` exists only as an
**assumed hypothesis** in the Phase 2 scratch prototype
(`specs/430_.../scratch/PersistPrototype.lean:25`), never as a derived corollary in `Scheme.lean`
itself. `IWorldHist`'s `par`/(H0)/(H1)/(H1-acc) clauses (`Scheme.lean:3213`ff) supply the raw
material — `par : Nat → Nat` is total and unique-parent, so `parAncestor`-chains are
automatically linear, and (H1-acc) links `parAncestor` to `isAccessible` — but:

1. `IWorldHist` is **not exported** in `intExpandBranches_openBranch_sat`'s conclusion (checked
   directly: the conclusion is exactly `IBranchSaturation Atom b ∧ IFimpAccess edges b ∧
   IPosPersistRaw rawEdges b ∧ IReuseContain lbEdges b`, four components, no `IWorldHist` term).
   Deriving `ForestComparable` at `openBranch_countermodel`'s call site (where Phase 9's lemma
   would need to be applied) requires **another conclusion-signature change** to
   `intExpandBranches_openBranch_sat`, threading a fifth existential — the same kind of change
   Phases 7/8 each made, each its own dispatch.
2. Converting a raw `isAccessible edges x l = true` hypothesis (what the reuse witness
   `intFImpReuseWitnessAnc?_spec` actually supplies, per `Expansion.lean:321`) into a
   `parAncestor par x l` membership (what (H1-acc) is stated in terms of) is itself an
   unestablished direction — (H1-acc) only gives `parAncestor → isAccessible`, not the converse.
   The converse needs the tree to have **no accessibility edges beyond the recorded parent
   chain**, a global uniqueness property not yet stated as its own lemma.

This is exactly the gap Gate B's own prototype (Phase 2, `handoffs/02_gate-b-verdict.md`)
already found independently: *"formula-level provenance ... is the load-bearing fact ... This is
a genuine, sizeable engineering task — comparable in scope to the existing
`IWorldHist`/`IAllAccessConsistent` threading — not a one-line corollary."* Phase 9's own task
list item ("Export `par`-linearity and (H1-acc) from `IWorldHist` as the `ForestComparable`
fact ... export, not construction") undersold this: the export requires a signature change to
the same load-bearing lemma Phases 7/8 touched, not a standalone corollary.

## Sub-case analysis (once comparability is assumed)

Granting `ForestComparable` for a moment, to record exactly how far the cheap route reaches:

- **`y ≤ x` (the "descendant" sub-case, Gate B's terminology)**: closes cleanly and requires NO
  new machinery. If `χ`'s premise/copy-source world `y` satisfies `isAccessible rawEdges y x`,
  Phase 7's `IPosPersistRaw rawEdges b` delivers `T(χ)@x ∈ b` directly (`y` raw-accessible to
  `x`, `x` trivially has an entry). For the cross-world T-imp decomposition source specifically
  (premise `T(φ→ψ)@y` with `y ≤ x`, plus `T(φ)@l ∈ bSnap` hence `T(φ)@x ∈ bSnap ⊆ b` via
  `IReuseContain`): `IPosPersistRaw` forwards `T(φ→ψ)@y` to `x`, then `IBranchSaturation.sat_timp`
  (reflexive, `Scheme.lean:120`) fires at `x` itself, and `S.no_contradiction` rules out the
  `F(φ)@x` disjunct since `T(φ)@x` already holds — leaving `T(ψ)@x`. Both mechanisms are
  already-landed, already-exported facts; nothing new needs to be written for this half.
- **`x ≤ y ≤ l` (the "ancestor" sub-case, Gate B's terminology)**: **remains open.** Content only
  ever flows forward (ancestor → descendant) via the copy channel; knowing `χ` at the
  intermediate world `y` (a descendant of `x`) says nothing about `χ` at `x` itself. Closing this
  needs `χ`'s **own point of origin** (not `y`, but wherever `χ` was genuinely introduced —
  by mint, by the initial formula, or by cross-world T-imp decomposition from something even
  higher) traced back far enough to land at or above `x`. This is exactly Phase 10's origin-
  tracing extension, not a corollary of anything currently exported.

## Verdict rationale

The plan's own Risk table names this precisely: *"The weaker sufficient statement collapses
back into full origin tracing at the residual `x ≤ y ≤ w` case ... High/Medium."* That risk is
realized. No counterexample to the underlying THEOREM was found (Gate B2 already established
this empirically, Phase 5); the collapse is a **proof-route** limitation, identical in kind to
DP-3/DP-4's original defect (Phase 6) — not a refutation of the statement. Per the plan's own
Rollback/Contingency: *"Phase 9 returns COLLAPSED: proceed to Phase 10. This is a planned
branch, not a failure."*

## Why no Cslib/ code lands this phase

Any lemma landed now would have to be one of:
- The full residual lemma with the `x ≤ y ≤ l` case `sorry`'d — **prohibited** (no `sorry`, no
  weakened statement, per the plan's explicit prohibition, carried from Phase 5's discipline).
- A `ForestComparable` export requiring a new `intExpandBranches_openBranch_sat` conclusion
  component — this is real work, but it is **Phase 10's own first natural step** (Phase 10's
  task list already calls for extending `IWorldHist`'s witness functions / threading a sibling
  invariant through the same induction). Landing it now, ahead of the origin-tracing extension
  it exists to serve, risks a signature change that gets revised again immediately in Phase 10 —
  duplicated churn, not saved work.
- A restatement of `IPosPersistRaw` under an assumed `isAccessible rawEdges y x` hypothesis for
  the closing half — adds no new content beyond Phase 7's already-landed lemma; not a genuine
  increment.

## What Phase 10 inherits from this analysis (do not re-derive)

- The two-source enumeration (decomposition of a reuse-time premise; copy from a raw ancestor)
  is confirmed still exhaustive for **already-covered content** — the `y ≤ x` closing argument
  above is complete and reusable verbatim once `ForestComparable` exists.
- The blocker is precisely and only the `x ≤ y ≤ l` sub-case, and precisely because content
  origin (not merely current presence) is the load-bearing fact — confirmed independently by
  Gate B's Phase 2 prototype and this phase's fresh analysis.
- `ForestComparable`/`par`-linearity is NOT yet exported anywhere in `Scheme.lean`; it must be
  built as part of Phase 10, most likely as a further conclusion component on
  `intExpandBranches_openBranch_sat` (a fifth existential, alongside `edges`, `rawEdges`,
  `lbEdges`) or threaded via a sibling invariant mirroring `IAllAccessConsistent`'s
  companion-not-merged pattern — consistent with Phase 10's own task list.
- The direction gap in (H1-acc) — it gives `parAncestor → isAccessible`, not the converse — is a
  concrete detail Phase 10 needs to resolve or route around (e.g. by stating the origin-tracing
  invariant directly in terms of `isAccessible`, never converting through `parAncestor`, if
  that avoids needing the converse at all).

## Verification

No Lean file changed. Confirmed no regression: `lake build` (full project, 3311 jobs) green,
identical warning set to Phase 8 (`FrameSoundness.lean:1252`, `Scheme.lean:671`,
`Scheme.lean:7617` reported at `Completeness.lean:137`/`Minimal/Completeness.lean:133` — i.e.
the same 4 in-scope sorries: DP-5, the Phase-6 `openBranch_countermodel` conjunct, DP-3, DP-4).
`lake exe checkInitImports` clean. `lake exe lint-style` clean. `lean_verify` on
`truthLemma`, `tableau_complete`, `openBranch_countermodel`, `intuitionisticTableau_complete`,
`minimalTableau_complete`: all report only the expected `["propext", "sorryAx",
"Classical.choice", "Quot.sound"]` (transitive `sorryAx`, unchanged from Phase 8).
