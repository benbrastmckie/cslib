# Implementation Plan: DP-2 World-History Invariant and Mint Residue

- **Task**: 585 - prove_post_blocking_world_bound_chain_and_mint_invariant
- **Status**: [IMPLEMENTING]
- **Effort**: 17 hours
- **Dependencies**: None (task 430 must not run concurrently -- see Serialization below)
- **Research Inputs**: specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/reports/01_dp2-mint-invariant-transfer.md
- **Artifacts**: plans/01_dp2-worldhist-mint-invariant.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false (this field denotes plan minimality, not Lean 4)

## Overview

Discharge DP-2, the last strategic sorry in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
(currently line 2605). The lemma `intFreshMint_preserves_nw` as written is false, so the work is
not to prove it but to replace it with a correctly-premised statement whose premise is genuinely
discharged at the single call site (`Scheme.lean:5362-5363`). Per the research report, the premise
must be a **structural creation-history invariant** (`IWorldHist`), not a numeric strengthening of
`IAllNW`: no numeric strengthening is preserved by the mint arm. The numeric bound
`nw <= WBound phi0` is re-derived as a corollary at the consumption site from the structural
invariant via depth (pigeonhole on `(sfor, obl)` pairs) times branching (out-degree bounded by
subformula count).

Definition of done: the sorry at `Scheme.lean:2605` is gone, `lake build` is green with zero
`declaration uses 'sorry'` warnings attributable to this development, the Tableau-subtree bare-sorry
count drops 4 -> 3 (repo-wide 6 -> 5), and every hypothesis added to any existing declaration is
discharged at its call site.

### Research Integration

The plan follows the research report and **overrides the original task description in two
load-bearing ways**:

1. **The description's step (b) is rejected.** Restating `intFreshMint_preserves_nw` with the
   numeric premise `nw < WBound phi0` and threading it is not inductive: after a mint the counter
   is `nw + 1`, and `nw < WBound phi0` yields only `nw + 1 <= WBound phi0`, not the strict form the
   *next* mint on the same branch needs. The threaded object is structural (`IWorldHist`, report
   section 3.2); the numeric bound is a derived corollary re-established at each consumption site
   (report section 3.3).
2. **The `intCreatedChain_le`-style final-branch transfer is rejected as non-derivable.** Report
   section 4.1 refutes it: conjunct 3 of the reuse check moves the wrong way under branch growth
   (positive content at `x` only grows, so the implication runs backwards), and no monotonicity
   or additional final-branch invariant recovers it. The working route (report section 4.2)
   consumes the runtime `none` **at mint time**, while `bPers` is still current, and keeps only the
   snapshot-free residue **(*) `not (sfor c subset sfor c')`**, which feeds the same pigeonhole.
   `intCreatedChain_le` is therefore left untouched and sorry-free; the new depth bound is a
   sibling lemma, not an edit.

The report's four absent supporting lemmas (sections 5.1-5.4) are Phases 1-4. The report's
9-phase decomposition is adopted with one refinement: **the (*) derivation is hoisted out of the
mint-arm phase into its own standalone gate phase (Phase 5)**, stated with all five of its inputs
as explicit hypotheses. This makes the single go/no-go risk testable *before* the ~500-line
`IWorldHist` threading development is built on top of it, rather than after.

### Prior Plan Reference

No prior plan for this task. The docstring at `Scheme.lean:2587-2596` records the prior
(now-superseded) framing that DP-2 required the runtime-check-to-final-branch transfer; Phase 11
updates that docstring to record the refutation and the (*) route actually taken.

### Roadmap Alignment

No ROADMAP.md consulted for this task (`roadmap_path` not supplied in delegation context).

## Goals & Non-Goals

**Goals**:
- Replace `intFreshMint_preserves_nw`'s false statement with a correctly-premised lemma
  (`intWorldHist_nw_le`, or the name-preserving strengthened form of report section 3.3) that is
  proved sorry-free.
- Establish `IWorldHist` inductively across all four `intExpandBranches.go` arms plus entry, and
  discharge the new premise at the sole call site (`Scheme.lean:5362-5363`).
- Add the four absent supporting lemmas the report identifies (report sections 5.1-5.4).
- Derive `nw <= WBound phi0` entirely from blocking combinatorics: (*)-driven depth bound times
  (H4)-driven branching bound, matching `WBound`'s exact
  `(card + 1) ^ (intChainBound + 1)` shape via a path injection.
- Net: Tableau-subtree bare-sorry count 4 -> 3; repo-wide 6 -> 5; `lake build` green.

**Non-Goals**:
- DP-1 (`intCreatedChain_le`, `Scheme.lean:1757`) is RESOLVED and stays untouched. It is available
  leverage, not an obligation. Its proof body is a template for Phase 9's pigeonhole, copied
  rather than edited.
- DP-5 (`truthLemma` T-imp, `Scheme.lean:633`), DP-3 (`Intuitionistic/Completeness.lean:140`), and
  DP-4 (`Minimal/Completeness.lean:128`) are owned by another task and MUST NOT be touched.
- `intFImpReuseWitnessAnc?` (`Expansion.lean`) is NOT edited. Only a new sibling spec lemma is
  added alongside it.
- No attempt at the section 4.1 final-branch transfer, and no attempt at the two refuted cheap
  routes (report section 6: fuel-bounded counter; flat pigeonhole without the tree). These are
  recorded dead ends; do not re-derive them.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| (*) derivation (report 4.2) fails in Lean despite being airtight on paper | H | M | Phase 5 is a standalone gate stated with all inputs as hypotheses, run *before* the invariant bulk. On failure mark [BLOCKED] with the exact goal state; do not proceed to Phases 6-11 |
| `isAccessible`'s fuel budget (`fuel = edges.length`) proves insufficient for the one-hop extension | H | L | `par c < c` makes every ancestry path strictly increasing, so path length <= `edges.length`. If the fuel argument still fails, Phase 1 is [BLOCKED] and Phase 5's `hacc` input has no producer |
| `IWorldHist` needs a 4-list zip (`bs`, `es`, `nws`, `edgeSets`); existing companions (`IAllConsistent`, `IAllAccessConsistent`) are only 3-list zips | M | H | Phase 6 builds the 4-list companion and its `_append`/`_map_const` plumbing explicitly, mirroring `IAllNW_append` (`Scheme.lean:2421`) and `IAllNW_map_const` (`Scheme.lean:2433`), before any arm work begins |
| Adding a hypothesis to `intExpandBranches_openBranch_sat` becomes an undischarged premise (a weakening in disguise) | H | L | Phase 3 discharges `no_contradiction` at the single call site (`openBranch_countermodel`, ~`Scheme.lean:5597-5609`) with `S.no_contradiction` within the same phase; Phase 3's exit criteria require the call site green, not just the signature |
| Path-injection size bound (report 4.5) has no end-to-end Mathlib lemma | M | M | Only `Fintype.card_pi_const` and `Finset.card_le_card_of_injOn` are needed as building blocks; both verified present. Phase 10 constructs `parIter`/depth/path explicitly |
| Concurrent edits to `Scheme.lean` from task 430 | M | L | Serialize; see Serialization below. Do not run task 430 while this task is in [IMPLEMENTING] |
| Phases 3 and 4 both edit `intExpandBranches_openBranch_sat`'s signature and `key` induction | M | H | They are placed in different waves and must never run in parallel despite both being additive |

## Serialization

`specs/430_prove_atom_persistence_upward_closure_for_intexpan/` also edits `Scheme.lean` (DP-3/DP-4/DP-5).
Line ranges are disjoint, but both touch the same file. **Do not run the two tasks concurrently.**
If a positive-formula persistence / upward-closure lemma lands from that task, check whether it
subsumes `IWorldHist` clause (H3) before re-proving it in Phase 6.

## Verification Commands (referenced by every phase)

```bash
# FULL tier
lake build

# LOCAL tier (single module)
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme
lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion

# Sorry census -- Tableau subtree. Reads 4 for Phases 1-10; MUST read 3 after Phase 11.
grep -rn --include=*.lean -E "^[[:space:]]*sorry[[:space:]]*$" Cslib/Logics/Propositional/Tableau/ | wc -l

# Sorry census -- repo-wide. Reads 6 for Phases 1-10; MUST read 5 after Phase 11.
grep -rn --include=*.lean -E "^[[:space:]]*sorry[[:space:]]*$" Cslib/ | wc -l

# Axiom-level census (name-independent; catches sorryAx propagation into private decls)
lake build 2>&1 | grep -c "declaration uses 'sorry'"

# Targeted axiom check for a private declaration: place a TEMPORARY `#print axioms <name>`
# line in the SAME file immediately after the declaration (private names resolve within their
# own file), read the output, then REMOVE the line before committing.
```

**Standing exit criterion, every phase**: the Tableau-subtree census reads exactly 4 (exactly 3
after Phase 11), the repo-wide census reads exactly 6 (exactly 5 after Phase 11), and no new
`sorry`, `admit`, `native_decide`, `def X := True`, `theorem X := trivial`, or other vacuous
placeholder was introduced. Relocating the obligation into a new sorry-bearing helper does not
count as progress and is prohibited.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 5 | 1, 2, 3 |
| 3 | 6 | 5 |
| 4 | 7, 8, 9 | 3, 4, 5, 6 |
| 5 | 10 | 6, 9 |
| 6 | 11 | 7, 8, 9, 10 |

Phases within the same wave can execute in parallel, **with one exception**: Phases 3 and 4 both
edit `intExpandBranches_openBranch_sat`'s signature and its `key` induction and are deliberately
placed in different waves; they must never be dispatched in parallel.

---

### Phase 1: isAccessible one-hop extension [COMPLETED]

**Deviation note**: the literally-stated lemma shape `(c,p) ∈ edges -> isAccessible edges x p = true
-> isAccessible edges x c = true` (for a FIXED, already-accumulated `edges`) is not fuel-sound in
general: `isAccessible edges x y` always uses fuel EXACTLY `edges.length` for every pair, and
composing a fresh hop costs one unit of fuel that a fixed-`edges` snapshot cannot supply
(confirmed by hand-deriving the `go`-level fuel arithmetic). The mitigation anticipated by this
risk in the plan ("this phase may assume `par c < c`...") is resolved differently: the lemma is
specialized to the exact shape actually consumed at every mint site, where `edges` gains a BRAND
NEW edge `(c, p)` via append (`edges ++ [(c, p)]`, matching `Scheme.lean:3272`'s mint-arm append
exactly). In that shape the fuel arithmetic is exact (no deficit), since
`(edges ++ [(c, p)]).length = edges.length + 1` matches the one extra hop precisely. Proved as
`isAccessible_one_hop_ext` (plus its `go`-level building blocks `isAccessible_go_direct` and
`isAccessible_go_one_hop_ext`), all sorry-free, `lake build` green. Downstream consequence for
Phase 6/7 (recorded here for continuity): ancestor-accessibility (needed for (H5)'s `hacc` input)
must be threaded as an INCREMENTAL invariant updated once per mint via
`isAccessible_append_mono` + `isAccessible_one_hop_ext` in lockstep with `edges`'s real growth,
not re-derived post-hoc from a fixed snapshot by induction on the ancestor chain (that direction
reintroduces the same fuel deficit). Phase 6's `IWorldHist` definition should account for this.

- **Goal:** Prove the absent one-hop ancestry extension lemma so that `par`-ancestry can be
  converted to `isAccessible` at the mint site (report section 5.1).
- **Tasks:**
  - [ ] Read `isAccessible` (`Rules.lean:92-107`) and confirm the fuel-bounded DFS shape with
        `fuel = edges.length`.
  - [ ] Read the three existing helpers: `isAccessible_one_step` (`Scheme.lean:293-305`),
        `isAccessible_go_append_mono` (`~310`), `isAccessible_go_fuel_mono` (`~339`). Note that
        `Scheme.lean:250` explicitly declines transitivity -- this phase supplies it in the
        weaker one-hop form only.
  - [ ] State and prove
        `(c, p) in edges -> isAccessible edges x p = true -> isAccessible edges x c = true`
        as a private lemma placed next to its siblings.
  - [ ] Justify the fuel budget: paths are strictly increasing in the label order (this phase may
        assume `par c < c` as a hypothesis on the ancestry chain rather than importing Phase 4),
        so path length is bounded by `edges.length` and the DFS fuel suffices.
  - [ ] Do NOT prove full transitivity. One-hop extension is the whole obligation.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** The report estimates ~100-180 new Lean lines confined to `Scheme.lean`,
  additive only (no existing declaration modified). Confirm at implementation time by
  `git diff --stat` on the phase commit: a diff touching any file other than
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`, or showing deletions in
  existing declarations, falsifies the hypothesis and must be reported.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - additive private lemma near
    the existing `isAccessible_*` helpers
- **Verification:**
  - `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` green
  - Temporary `#print axioms` on the new lemma shows no `sorryAx`; remove the line before commit
  - Standing sorry-census criterion holds
- **Exit criteria:** The one-hop lemma exists, is sorry-free, and builds. If the fuel argument
  cannot be closed, mark [BLOCKED] with the exact goal state -- Phase 5's `hacc` input then has
  no producer and the route stalls.

---

### Phase 2: intFImpReuseWitnessAnc?_none_spec [NOT STARTED]

- **Goal:** Supply the absent `none` direction of the reuse-check spec, so the runtime `none` can
  be instantiated at a specific candidate label (report section 5.2).
- **Tasks:**
  - [ ] Read the existing `some` direction `intFImpReuseWitnessAnc?_spec`
        (`Expansion.lean:295-322`) and the function body (`Expansion.lean:231-283`), noting the
        five reuse conjuncts at `Expansion.lean:279-283`.
  - [ ] State: if `intFImpReuseWitnessAnc? bPers edges newForms newE = none`, and
        `x in (bPers.map (.label)).eraseDups`, and the obligation lookup succeeds, then the
        conjunction of the five conjuncts fails at `x`.
  - [ ] Prove it mechanically from `List.findSome?_eq_none` plus the same `if`-unfold the existing
        `some` spec uses.
  - [ ] Place the lemma in `Expansion.lean` immediately next to its sibling.
  - [ ] **Constraint check:** `intFImpReuseWitnessAnc?` itself MUST NOT be edited. Confirm by
        inspecting the diff -- only additive lines below the existing spec lemma.
- **Timing:** 1 hour
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** The report estimates ~40-70 new Lean lines confined to `Expansion.lean`,
  purely additive. Confirm at implementation time by `git diff` showing zero changed lines inside
  the `intFImpReuseWitnessAnc?` definition itself; any such change violates a binding constraint
  and must be reverted, not explained.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - additive spec lemma
- **Verification:**
  - `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion` green, then
    `lake build` green (Expansion is upstream of Scheme)
  - Temporary `#print axioms` on the new lemma shows no `sorryAx`; remove before commit
  - `git diff Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` shows no edit
    inside `intFImpReuseWitnessAnc?`
  - Standing sorry-census criterion holds
- **Exit criteria:** The `_none_spec` lemma exists, is sorry-free, builds, and
  `intFImpReuseWitnessAnc?` is byte-identical to its pre-phase state.

---

### Phase 3: closurePred no-contradiction hypothesis threading [NOT STARTED]

- **Goal:** Give `intExpandBranches_openBranch_sat` access to the fact that an unclosed branch has
  no `F(psi)@w` together with `psi` positive at `w`, and discharge the new hypothesis at its sole
  call site (report section 5.3).
- **Tasks:**
  - [ ] Confirm `intExpandBranches_openBranch_sat` (`~Scheme.lean:4856-4874`) currently takes
        `closurePred : IBranch Atom -> Bool` as a bare parameter with no properties.
  - [ ] Read the scheme field `IntMinScheme.no_contradiction` (`Scheme.lean:163-166`) and confirm
        both scheme instances prove it (`Scheme.lean:211`, `Scheme.lean:240`).
  - [ ] Add a hypothesis to `intExpandBranches_openBranch_sat` of the shape
        `closurePred b = false -> (neg, psi, w) in b -> psi not in posFormulasAt b w`.
  - [ ] Thread the hypothesis into the `key` `suffices` block so it is available inside the
        induction (it is a property of `closurePred`, constant across the recursion -- do NOT add
        it to the per-branch `IAll*` companions).
  - [ ] Discharge it at the single call site `openBranch_countermodel` (~`Scheme.lean:5597-5609`)
        with `S.no_contradiction`.
  - [ ] **Anti-weakening check:** the added hypothesis must be discharged in this same phase. A
        premise added and left undischarged is a weakening in disguise and fails the acceptance
        gate.
- **Timing:** 1 hour
- **Depends on:** none
- **Verification Tier:** interface
- **Scope Hypothesis:** The report estimates ~60-100 changed Lean lines, all in `Scheme.lean`:
  one signature, the `key` block's hypothesis list, and one call site. Confirm at implementation
  time by grepping for every occurrence of `intExpandBranches_openBranch_sat` in the repo and
  checking each is either the definition or a supplied-argument call site -- if more than one
  call site exists, the estimate is falsified and every additional site must also be discharged.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - lemma signature, `key`
    block, and the `openBranch_countermodel` call site
- **Verification:**
  - `lake build` green (full tier: signature change with call sites)
  - `grep -rn "intExpandBranches_openBranch_sat" Cslib/` enumerates exactly the definition plus
    the discharged call sites -- no undischarged site remains
  - Standing sorry-census criterion holds
- **Exit criteria:** Signature carries the hypothesis, the call site supplies
  `S.no_contradiction`, and `lake build` is green.

---

### Phase 4: Strict label bound as a parallel invariant [NOT STARTED]

- **Goal:** Add the strict label-bound companion needed for `par c < c` (report section 5.4).
  The existing `ILabelBound b nw := forall sf in b, sf.label <= nw` (`Scheme.lean:953-954`) is too
  weak and is already bundled inside `IAllConsistent` -- do not modify it.
- **Tasks:**
  - [ ] Define a strict form `ILabelBoundStrict b nw := forall sf in b, sf.label < nw`.
  - [ ] Define its list companion in the "companion, not merged" shape used by
        `IAllAccessConsistent` (`Scheme.lean`, 3-list zip over `bs`, `es`, `nws`) -- do NOT merge
        it into `IAllConsistent`.
  - [ ] Prove the `_append` and `_map_const` plumbing lemmas mirroring `IAllNW_append`
        (`Scheme.lean:2421`) and `IAllNW_map_const` (`Scheme.lean:2433`).
  - [ ] Thread it through `intExpandBranches_openBranch_sat`'s `key` induction as a genuine
        parallel invariant on both the `pending` and `done` sides. It MUST be threaded, not
        derived from `ILabelBound`.
  - [ ] Discharge entry: `openBranch_countermodel` starts at `branches = [[(neg, phi, 0)]]`,
        `nextWorlds = [1]` (`Scheme.lean:5578`), so `0 < 1` holds.
  - [ ] Discharge the four arms: mint introduces label `nw < nw + 1`; alpha, beta, and reuse arms
        leave labels and `nw` unchanged.
- **Timing:** 1.5 hours
- **Depends on:** 3
- **Verification Tier:** interface
- **Scope Hypothesis:** The report estimates ~60 new Lean lines, but that figure covers the
  definition and arm cases only; the `key`-block threading and both `_append`/`_map_const`
  plumbing lemmas may push it to ~120-180. Confirm at implementation time by counting added lines
  in the phase diff and reporting the actual figure; a figure above ~250 signals the invariant is
  being merged into `IAllConsistent` rather than kept as a companion, which is the wrong shape.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - new definitions, plumbing
    lemmas, `key` induction threading, entry discharge
- **Verification:**
  - `lake build` green
  - `grep -n "ILabelBound\b" Cslib/.../Scheme.lean` confirms the original `ILabelBound` and
    `IAllConsistent` are unchanged
  - Standing sorry-census criterion holds
- **Exit criteria:** The strict companion is threaded across entry and all four arms, sorry-free,
  and `IAllConsistent` is untouched.

---

### Phase 5: GO/NO-GO GATE -- standalone mint-residue lemma (*) [NOT STARTED]

- **Goal:** Manufacture the snapshot-free residue **(*) `not (sfor subset sfor_c')`** from the
  runtime `none`, as a **standalone lemma with all five inputs supplied as explicit hypotheses**.
  This is the single point where the entire route can still fail (report section 8). Hoisting it
  out of the mint arm makes the risk testable before ~500 lines of invariant threading are built
  on top of it.
- **Tasks:**
  - [ ] State the standalone lemma. Shape (adapt names to the actual source):
        given `hnone : intFImpReuseWitnessAnc? bPers edges newForms newE = none`, a candidate
        `c'` with `hmem : (neg, psi, c') in bPers`, `hacc : isAccessible edges c' p = true`,
        `hle : c' <= p`, `hopen : closurePred bPers = false` plus the no-contradiction property,
        and `hsub : sfor_c' subset posFormulasAt bPers c'`,
        conclude `not (sfor subset sfor_c')` where `sfor = phi :: posFormulasAt bPers p`.
  - [ ] Establish candidate membership: `c'` is in `(bPers.map (.label)).eraseDups` because
        `(neg, psi, c') in bPers`. Use Phase 2's `_none_spec` to instantiate at `x := c'`.
  - [ ] Discharge conjunct 1 (`isAccessible edges c' p = true`) from the `hacc` hypothesis
        (produced downstream by Phase 1's one-hop extension over the `par` chain).
  - [ ] Discharge conjunct 2 (`c'.ble p`) from `hle`.
  - [ ] Discharge conjunct 4 (`psi not in posFormulasAt bPers c'`) from `hmem` plus the
        no-contradiction property applied to the unclosed `bPers`.
  - [ ] Discharge conjunct 5 (`(neg, psi, c') in bPers`) from `hmem` directly.
  - [ ] Conclude conjunct 3 must fail: `not (sfor subset posFormulasAt bPers c')`. Combine with
        `hsub` to obtain (*): `not (sfor subset sfor_c')`.
  - [ ] Confirm (*) mentions no branch, no edge list, and no snapshot -- it is permanently true.
        If the statement still mentions `bPers` or `edges`, the residue is not snapshot-free and
        the gate has NOT been passed.
  - [ ] **`sfor` grounding:** confirm the `sfor` projection is exactly
        `newForms.filterMap (pos)` (cf. `Scheme.lean:5214-5216`) and matches `intFImpRule`'s
        `phi :: posFormulasAt bPers l` (`Rules.lean:162-164`).
- **Timing:** 2 hours
- **Depends on:** 1, 2
- **Verification Tier:** local
- **Scope Hypothesis:** Asserted scope is one new standalone private lemma of ~80-150 lines in
  `Scheme.lean`, with zero edits to any existing declaration. Confirm at implementation time by
  `git diff --stat`: any deletion inside an existing declaration falsifies the hypothesis and
  means the gate was passed by changing something else, which does not count.
- **Verification:**
  - `lake build` green
  - Temporary `#print axioms` on the new lemma shows no `sorryAx`; remove before commit
  - Read the final statement back and confirm the conclusion's free variables contain neither a
    branch nor an edge list
  - Standing sorry-census criterion holds
- **Exit criteria (GO):** (*) is proved as a sorry-free standalone lemma whose conclusion is
  snapshot-free. Proceed to Phase 6.
- **Exit criteria (NO-GO) -- BLOCKING INSTRUCTION:** If (*) cannot be produced as a sorry-free
  `have`/lemma within this dispatch, mark this phase **[BLOCKED]** and record: (a) exactly which
  of the five conjunct discharges failed, (b) the verbatim Lean goal state reached at the point
  of failure, (c) the tactics and lemma names attempted. Then STOP.
  - Do NOT substitute a placeholder.
  - Do NOT relocate the obligation into a new sorry-bearing helper.
  - Do NOT add an undischarged hypothesis to `intExpandBranches_openBranch_sat`.
  - Do NOT introduce a vacuous definition (`def X := True`, `theorem X := trivial`, or kin) --
    these are semantically equivalent to `sorry` and are not discharges.
  - Do NOT proceed to Phases 6-11. The route depends on this result; building the invariant on an
    unestablished residue produces work that must be discarded.

---

### Phase 6: IWorldHist definition, counter-redundancy, plumbing, entry case [NOT STARTED]

- **Goal:** Define the threaded structural invariant and its list companion, prove the counter is
  redundant with `edges`, and discharge the (vacuous) entry case (report sections 3.1, 3.2, 5.5).
- **Tasks:**
  - [ ] Define `IWorldHist phi0 b e nw edges` per report section 3.2, with witness functions
        `par`, `obl`, `sfor`, `fire` and clauses (H1) tree structure, (H2) universe containment,
        (H3) planted monotone facts, (H4) sibling uniqueness, (H5) the (*) residue from Phase 5.
  - [ ] Define `parAncestor par x y` as reflexive-transitive iteration of `par`, well-founded by
        `par c < c`.
  - [ ] Confirm every clause is either fixed arithmetic/subformula data (H1, H2, H4, H5) or
        monotone in `b` (H3). **No branch snapshot may appear anywhere** -- this is the property
        that makes the invariant threadable at all. If a snapshot creeps in, the definition is
        wrong.
  - [ ] Prove the counter-redundancy invariant `nw = edges.length + 1` (report section 3.1) as a
        separate parallel-list invariant over `(pendingNW, pendingEdges)`, in the same
        "companion, not merged" shape. Entry gives `1 = 0 + 1`.
  - [ ] Define the list companion `IAllWorldHist` over the FOUR parallel lists (`bs`, `es`,
        `nws`, `edgeSets`). Note this is a new shape: the existing companions `IAllConsistent`
        and `IAllAccessConsistent` are 3-list zips only.
  - [ ] Prove `_append` and `_map_const` plumbing for the 4-list companion, mirroring
        `IAllNW_append` (`Scheme.lean:2421`) and `IAllNW_map_const` (`Scheme.lean:2433`).
  - [ ] Discharge the entry case: `nw = 1`, so no `c` satisfies `1 <= c < 1` and the invariant is
        vacuously true at `openBranch_countermodel`'s initial state (`Scheme.lean:5578`).
  - [ ] Thread both companions through the `key` induction's hypothesis list (arms are Phases 7
        and 8; this phase only adds the hypotheses and closes entry).
- **Timing:** 2 hours
- **Depends on:** 5
- **Verification Tier:** local
- **Scope Hypothesis:** The report estimates ~150-250 Lean lines for the definition, plumbing,
  and entry case. The 4-list companion is a new shape not present in the file, so plumbing may
  exceed the estimate. Confirm at implementation time by reporting the actual added-line count;
  if it exceeds ~350, stop and report before continuing to arms -- an oversized definition usually
  means a snapshot leaked into a clause.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - new definitions, plumbing,
    `key` hypothesis threading, entry discharge
- **Verification:**
  - `lake build` green with the arm cases still open only as *unthreaded* obligations (the phase
    must not leave a `sorry`; if arms cannot yet be closed, thread the hypotheses but do not yet
    claim the invariant in the conclusion -- see exit criteria)
  - Read `IWorldHist`'s statement back and confirm no branch-snapshot argument in any clause
  - Standing sorry-census criterion holds
- **Exit criteria:** `IWorldHist`, `parAncestor`, the counter-redundancy invariant, the 4-list
  companion, its plumbing, and the entry discharge all exist and build sorry-free. Because arms
  are not yet proved, this phase must NOT assert the invariant as an established conclusion of
  the induction -- it may only define and prove the pieces listed. Introducing a `sorry` to bridge
  the unproved arms is prohibited; if intermediate scaffolding is unavoidable, prove the pieces as
  standalone lemmas and defer the induction wiring to Phases 7-8.

---

### Phase 7: Mint-arm preservation of IWorldHist [NOT STARTED]

- **Goal:** Prove `IWorldHist` is preserved by the fresh-mint arm of `intExpandBranches.go`
  (`Scheme.lean:3263-3272`), consuming Phase 5's (*) lemma (report section 5.5, the mint case).
- **Tasks:**
  - [ ] Locate the mint arm: `edges` is appended in exactly one place,
        `doneEdges ++ [edges ++ [newE]] ++ restEdges` (`Scheme.lean:3272`), and `nw` increments in
        exactly the same arm (`nw'`, `Scheme.lean:3271`).
  - [ ] Use `intApplyRuleFull_linearResult_nextWorld` (`Scheme.lean:2494-2522`) for
        `nw' = nw + 1` on this arm.
  - [ ] Extend the four witness functions (`par`, `obl`, `sfor`, `fire`) by one point at `c = nw`:
        `par nw = l` (the label of the fired `F(phi -> psi)`), `obl nw = psi`,
        `sfor nw = phi :: posFormulasAt bPers l`, `fire nw = phi -> psi`.
  - [ ] Discharge (H1): `newE = (nw, l)` from `intFImpRule` (`Rules.lean:159-164`), and
        `par nw = l < nw` from Phase 4's strict label bound.
  - [ ] Discharge (H2): `obl`, `fire`, and every member of `sfor` lie in `intSubfmls phi0`.
  - [ ] Discharge (H3): the planted facts `(neg, obl nw, nw) in b` and
        `forall chi in sfor nw, chi in posFormulasAt b nw` hold at the post-mint branch and are
        monotone under every later append (`Branch.extendMany b sfs = sfs ++ b`,
        `Foundations/Logic/Tableau/Branch.lean:62`; `applyPersistenceFixpoint_mem_preserved`, used
        at `Scheme.lean:5341`).
  - [ ] Discharge (H4) sibling uniqueness: from `intStepBranch_some_exists_fuel`
        (`Scheme.lean:3163-3182`), `e.any (. == sf) = false` together with `newExp = e ++ [sf]`
        means the expanded set is duplicate-free along a lineage and never shrinks, so
        `(neg, chi, p)` fires at most once (report section 4.4).
  - [ ] Discharge (H5) using Phase 5's standalone lemma. Supply its hypotheses from the local
        context: `hnone` from the reuse check at the mint, `hmem`/`hsub` from the inherited (H3),
        `hacc` from Phase 1's one-hop extension applied along the `par` chain, `hle` from (H1)'s
        `par c < c`, and the no-contradiction property from Phase 3's threaded hypothesis together
        with `hcl : not (closurePred bPers = true)` (`rw [if_neg hcl] at hgo`, `Scheme.lean:5295`).
  - [ ] Discharge the counter-redundancy invariant on this arm: both `nw` and `edges.length`
        increase by exactly one.
- **Timing:** 2 hours
- **Depends on:** 3, 4, 5, 6
- **Verification Tier:** full
- **Scope Hypothesis:** The report's estimate for the whole of section 5.5 is ~350-550 lines
  across the mint arm and the other three arms; this phase claims the mint-arm share, estimated
  at ~250-400 lines. Confirm at implementation time by reporting the actual added-line count for
  this arm alone; a figure far below ~150 suggests an arm case was closed by `simp` without the
  (H5) discharge actually being used, which must be checked by confirming Phase 5's lemma name
  appears in the proof term.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - mint arm of the `key`
    induction inside `intExpandBranches_openBranch_sat`
- **Verification:**
  - `lake build` green
  - `grep -n "<phase-5-lemma-name>" Cslib/.../Scheme.lean` confirms the (*) lemma is actually
    consumed in the mint arm, not bypassed
  - Standing sorry-census criterion holds
- **Exit criteria:** The mint arm re-establishes `IWorldHist` (all five clauses) and the
  counter-redundancy invariant, sorry-free. If a clause cannot be closed, mark [BLOCKED] with the
  clause name and the verbatim goal state; do not introduce a placeholder or relocate the
  obligation.

---

### Phase 8: Alpha, beta, and reuse arm preservation [NOT STARTED]

- **Goal:** Prove `IWorldHist` and the counter-redundancy invariant are preserved by the three
  non-minting arms (report section 5.5).
- **Tasks:**
  - [ ] Confirm from `intExpandBranches.go` (`Scheme.lean:3206-3338`) that the alpha arm
        (`~3249`), reuse arm (`~3263`), and beta arm (`~3282`) all pass `edges` through unchanged
        and leave `nw` unchanged (`intApplyRuleFull_linearResult_nextWorld`, `Scheme.lean:2494-2522`).
  - [ ] Reuse the SAME witness functions unchanged (no extension is needed -- no world is created).
  - [ ] Discharge (H1), (H2), (H4), (H5) by constancy of `edges`, `nw`, and the recorded data.
  - [ ] Discharge (H3) by monotonicity of `b` under `Branch.extendMany` and
        `applyPersistenceFixpoint_mem_preserved` -- the planted facts survive every append.
  - [ ] Discharge counter-redundancy by constancy of both sides.
  - [ ] Discharge the strict label bound on these arms (labels unchanged) if Phase 4 left any arm
        obligation open.
- **Timing:** 1.5 hours
- **Depends on:** 6
- **Verification Tier:** interface
- **Scope Hypothesis:** The report estimates ~100-150 Lean lines for all three arms combined.
  Confirm at implementation time by reporting the actual added-line count; a figure substantially
  above ~250 suggests (H3)'s monotonicity is being re-proved per-arm instead of factored into one
  shared lemma, which should be refactored rather than duplicated.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - alpha, beta, and reuse arms
    of the `key` induction
- **Verification:**
  - `lake build` green
  - Standing sorry-census criterion holds
- **Exit criteria:** All three non-minting arms re-establish `IWorldHist` and counter-redundancy,
  sorry-free. Together with Phase 7 and Phase 6's entry case, the invariant is now established
  inductively.

---

### Phase 9: Pigeonhole depth bound from (*) [NOT STARTED]

- **Goal:** Bound the length of any `par`-ancestor chain of created worlds by `intChainBound phi0`
  (report section 4.3).
- **Tasks:**
  - [ ] Prove that along any `par`-ancestor chain, the pairs `((sfor c).toFinset, obl c)` are
        pairwise distinct: if two chain members `c' < c` had equal pairs, (H5)/(*) would be
        contradicted by `sfor c subset sfor c'`.
  - [ ] Place the pairs in `(intSubfmls phi0).toFinset.powerset x (intSubfmls phi0).toFinset`,
        of cardinality `2 ^ card * card = intChainBound phi0` (`Scheme.lean:1683-1684`).
  - [ ] Conclude chain length <= `intChainBound phi0`.
  - [ ] **Copy, do not edit:** adapt `intCreatedChain_le`'s existing pigeonhole body
        (`Scheme.lean:1774-1814`) with `posFormulasAt b (ws (i+1))` replaced by `sfor` and `hunb`
        replaced by (*). `intCreatedChain_le` must remain byte-identical and sorry-free.
  - [ ] Update `intCreatedChain_le`'s docstring to record that it is now unconsumed by this route
        and to preserve the section 4.1 negative result next to it. Do NOT delete the lemma -- it
        is correct, and the refutation is worth preserving alongside it.
  - [ ] **Binding-constraint check:** the bound must come from blocking combinatorics. Confirm no
        use of the unsigned `eraseDups` / `2 ^ U.length` bound form and no appeal to
        `intUniverse`'s linear range anywhere in this phase.
- **Timing:** 1.5 hours
- **Depends on:** 6
- **Verification Tier:** local
- **Scope Hypothesis:** The report estimates ~120 Lean lines, adapted from `intCreatedChain_le`'s
  body. Confirm at implementation time by `git diff`: `intCreatedChain_le`'s proof body must show
  zero changed lines (docstring-only change permitted). Any change inside its proof falsifies the
  "sibling, not an edit" claim and must be reverted.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - new sibling pigeonhole
    lemma; `intCreatedChain_le` docstring only
- **Verification:**
  - `lake build` green
  - `grep -n "eraseDups" Cslib/.../Scheme.lean` shows no new occurrence introduced by this phase
    in a bound-derivation role
  - `git diff` on `intCreatedChain_le` shows docstring-only changes
  - Standing sorry-census criterion holds
- **Exit criteria:** Chain length <= `intChainBound phi0` is proved sorry-free from (H5), and
  `intCreatedChain_le`'s proof is untouched.

---

### Phase 10: Path-injection size bound and intWorldHist_nw_le [NOT STARTED]

- **Goal:** Convert depth (Phase 9) plus branching (H4) into `nw <= WBound phi0`, matching
  `WBound`'s exact shape (report section 4.5).
- **Tasks:**
  - [ ] Confirm `WBound phi = (B + 1) ^ (D + 1)` with `B = (intSubfmls phi).toFinset.card`,
        `D = intChainBound phi` (`Scheme.lean:1692-1693`), and that this is exactly
        `Fintype.card (Fin (D+1) -> Option S)` with `|S| = B` via `Fintype.card_pi_const`
        (`Mathlib.Data.Fintype.BigOperators`).
  - [ ] Define `parIter` and depth from `par`, well-founded by `par c < c`.
  - [ ] Construct the injection
        `{0, ..., nw-1} -> (Fin (intChainBound phi0 + 1) -> Option {chi // chi in (intSubfmls phi0).toFinset})`
        mapping `c` to its root-to-`c` path of fired implications, padded with `none`.
  - [ ] Prove the map is well-defined: path length <= `D` by Phase 9's depth bound.
  - [ ] Prove injectivity from (H4): each step of the path is determined by parent plus fired
        formula.
  - [ ] Conclude `nw <= WBound phi0` via `Finset.card_le_card_of_injOn` plus
        `Fintype.card_pi_const`.
  - [ ] State and prove `intWorldHist_nw_le {phi0 b e nw edges} (hHist : IWorldHist phi0 b e nw edges) : nw <= WBound phi0`.
  - [ ] **Binding-constraint check:** no arithmetic slack argument, no `2 ^ U.length` form, no
        appeal to `intUniverse`'s linear range. The `WBound` shape is matched exactly by design.
- **Timing:** 2 hours
- **Depends on:** 6, 9
- **Verification Tier:** local
- **Scope Hypothesis:** The report estimates ~200-350 Lean lines (`parIter`, depth, path
  construction, injectivity, the two Mathlib applications). Confirm at implementation time by
  reporting the actual figure. If `Fintype.card_pi_const` or `Finset.card_le_card_of_injOn` turns
  out not to apply in the needed form, report the exact mismatch rather than substituting a
  looser bound -- a looser bound that does not reach `WBound` is not a discharge.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - `parIter`, depth, path
    injection, `intWorldHist_nw_le`
- **Verification:**
  - `lake build` green
  - Temporary `#print axioms intWorldHist_nw_le` shows no `sorryAx`; remove before commit
  - Standing sorry-census criterion holds
- **Exit criteria:** `intWorldHist_nw_le` is proved sorry-free and derives `nw <= WBound phi0`
  purely from blocking combinatorics.

---

### Phase 11: Retire the sorry, rewire the call site, final verification [NOT STARTED]

- **Goal:** Remove DP-2. Replace `intFreshMint_preserves_nw`'s false statement with the correctly
  premised form and discharge the new premise at the sole call site (report sections 3.3, 8 phase 9).
- **Tasks:**
  - [ ] Replace the body of `intFreshMint_preserves_nw` (`Scheme.lean:2602-2605`). Either:
        (a) delete it in favour of `intWorldHist_nw_le` applied to the post-mint state, or
        (b) keep the name with the strengthened premise of report section 3.3 -- the post-mint
        history invariant `IWorldHist phi0 (Branch.extendMany bPers newForms) (e ++ [sf]) (nw + 1) (edges ++ [newE])`
        concluding `nw + 1 <= WBound phi0` -- proved by `intWorldHist_nw_le`.
        Prefer (b) for continuity unless (a) is materially simpler.
  - [ ] Rewire the call site (`Scheme.lean:5362-5363`,
        `have hNW_ext : nw' <= WBound phi0 := by rw [hnw'_eq]; exact intFreshMint_preserves_nw hNWP_head`)
        to supply the post-mint `IWorldHist` established by Phase 7's mint-arm preservation, in
        place of the bare `hNWP_head` (`Scheme.lean:5299`).
  - [ ] **Anti-weakening check:** the new premise MUST be discharged at the call site from the
        threaded invariant. If it can only be supplied by adding a further undischarged hypothesis
        upstream, that is a weakening in disguise -- mark [BLOCKED] instead.
  - [ ] Rewrite the DP-2 docstring (`Scheme.lean:2587-2596`) to record what actually happened:
        the numeric-premise route is not inductive; the `intCreatedChain_le`-style final-branch
        transfer is not derivable (report section 4.1); the route taken is the mint-time
        snapshot-free residue (*).
  - [ ] Remove every temporary `#print axioms` line added during Phases 1-10.
  - [ ] Confirm the two refuted cheap routes are recorded as dead ends in the summary so they are
        not re-derived: fuel-bounded counter (circular), flat pigeonhole without the tree
        (siblings never block each other).
  - [ ] Confirm DP-3, DP-4, and DP-5 are untouched.
- **Timing:** 1 hour
- **Depends on:** 7, 8, 9, 10
- **Verification Tier:** full
- **Scope Hypothesis:** Asserted scope is ~30-60 changed lines in `Scheme.lean` only, plus
  deletions of temporary diagnostics. Confirm at implementation time by `git diff --stat` over the
  whole task: the only files changed across all eleven phases should be
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` and
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`. Any third file falsifies the
  hypothesis and must be explained.
- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - DP-2 lemma, its docstring,
    the call site, diagnostic cleanup
- **Verification:**
  - `lake build` green
  - `lake build 2>&1 | grep -c "declaration uses 'sorry'"` decreased by exactly 1 from its
    pre-task value
  - `grep -rn --include=*.lean -E "^[[:space:]]*sorry[[:space:]]*$" Cslib/Logics/Propositional/Tableau/ | wc -l`
    reads exactly **3**
  - `grep -rn --include=*.lean -E "^[[:space:]]*sorry[[:space:]]*$" Cslib/ | wc -l` reads exactly **5**
  - The three surviving Tableau sorries are exactly `Scheme.lean:633` (DP-5),
    `Intuitionistic/Completeness.lean:140` (DP-3), `Minimal/Completeness.lean:128` (DP-4)
  - `grep -rn "#print axioms" Cslib/` returns nothing added by this task
- **Exit criteria:** DP-2 discharged, no sorry relocated, no statement weakened, `lake build`
  green, counts as above.

---

## Testing & Validation

- [ ] `lake build` green at the end of every phase (module-local build permitted mid-phase per the
      phase's Verification Tier; the full gate still runs before each phase closes).
- [ ] Tableau-subtree bare-sorry census reads 4 through Phase 10 and exactly 3 after Phase 11.
- [ ] Repo-wide bare-sorry census reads 6 through Phase 10 and exactly 5 after Phase 11.
- [ ] `lake build 2>&1 | grep -c "declaration uses 'sorry'"` decreases by exactly 1 across the task.
- [ ] No `sorry`, `admit`, `native_decide`, `def X := True`, `theorem X := trivial`, or other
      vacuous placeholder introduced at any point.
- [ ] `intFImpReuseWitnessAnc?` (`Expansion.lean`) byte-identical to its pre-task state.
- [ ] `intCreatedChain_le`'s proof body byte-identical to its pre-task state (docstring change
      permitted).
- [ ] `IAllConsistent` and `ILabelBound` unchanged (new invariants are companions, not merges).
- [ ] No `eraseDups` / `2 ^ U.length` bound form used in any bound derivation.
- [ ] No appeal to `intUniverse`'s linear range in any bound derivation.
- [ ] Every hypothesis added to an existing declaration is discharged at its call site within the
      same phase that added it.
- [ ] `Scheme.lean:633`, `Intuitionistic/Completeness.lean:140`, `Minimal/Completeness.lean:128`
      untouched.

## Artifacts & Outputs

- `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/plans/01_dp2-worldhist-mint-invariant.md` (this file)
- `specs/585_prove_post_blocking_world_bound_chain_and_mint_invariant/summaries/01_dp2-worldhist-mint-invariant-summary.md` (on completion)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` - modified
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` - modified (Phase 2 only)

## Rollback/Contingency

- Phases 1-4 are strictly additive and independently verifiable. Each may be kept even if the
  route later fails: each removes a named absent lemma and none can be invalidated by a change of
  route. Recommended to execute and commit them regardless of the Phase 5 outcome.
- **If Phase 5 (the gate) is [BLOCKED]**: keep Phases 1-4's commits, leave DP-2's sorry in place,
  and stop. Record the failing conjunct, the verbatim goal state, and the attempted tactics. The
  correct next action is a new research dispatch on the failing conjunct, not a placeholder and
  not a re-attempt of the section 4.1 final-branch route.
- **If a later phase fails**: the work is confined to two files. Roll back with per-phase commits
  (`git revert` of the phase commit), never with a destructive operation on a dirty tree -- run
  `bash .claude/scripts/git-snapshot.sh 585` first if the tree is dirty.
- No downstream consumer of `Scheme.lean` sees an interface change except through Phase 3's
  hypothesis on `intExpandBranches_openBranch_sat` (a private lemma with one in-file call site),
  so rollback has no cross-module blast radius.
