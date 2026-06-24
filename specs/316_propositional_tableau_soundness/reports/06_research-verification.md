# Research Verification Report: Report 05 (FreshAbove Strategy)

- **Task**: 316 - propositional_tableau_soundness
- **Type**: Adversarial verification / vetting dispatch (read-only; no `.lean` or plan edits)
- **Report under review**: `specs/316_propositional_tableau_soundness/reports/05_intuitionistic-soundness-induction.md`
- **Session**: sess_1782335183_8462da_316verify
- **Completed**: 2026-06-24
- **Standards applied**: (1) Literature authority (H3 reference grounding); (2) Proof-assistant ground truth (Lean goal-state inspection — strongest standard for a formalization)
- **Reference grounding tier**: Tier 1 (literature-backed; BibKey verification against `references.bib`)

## Executive Summary

The report's recommended **`FreshAbove` invariant** strategy is **SOUND and SAFE to implement**,
confirmed at the strongest available standard (Lean goal-state inspection at the sorry sites), with
literature grounding that rests on authoritative sources (Fitting 1983 §9.5, Fitting 2014 §5–6,
Waaler–Wallen Handbook Ch. 5) and NOT solely on the non-authoritative Open Logic Project.

**Final verdict: APPROVE-WITH-CORRECTIONS.** The strategy is correct; two non-blocking corrections
concern citation hygiene (BibKey gaps in `references.bib`), and one minor clarification concerns the
already-resolved L978 `.symm` matter. None invalidates the implementation plan.

Decisive finding (supersedes all textbook citations): the `hfresh` goal `∀ sf' ∈ bPers,
sf'.label ≠ nwH` at line 945 is **provably unprovable from the hypotheses currently in scope** —
inspection of the live goal state shows `nwH` is a bare `ℕ` from destructuring `pendingNW = nwH :: nwT`
with **no hypothesis** relating it to the labels on `bPers`/`bh`/`b`. The freshness invariant is
therefore genuinely necessary, not a detour. Lean ground truth confirms the report's central claim (F2).

## Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Authority | Lean Target | Translation Notes |
|--------------|--------|-----------|-------------|-------------------|
| Per-rule satisfiability-preservation (≥1 child satisfiable) | Fitting1983 §9.5 / Fitting2014 §6 | Authoritative | `intRule_preserves_sat` (L83) | Conclusion is a `match` on `intApplyRuleFull`, returning ∃worldOf' (linear) or ∃br (branching) |
| F-→ requires a FRESH prefix/world | Fitting1983 §9.5 / WaalerWallen1999 Ch.5 | Authoritative | `hfresh`/`FreshAbove` (L945, L961) | "new prefix on the branch" → `∀ sf'∈b, sf'.label ≠ nw` |
| Persistence (Lift) lemma: forced at w ⟹ forced at w'≥w | Fitting2014 §6 (Lift) / Fitting1969 | Authoritative | `iforces_persistence` (Kripke.lean) | Used inside `intRule_preserves_sat` F-→ arm (L223) |
| Conservative model extension at fresh prefix via `update` | Fitting1983 §9.5 | Authoritative | `monotoneEdges_update` (L688–762) | `Function.update worldOf nw w'`; needs 3 edge-freshness facts + `hle` |
| Kripke semantics for IPL | ChagrovZakharyaschev1997 §2.2 | Authoritative | module docstrings | Co-cited in `Rules.lean`/`Expansion.lean` |

## Standard 1 — Literature Authority (claim-by-claim grounding table)

| # | Load-bearing claim | Cited source(s) | Authority rank | Independent corroboration | VERDICT |
|---|--------------------|-----------------|----------------|---------------------------|---------|
| L1 | Soundness = per-rule satisfiability-preservation to ≥1 child | Fitting1983 §9.5; Fitting2014 §6 | Authoritative | Web search confirms Fitting "Proof Methods" book states: "whenever all prefixed formulas on a branch are satisfiable, any rule application results in at least one extended branch satisfiable"; Fitting2014 §6 title "Soundness and Completeness" confirmed via PDF fetch | confirmed |
| L2 | The F-→ rule requires a FRESH prefix | Fitting1983 §9.5; WaalerWallen1999 Ch.5; (also OpenLogic L107/L349) | Authoritative (primary) | Web search: "a prefix is...new [if it does not already occur on] the branch"; Fitting2014 §5 "Prefixed Intuitionistic Tableaux" confirmed; **AND Lean goal-state: hfresh unprovable without it** | confirmed (Lean-superseded) |
| L3 | Freshness makes the model extension conservative | Fitting1983 §9.5 | Authoritative | `monotoneEdges_update` requires exactly `hnw_not_child ∧ hnw_not_parent ∧ hnw_ne_parent` — the Lean encoding of "nw new to the edges"; confirmed by reading L688–699 | confirmed (Lean) |
| L4 | Persistence/Lift lemma factoring | Fitting2014 §6 (Lift); Fitting1969 | Authoritative | `iforces_persistence` exists in Kripke.lean and is used at Soundness L223 | confirmed (Lean) |
| L5 | Satisfiable-set definition (m : Pfx→W, m(σ)≤m(σ.n), T/F forcing) | Fitting2014 §5–6; **OpenLogic** (L107) | Authoritative (primary) + non-authoritative (secondary) | Fitting2014 §5 title "Propositional Prefixed Intuitionistic Tableaux" confirmed via PDF fetch; matches `intBranchSatisfied` + `MonotoneEdges` | confirmed |

### Citation attribution check (real / correctly attributed?)

- **Fitting1969** — present in `references.bib` (L196), correctly attributed (North-Holland, 1969). ✓
- **ChagrovZakharyaschev1997** — present in `references.bib` (L75), §2.2 matches module docstring. ✓
- **Fitting1983** — cited in module docstrings as "Chapter 4" and in the report as "Ch. 9 §9.5". **NOT in `references.bib`.** The book is real (Springer/Reidel Synthese Library vol. 169, confirmed via web search: link.springer.com 10.1007/978-94-017-2794-5). Correctly attributed, but missing BibKey. → CORRECTION 1.
- **Fitting2014** — real, peer-reviewed (Notre Dame J. Formal Logic 55(1):41–61, DOI 10.1215/00294527-2377869). PDF fetched: §5 "Propositional Prefixed Intuitionistic Tableaux" and §6 "Propositional Tableau Soundness and Completeness" confirmed — the report's "§5–6" attribution is exact. **NOT in `references.bib`.** → CORRECTION 1.
- **WaalerWallen1999 / Handbook1999** — Handbook of Tableau Methods (Kluwer, 1999, DOI 10.1007/978-94-017-1754-0) is real; the Waaler–Wallen chapter "Tableaux for Intuitionistic Logics" exists. The exact "Ch. 5, pp. 255–296" page span could not be independently confirmed in this pass (corpus empty; no page-level web hit). Real and authoritative; page span uncorroborated. **NOT in `references.bib`.** → CORRECTION 1 + flag.
- **OpenLogic** — non-authoritative teaching text (correctly identified as such in the user directive). Real (builds.openlogicproject.org). Used only as secondary corroboration. → see Standard-1 OpenLogic list below.

## Open Logic Project dependency audit

OpenLogic appears at exactly two locations in report 05:

1. **Line ~107** — co-cited with Fitting2014 §5–6 for the satisfiable-set definition (claim L5).
   **Primary support = Fitting2014 (peer-reviewed, authoritative).** OpenLogic is secondary. → NOT sole support.
2. **Line ~349** — the `[OpenLogic]` Appendix reference-list entry itself (not a claim). The freshness
   case it describes is independently supported by Fitting1983 §9.5, Fitting2014 §5–6, and Waaler–Wallen. → NOT sole support.

**Result: NO load-bearing claim rests solely on the Open Logic Project.** Every claim OpenLogic
touches is independently confirmed by an authoritative source (Fitting2014, peer-reviewed) AND, for
the single most load-bearing claim (freshness is necessary), by Lean goal-state inspection — which
supersedes any textbook.

## Standard 2 — Proof-Assistant Ground Truth (5 concrete Lean specifics)

All verified read-only against the working tree (file may be concurrently edited; line numbers are
current at time of read).

| # | Report claim | Verification method | Result |
|---|--------------|---------------------|--------|
| 1 | `hfresh` goals genuinely cannot be discharged without a freshness invariant | `lean_goal` at L945 | **CONFIRMED.** Goal `∀ sf'∈bPers, sf'.label ≠ nwH`; scanning all hypotheses, `nwH` is a bare `ℕ` from `pendingNW = nwH :: nwT` with NO `< nwH` / `FreshAbove` / label-bound hypothesis in scope. Invariant is necessary. |
| 2 | Cited lemmas EXIST, sorry-free, with claimed signatures | `grep` decls + sorry-scan L400–770; `lean_local_search` | **CONFIRMED.** `intRule_preserves_sat` (L83), `applyPersistenceFixpoint_sat` (L404, report said "L404–420" ✓), `monotoneEdges_go` (L527), `monotoneEdges_update` (L688–762 ✓ exact), `iforces_persistence` (Kripke.lean). Zero `sorry` in L400–770. |
| 3 | `intRule_preserves_sat` returns a `match` (so `.1/.2` invalid; `rw [hresult_sf]` needed first) | Read L95–103 | **CONFIRMED.** Conclusion is literally `match intApplyRuleFull sf nw b with \| .linearResult … => ∃ worldOf', … \| .branchingResult … => ∃ br ∈ …`. Working branchingResult case does `rw [hresult_sf] at hpres` at L970. |
| 4 | `monotoneEdges_update` consumes exactly the 3 edge-freshness facts + `worldOf parentLabel ≤ w'` | Read L688–699 | **CONFIRMED.** Params: `hnw_not_child`, `hnw_not_parent`, `hnw_ne_parent`, `hmono`, `hle : worldOf parentLabel ≤ w'`. Concludes `MonotoneEdges (Function.update worldOf nw w') (edges ++ [(nw, parentLabel)])` — matching the F-→ arm's `Function.update worldOf nw w'` (L190). |
| 5 | Fuel IH `ih` (not `ih_inner`) is correct for linearResult `bp=bh`; L978 fix is `.symm` orientation on `hdlength_edges`/`List.zip_append` | `lean_goal` L945 + L978 | **CONFIRMED (with clarification).** Live goal: `ih` quantifies over `branches/edgeSets…fuel''`; `ih_inner` over `bt`/pending. `hgo` in the linear arm reduces to `intExpandBranches (done++[…]++bt) … fuel''` → `ih` is correct. The L978 membership uses `rw [List.zip_append (by exact hdlength_edges)]` — current working-tree orientation is `hdlength_edges` AS-IS (no `.symm`), which is correct. The "`.symm` build error" was a *prior transient* error; the fix in the tree is already correct. See CORRECTION 3 (clarification only). |

## Adversarial Self-Verification

- **Challenge to L1/L2 (could the freshness rest only on OpenLogic?):** Refuted. Web search confirms
  Fitting's "Proof Methods" book and Fitting2014 (peer-reviewed) both state the new-prefix condition;
  and Lean goal-state proves necessity independent of any source.
- **Challenge to "lemmas exist & sorry-free":** Verified by direct grep of declarations and an
  explicit sorry-scan of L400–770 (the helper region) returning empty. Not taken on the report's word.
- **Challenge to "match-not-product":** Verified by reading the actual lemma conclusion (L95–103), not
  inferred — it is syntactically a `match`.
- **Challenge to "ih not ih_inner":** Verified against the live goal-state quantifier shapes, not the
  report's prose.
- **Uncertain / unconfirmed (confidence noted):**
  - WaalerWallen1999 exact page span "255–296" — *medium confidence*; chapter exists and is
    authoritative, but the precise pages were not independently corroborated this pass.
  - Fitting1983 "Ch. 9 §9.5" precise section number — *medium-high confidence*; book confirmed real and
    on-topic; the report and module docstrings disagree on chapter (docstring says Ch. 4, report says
    Ch. 9 §9.5). Both may be correct (different editions/sections); flagged as CORRECTION 2.
- **Zero-debt compliance:** The recommended plan closes all 3 sorries structurally (no sorry deferral,
  no new axioms). Compliant.
- **Reuse completeness:** All 5 reused lemmas pre-exist; the only new abstraction is `FreshAbove` + 4
  preservation lemmas — a strengthening, not a redesign. Reuse-first satisfied.

## Corrections the implementer / planner must apply

- **CORRECTION 1 (citation hygiene, non-blocking):** `references.bib` lacks `Fitting1983`,
  `Fitting2014`, `WaalerWallen1999`, and `Handbook1999`, all of which the report cites as
  authoritative support. Add these BibKeys before any artifact uses `[Fitting1983]`/`[Fitting2014]`
  citations, or the citations will not resolve. (Does NOT affect the proof strategy.)
- **CORRECTION 2 (chapter-number discrepancy, non-blocking):** Module docstrings cite Fitting1983
  **Ch. 4**; report 05 cites **Ch. 9 §9.5**. Reconcile (likely Ch. 4 = rules/tableaux, the soundness
  proof in a later section) so the docstring and report agree. Does not affect correctness.
- **CORRECTION 3 (clarification, already resolved):** The report flags an L978 `.symm` orientation
  build error. In the current working tree L978 is `rw [List.zip_append (by exact hdlength_edges)]`
  with NO `.symm` — already correct. The implementer should mirror this exact orientation in the new
  linearResult `bp=bh` case and must NOT add a `.symm`.

## Final Verdict

**APPROVE-WITH-CORRECTIONS.**

The `FreshAbove` invariant approach is sound and safe to implement as planned. Its single most
load-bearing claim (freshness necessity) is confirmed by Lean goal-state inspection — the strongest
possible standard — and its literature grounding rests on authoritative, peer-reviewed sources
(Fitting1983, Fitting2014, Waaler–Wallen), NOT solely on the Open Logic Project. The three concrete
Lean specifics that would sink an implementation if wrong (match-not-product, ih-vs-ih_inner, the
3+1 args to `monotoneEdges_update`) are all confirmed correct against the actual code.

The corrections are citation-hygiene only (add 4 BibKeys; reconcile one chapter number) plus one
already-resolved clarification (no `.symm` at L978). None blocks implementation.
