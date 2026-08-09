# Canonical corrected-framing text (shared source for H1-H10)

## Disposition line (opens every hunk)

**Open — augmented-frame route known-bad, admissible edge space characterised.**

## Canonical paragraph (full form, used at H1; condensed at other sites, each pointing back at H1)

The `∃ edges` conjunct of `openBranch_countermodel` is **open, not refuted**. Two independent
arguments support this:

1. **Structural (needs no computation).** `IValid φ` quantifies over every preorder and every
   upward-closed valuation, so any refutation of this lemma must exhibit an IPC-valid `φ` on
   which the algorithm returns `.openBranch`. `phiRef1 := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb))
   → pr` is not even classically valid, so it was never a candidate refutation of this lemma,
   whatever it does to any one frame choice.
2. **Computational.** The admissible `edges` are exactly the subsets of the atom-set-inclusion
   preorder `⊑` (`w ⊑ w' ↔ A(w) ⊆ A(w')` where `A(w)` is `w`'s positive-atom set on `b`), and
   every such subset is automatically upward-closed — so conjunct 1 needs no fact about the
   tableau algorithm at all. On the branch the real `intuitionisticTableau` returns for
   `phiRef1`, the pruned edge set `edges = [(1, 0)]` satisfies BOTH conjuncts (computed, not
   CI-protected: see the scratch probes `WitnessProbe.lean`/`WitnessSearch2.lean`, not promoted
   into `CslibTests/`). Exhaustive enumeration over the complete admissible space finds 40
   witnesses for `phiRef1` alone, and witnesses for every other open-branch formula tested.

What is refuted is a **witness choice**, not the statement: the AUGMENTED frame
`intAccessPreorder edges` (the `augSets` witness `intExpandBranches_openBranch_sat` threads,
carrying the algorithm's loop-back edges) fails upward closure at `phiRef1`
(`CslibTests/BetaSplitRefutation.lean`, zero errors, zero sorries, `branchesAgree = true`).
That is a real refutation of *augmented-frame positive-formula persistence*, and the
`intFImpReuseWitnessAnc?` frame-construction defect it exposes is real and unfixed. It is not a
refutation of `openBranch_countermodel`'s statement, because `truthLemma`'s frame is a
parameter — the refuted invariant is needed only when that parameter IS the augmented frame.

**Honesty bound.** The general `∀ φ` statement remains unproved. The maximal inclusion frame `⊑`
is NOT a uniform witness — computed evidence shows it fails at exactly the `phiRef1`/`phiRef3`
family (`WitnessSearch3.lean`, computed, not CI-protected). Per the structural argument above,
proving the lemma in general is equivalent to proving the tableau procedure complete: this is
not a small residual, it is the completeness theorem itself. The remaining obligation is a
uniform construction of `edges` from `b` plus a truth lemma over that frame.

## C4 checklist (present in every corrected hunk, verified at Phase 6)
- [ ] states the `∀ φ` statement is unproved
- [ ] states the maximal inclusion frame `⊑` is not a uniform witness (fails at
      `phiRef1`/`phiRef3`)
- [ ] does not claim the lemma is proved

## C5 checklist (what survives, must not be deleted/weakened)
- [ ] `BetaSplitRefutation.lean`'s counterexample is still described as a real refutation of
      augmented-frame positive-formula persistence
- [ ] `intFImpReuseWitnessAnc?`'s frame-construction defect is still named as real and unfixed

## C7 evidence-honesty checklist
- [ ] leads with the structural argument (§2/argument 1 above), which is self-contained
- [ ] labels the `[(1, 0)]` witness / enumeration counts / maximal-frame failure as computed
      against the real algorithm, not CI-protected facts (the probes are not in `CslibTests/`)
