# Teammate C Findings: Gaps, Inconsistencies, and Blind Spots
## Task 313 — Propositional Logic Proof Systems Overview (Critical Review)

**Reviewer focus**: Tableau systems in progress, conservative extension results, sequent calculi in
progress, and the overarching vision of four equivalent proof systems across three logics.

---

## Executive Summary

The overall architecture is sound and intellectually coherent. However, several significant gaps
and one critical deployment issue undermine the story when read carefully. The most acute problem
is that LK cut elimination is written and appears correct but is **excluded from the build** due to
reported build errors. This silently breaks the LK story. A second concern is that the tableau
systems have **13 sorry instances across 5 files**, and the decision procedure instances for
intuitionistic and minimal logic are structurally sorry-free only in the sense that they propagate
sorry-tagged witnesses — they are not independently meaningful without the underlying proofs. The
conservative extension chain also has two missing links that matter for the chain narrative.

---

## Concern 1: LK Cut Elimination Is Written But Excluded
**Severity: CRITICAL**

`Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` is a 873-line file with
zero sorries. It contains a complete, apparently correct proof of `LKProof.cutAdmissibility`
and `LKProof.cutElim`, following the lexicographic induction on formula complexity and proof
height as documented in the literature.

However, `LK.lean` contains:

```
-- CutElimination excluded: has build errors requiring dedicated proof rewrite
-- public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
```

This means:
- LK cut elimination does not appear in any downstream module (including `ProofSystemEquivalence`).
- The three-way equivalence for CPL in `ProofSystemEquivalence.lean` does not include a fourth
  entry for `CutFreeLKProof`, even though LJ's three-way equivalence module includes cut
  elimination from LJ.
- The Zulip comment cannot honestly say "LK cut elimination is proved" without noting this.

The asymmetry between LJ (which exports cut elimination) and LK (which silently excludes it)
will confuse readers. The reason for the build errors is not documented in any artifact,
and task 314 is still in `[IMPLEMENTING]` status — the cause of the exclusion is unknown
without running a build.

**Action needed**: Before writing the Zulip post, determine whether the build errors are due to
upstream changes that happened after the file was written (e.g., changes to `Proposition.or.inj`
or `Finset.insert_comm`), or whether the proof has a genuine logical gap. If build errors are
cosmetic (renaming/API drift), they should be fixed before the post goes out.

---

## Concern 2: Tableau Sorries Are Deeper Than Reported
**Severity: IMPORTANT**

The task inventory says "6 sorry in 3 files for classical, 6+7 for intuitionistic". The actual
count from file inspection is:

| File | Actual sorry count |
|------|--------------------|
| `Classical/Soundness.lean` | 1 (classicalTableau_sound induction) |
| `Classical/Completeness.lean` | 3 (classicalOpenBranch_countermodel x2, truth lemma x1) |
| `Intuitionistic/Soundness.lean` | 2 (intRule_preserves_sat, intuitionisticTableau_sound) |
| `Intuitionistic/Completeness.lean` | 3 (truth lemma x3) |
| `Minimal/DecisionProcedure.lean` | 2 (minimalTableau_sound, minimalTableau_complete) |

Total: **11 substantive sorries** across 5 files.

Critically:

1. The `Decidable (Tautology φ)` instance `instDecidableTautologyTableau` in
   `Classical/DecisionProcedure.lean` is only structurally sorry-free: it calls
   `classicalTableau_sound` and `classicalTableau_complete`, both of which are sorry. The
   file's module comment acknowledges this but calls the existing `instDecidableTautology`
   in `Bool.lean` "the primary sorry-free decision procedure" — which means the classical
   tableau does not yet provide an independent, sorry-free decision procedure.

2. Similarly, `instDecidableIValid` and `instDecidableMValid` in the intuitionistic and minimal
   modules depend on their respective sorry-tagged soundness/completeness theorems.

3. The minimal tableau module (`Minimal/DecisionProcedure.lean`) has only one file — there are
   no `Minimal/Soundness.lean`, `Minimal/Completeness.lean`, or `Minimal/Expansion.lean` files.
   The minimal tableau reuses `intExpandBranches` (from `Intuitionistic/Expansion.lean`) with a
   different closure predicate. This is architecturally reasonable but means the minimal system
   has no standalone soundness or completeness proofs, only the two sorried stubs in the
   decision procedure file.

4. Task 319 (Minimal Tableau Infrastructure) depends on 316 and 317 and is `[NOT STARTED]`.
   This means minimal is waiting for the entire intuitionistic pipeline to complete first.

**For the Zulip post**: Be accurate. The tableau infrastructure is in place and the algorithms
are implemented, but the mathematical proofs of soundness and completeness are not yet complete
for any of the three variants. The `Decidable` instances are structural placeholders contingent
on completing these proofs.

---

## Concern 3: Missing Tableau–SC and Tableau–Hilbert Equivalence Bridges
**Severity: IMPORTANT**

`ProofSystemEquivalence.lean` currently contains:
- CPL: Hilbert ↔ ND ↔ LK (three-way TFAE)
- IPL: Hilbert ↔ ND ↔ LJ (three-way TFAE)
- MPL: Hilbert ↔ ND (two-way only)

No tableau equivalences are stated or planned in any file or task. Specifically:
- There is no `hilbert_iff_classicalTableau` or `classicalTableau_iff_lk`.
- There is no `hilbert_iff_intuitionisticTableau` or `intuitionisticTableau_iff_lj`.
- There is no task in state.json for tableau–SC bridges.

The vision of "four equivalent proof systems" requires six pairwise equivalences (or
transitivity through a hub). Currently, the equivalence chain is:

  **Hilbert ↔ ND ↔ SC** (for CPL, IPL)
  **Hilbert ↔ ND** (for MPL)
  **Tableau ↔ Hilbert** (via soundness/completeness, once sorry-free)

The last link exists only implicitly: `classicalTableau_decides` states
`classicalTableau φ = closed ↔ Tautology φ`, and `prop_completeness_iff_tautology` connects
to Hilbert derivability. But this is not packaged as a named bridge theorem in
`ProofSystemEquivalence.lean`, and it is not sorry-free.

**Structural issue**: Tableau–SC bridges (e.g., LK sequent provability iff tableau closes)
are known results in the literature but are not planned anywhere in the task inventory. The
decidability advantage of tableau would be more clearly stated if the connection to SC cut
elimination (subformula property → decidability) were explicit.

---

## Concern 4: No Minimal Sequent Calculus (LM) — Acknowledged but Gap Matters
**Severity: IMPORTANT**

`ProofSystemEquivalence.lean` explicitly acknowledges that there is no minimal sequent
calculus in CSLib:

> "No minimal sequent calculus (LM) exists in CSLib, so only a two-way equivalence is available."

This is not a bug, but it does create an asymmetry in the narrative: the "four equivalent proof
systems" vision (Hilbert, ND, SC, Tableau) cannot be fully realized for MPL — only Hilbert and
ND are connected.

The absence of an LM (or G3m) sequent calculus is mathematically interesting. Minimal logic
does have sequent calculus formulations (G3m removes efq from G3i), and the minimal tableau
reuses intuitionistic expansion rules. The Zulip post should address this gap honestly:
either by noting that LM is a planned future task, or by explaining why the minimal case
only achieves three-way equivalence (Hilbert ↔ ND ↔ Tableau) rather than four-way.

---

## Concern 5: Conservative Extension Chain Is Incomplete
**Severity: IMPORTANT**

The intended chain from `state.json` task 312 description is:

  IPL⟨→,⊤⟩ ⊂ IPL⟨∧,→,⊤⟩ ⊂ MPL ⊂ IPL ⊂ CPL

Current status:
- IPL conservative over MPL (bot-free formulas): **DONE** (`hilbertIplConservativeOverMpl`)
- IPL conservative over IPL⟨∧,→,⊤⟩ (conjunction-implication): **DONE** (`hilbertIplConservativeOverConjImp`)
- IPL conservative over IPL⟨∧,→,⊥,⊤⟩ (conjunction-implication-bot): **DONE** (task 318)
- CPL conservative over IPL (via Glivenko): **PARTIAL** — Glivenko (`¬¬φ` derivable in IPL if derivable in CPL) is proved, but this is weaker than CPL being conservative over IPL for arbitrary formulas. True conservativity would require: if φ is derivable in CPL and φ is an IPL formula, then φ is derivable in IPL. This is the double-negation translation, not mere Glivenko.
- IPL conservative over IPL⟨→,⊤⟩: **NOT STARTED** (task 311, depends on Diego embedding task 310 which is in progress)
- Unified chain module: **NOT STARTED** (task 312, depends on 311)

The CPL/IPL relationship in CSLib uses Glivenko rather than Markov translation or
Friedman's theorem. This is a legitimate formalization choice, but it means CPL is not
technically shown to be conservative over IPL in the standard sense (every CPL-derivable
formula that is IPL-syntactically well-formed is also IPL-derivable). Glivenko gives a
weaker result: CPL derives `φ` implies IPL derives `¬¬φ`. The Zulip comment should
be precise about which direction of conservativity is claimed.

---

## Concern 6: The LJ Cut Elimination Sorry Is Non-Trivial
**Severity: IMPORTANT**

`LJ/CutElimination.lean` has exactly 1 sorry in `cutAdmissibility` at line 103:

```lean
noncomputable def cutAdmissibility (A : Proposition Atom) (Γ : Ctx Atom) ...
    (d₁ : CutFreeLJProof (Γ ⊢ A)) (d₂ : CutFreeLJProof (insert A Γ ⊢ C)) :
    CutFreeLJProof (Γ ⊢ C) := by
  sorry
```

The module comment says "The proof requires nested well-founded induction that is technically
challenging to express with Lean 4's pair-indexed inductive type `LJProof`."

The downstream `LJProof.cutElim` structural induction calls this sorry:
```lean
| cut A _ _ ih₁ ih₂ =>
    obtain ⟨d₁'⟩ := ih₁
    obtain ⟨d₂'⟩ := ih₂
    exact ⟨cutAdmissibility A _ _ d₁' d₂'⟩
```

So `LJProof.cutElim` depends on the sorry. However, the IPL three-way equivalence in
`ProofSystemEquivalence.lean` does NOT depend on cut elimination — it uses the bridge
through Hilbert and Kripke semantics. Cut elimination is an independent structural property.

**For the Zulip post**: Be precise. LJ cut elimination is stated but not fully proved. The
three-way equivalence for IPL is independent of this and is sorry-free. These are two separate
claims and should not be conflated.

---

## Concern 7: Tableau ↔ Decidability Argument Is Incomplete
**Severity: IMPORTANT**

The classical tableau `DecisionProcedure.lean` file acknowledges:

> "The existing `instDecidableTautology` in `Bool.lean` provides the primary sorry-free
> decision procedure."

This means the decidability advantage attributed to tableau is not currently provided by the
tableau algorithm itself, but by an independent Boolean enumeration. The comment that
`instDecidableTautologyTableau` is "an alternative" that "does not require `Fintype Atom`" is
correct but forward-looking — the instance is sorry-dependent.

A stronger claim would be: "the tableau algorithm terminates and decides tautologyhood without
requiring `Fintype Atom`, providing a decision procedure for infinite atom alphabets." This claim
is architecturally sound but not yet formally proved (soundness/completeness are sorry'd).

**Additional gap**: Intuitionistic and minimal validity previously had no `Decidable` instances.
The tableau architecture creates the right structure for such instances. But because the
underlying soundness/completeness are sorry'd, these are pre-declared placeholders rather than
actual sorry-free implementations. The `instDecidableIValid` and `instDecidableMValid` are the
most novel contributions of the tableau work — they have no sorry-free fallback in `Bool.lean`
(intuitionistic validity is not Boolean-decidable by enumeration without the tableau or LJ).

---

## Concern 8: Minimal Tableau Has No Soundness/Completeness Files
**Severity: IMPORTANT**

Unlike classical and intuitionistic, which each have dedicated `Soundness.lean` and
`Completeness.lean` files, the minimal tableau has only `Minimal/DecisionProcedure.lean` (the
single file containing everything). There are no `Minimal/Soundness.lean`, `Minimal/Expansion.lean`
(it reuses intuitionistic), or `Minimal/Completeness.lean`. This creates an organizational
inconsistency:

- The sorry-tagged `minimalTableau_sound` and `minimalTableau_complete` live in the "decision
  procedure" file rather than in properly scoped soundness/completeness files.
- Task 319 (Minimal Tableau Infrastructure) is NOT STARTED, meaning the minimal tableau is
  architecturally incomplete compared to the classical and intuitionistic variants.

---

## Concern 9: Tableau Completeness Files Not Mentioned in Task 317
**Severity: NICE-TO-HAVE**

Task 317 is titled "Propositional Tableau Completeness" with dependency on 316. However, the
completeness sorries already exist in files that were partially created: `Classical/Completeness.lean`
(3 sorries), `Intuitionistic/Completeness.lean` (3 sorries). Task 317 should reference these
existing file stubs rather than implying completeness files need to be created from scratch.

---

## Summary Table

| Concern | Area | Severity | Blocker for Zulip Post? |
|---------|------|----------|------------------------|
| LK CutElim excluded from build | SC | CRITICAL | Yes — must clarify |
| 11 tableau sorries, Decidable instances are sorry-dependent | Tableau | IMPORTANT | Yes — must be accurate |
| No Tableau↔SC bridge planned | Tableau/SC | IMPORTANT | Should acknowledge |
| No minimal sequent calculus (LM) | SC | IMPORTANT | Should acknowledge |
| Conservative chain incomplete (CPL/IPL and task 311/312 pending) | Conservative | IMPORTANT | Yes — must not overclaim |
| LJ cut elimination sorry non-trivial | SC | IMPORTANT | Yes — must clarify |
| Decidability only sorry-free via Bool.lean fallback for classical | Tableau | IMPORTANT | Should note |
| Minimal has no standalone Soundness/Completeness files | Tableau | IMPORTANT | Should note |
| Tableau completeness files already partially exist | Tableau | NICE-TO-HAVE | No |

---

## Recommended Framing for Zulip Post

The honest framing is:

1. **Proof systems implemented**: Hilbert, ND, LK, LJ are all structurally complete with
   soundness, completeness, and equivalence bridges sorry-free for CPL (Hilbert/ND/LK) and
   IPL (Hilbert/ND/LJ). The three-way equivalences are formally proved.

2. **Structural properties**: LJ cut elimination is stated with one sorry in the core
   `cutAdmissibility` lemma. LK cut elimination is fully proved but currently excluded from
   the build due to unresolved build errors.

3. **Tableau**: The algorithm infrastructure is in place for all three logics (classical,
   intuitionistic, minimal). Soundness and completeness proofs are in progress (11 sorries
   across 5 files). The `Decidable (IValid φ)` and `Decidable (MValid φ)` instances are the
   primary novel contributions — these depend on completing the sorry proofs.

4. **Conservative extensions**: IPL conservative over MPL, over IPL⟨∧,→,⊤⟩, and over
   IPL⟨∧,→,⊥,⊤⟩ are formally proved. The deeper result (IPL conservative over IPL⟨→,⊤⟩)
   awaits the Diego embedding theorem (task 310, in progress). CPL/IPL is connected via
   Glivenko (not full conservativity). The unified chain module is planned for task 312.

5. **Minimal logic gap**: MPL currently has Hilbert ↔ ND equivalence and tableau infrastructure
   but no sequent calculus (LM). This is a known gap and a future direction.
