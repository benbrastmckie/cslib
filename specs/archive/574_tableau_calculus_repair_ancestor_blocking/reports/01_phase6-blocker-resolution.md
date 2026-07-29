# Research Report: Phase 6 Blocker Resolution — Ancestor-Blocking Witness Admissibility

- **Task**: 574 - tableau_calculus_repair_ancestor_blocking
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Date**: 2026-07-28
- **Agent**: cslib-research-hard-agent (H2 anti-analysis, H3 reference grounding, H4 adversarial
  self-verification)
- **Focus**: blocker research — Phase 6 (`intExpandBranches_openBranch_sat` reuse-site discharge)
- **Inputs read**:
  - `specs/574_tableau_calculus_repair_ancestor_blocking/.orchestrator-handoff.json` (`blockers[0]`)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/plans/01_tableau-repair-ancestor-blocking.md`
    (Overview, Goals & Non-Goals, Phases 5-8)
  - Live source: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`,
    `Expansion.lean`, `Rules.lean`
- **Live evidence artifacts** (produced by this dispatch, not committed to `Cslib/`):
  - `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/phase6-prototype.patch`
    (92 changed lines in `Scheme.lean`; 241-line unified diff)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/Scheme.lean.prototype`
    (full prototype file)
  - `specs/574_tableau_calculus_repair_ancestor_blocking/scratch/Scheme.lean.baseline`
    (Phase 5 end state, restored into `Cslib/` at dispatch end)

---

## Executive Verdict

**Remedy (b) is the provable one — and it is provable in a form that makes remedy (a)'s entire
Phase 5 quotient stack unnecessary.**

The blocker record's remedy (b) ("a companion invariant threading blocking events through the
induction as they happen, instead of post-hoc reconstruction via `intBlockRep` on the final
branch") is correct in principle. Its concrete realization is *not* another `rep`-function
predicate stack. It is:

> **Thread a second, invariant-side edge list (`augSets`) alongside the algorithm's own
> `edgeSets`, and record each blocking event as an explicit loop-back edge `(x, l)` in that list
> at the moment it happens.**

This works because `intExpandBranches_openBranch_sat`'s conclusion **existentially quantifies
`edges`**:

```lean
∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b
```

The lemma is therefore free to return an edge list that is *not* the one the algorithm
accumulated. Nothing in `intExpandBranches`, `Soundness.lean`, or the acceptance gate observes
that list. The whole "which `rep` do I use, and how do I compute the final branch's `rep` during
a forward induction?" problem — the actual obstruction behind both the reuse-site and the
`none`-leaf failures — simply does not arise, because the invariant's accessibility relation is
constructed forward, in lockstep with the induction, rather than reconstructed backward from the
final branch.

**The literature independently confirms this mechanism and refutes the alternative.** Garg,
Genovese & Negri (LICS 2012) — the very source the repo's `Sfor` naming and its
`intFImpReuseWitnessAnc?` docstring cite — construct their countermodel as `M ∪ C` with
`C = {x ≤ y | Sfor(x) ⊆ Sfor(y)}`, i.e. **by adding loop-back edges**, and state in their related
work that they "have not been able to find a suitable filtration on the obvious model whose worlds
are equivalence classes of ⪯ ∩ ⪰". Chagrov & Zakharyaschev independently warn that a filtration
relation in the `S̲ ⊆ S ⊆ S̄` interval "may be nontransitive even if the original R is
transitive" and that "not all S in this interval give rise to filtrations of intuitionistic
models" — which is exactly the assumption `intAccessPreorderQ`'s pullback design rests on. See
§"Source-to-Implementation Mapping" for verbatim quotes and provenance tiers.

**Status: verified end-to-end against the live tree, not argued.** A full prototype was
implemented, `lake build` (3,309 jobs) is green, the Phase-4 temporary `sorry` is **closed**, and
the repo-wide bare-`sorry` count is back to **exactly the 6-entry baseline**. See
§"Adversarial Self-Verification" for the falsification test and the claim table.

A second, independent defect in Phase 5.1's landed `intBlockRep` machinery was found in passing
(§"Secondary Defect"); it is a further reason remedy (a) cannot be rescued by reshaping
`sfSatisfiedQ` alone.

---

## Findings

### Source-to-Implementation Mapping (H3, Tier 1)

**Headline literature result: the published `Sfor`-containment method the repo's blocking check
is named after builds its countermodel by ADDING LOOP-BACK EDGES, not by quotienting — and its
authors explicitly report they could not make a filtration work.** This is the design the fix
recommended here implements, and it directly contradicts the plan's Phase 5 quotient premise.

| Source claim | BibKey (`references.bib` line) | Availability | Lean target | Translation note |
|---|---|---|---|---|
| **Countermodel of a saturated history** (Def. III.4): "The relations of CM(Σ;M;Γ;∆) are **M ∪ C, where C = {x ≤ y \| x ⪯ y}**", with `x ⪯ y iff Sfor(x) ⊆ Sfor(y)`; §III overview: "we can obtain a countermodel … **by adding an edge x ≤ y whenever Sfor(x) ⊆ Sfor(y)**" | `GargGenoveseNegri2012` (`:228`) | **Not in local corpus — web-verified** (`people.mpi-sws.org/~dg/papers/lics12.pdf`) | `augSets`: the invariant-side edge list, `augH ++ [(x, l)]` at each block | Direct match. GGN add an edge for **every** `⪯`-pair; the fix adds only the **triggering** pair, a strictly smaller relation — sufficient because the repo's Option-A `F(ψ)@x` conjunct makes the witness carry the obligation explicitly (see below). |
| GGN related work: "**we have not been able to find a suitable filtration on the obvious model whose worlds are equivalence classes of ⪯ ∩ ⪰. In particular, it seems extremely difficult to satisfy the 'back condition' of a filtration.**" | `GargGenoveseNegri2012` (`:228`) | web-verified | — (refutes the Phase 5 design) | The authors of the exact technique the repo cites report the quotient route as the one that does **not** work. |
| GGN Lemma III.5: the valuation `h` must be **separately proved monotone** w.r.t. the enlarged `≤` | `GargGenoveseNegri2012` (`:228`) | web-verified | Residual Risk **R1** | Confirms R1 is a real, named obligation of this design — not an artefact of the Lean encoding. |
| GGN Lemma III.6 / Cor. III.7: truth lemma proved "by lexicographic induction, first on φ, and then on the **partial (tree-like) order ⊑ of M**" — i.e. on the ORIGINAL tree order, not the enlarged relation | `GargGenoveseNegri2012` (`:228`) | web-verified | forward guidance for `truthLemma`'s T-imp `sorry` (Gap 1, out of scope) | `truthLemma` currently inducts on the formula alone. Any future attempt at the T-imp case must add the tree-order component or the induction is not well-founded. **Record in the revised plan.** |
| Filtration def. (§5.3, p. 141), conditions (i)-(iv′); **(iv′) intuitionistic back condition**: "if [x]S[y] then y ⊨ φ whenever x ⊨ φ, for all φ ∈ Σ"; Theorem 5.23 | `ChagrovZakharyaschev1997` (`:75`) | **In local corpus**, `chunk_0245.md`/`chunk_0246.md` | — | The coarsest intuitionistic filtration `S̄ = {([x],[y]) : ∀φ ∈ Σ (x ⊨ φ → y ⊨ φ)}` is *literally* `Sfor`-containment. GGN's `C` is its syntactic image asserted as edges rather than as a relation on classes. The two designs are duals. |
| CZ p. 141 warning: "**a relation S between S̲ and S̄ may be nontransitive even if the original R is transitive**, in particular, **not all S in this interval give rise to filtrations of intuitionistic models**" | `ChagrovZakharyaschev1997` (`:75`) | in corpus, `chunk_0246.md` | — (independent warning against Phase 5.2) | `intAccessPreorderQ` was built as a `rep`-pullback of `intAccessPreorder` on the assumption that "pulling back the closure suffices without re-deriving transitivity" (its docstring). CZ says that assumption is exactly the one that fails for intuitionistic models. |
| CZ §5.5 selective filtration (Lemma 5.45/Thm 5.46 GL; Lemma 5.50/Thm 5.51/Cor 5.52 Grz): never blocks — *selects* a witness guaranteed non-Σ-equivalent to any ancestor | `ChagrovZakharyaschev1997` (`:75`) | in corpus, `chunk_0261`-`chunk_0268` | not applicable | Requires a Lemma-5.50-style selection guarantee the repo's calculus does not supply. Recorded so a future dispatch does not chase it. |
| Def. 8.1 (**per-world** "copy": σ,σ′ agree on *every* formula) vs Def. 8.2 (**per-obligation** "modal copy": for each unreduced `σ : ¬□A` there is a shorter modal copy σ′ with `σ′ : ¬□A` reduced); footnote: extends to K4/S4 but **fails for KB and B** | Massacci 2000, *Single Step Tableaux for Modal Logics*, JAR 24:319-364 | **In local corpus** (`massacci_2000_single_step_tableaux_for_modal_logics`, `chunk_0025`/`chunk_0026`, pp. 336-337) — **no BibKey in `references.bib`** | `intFImpReuseWitnessAnc?`'s Option-A `F(ψ)@x` conjunct (`Expansion.lean:281`) | Answers the "same formula occurrence?" question: **both shapes exist and are not interchangeable across logics.** The repo's check is the **per-obligation** (Def. 8.2) shape — the stronger, safer one. |
| Loop-check blocking world is an **ancestor**; `T(φ→ψ)` splits at accessible worlds | `Fitting1983` (`:211`) Ch. 4 | **BibTeX key only — NOT navigable** | `intFImpReuseWitnessAnc?` ancestor direction | Provenance only, not verifiable from this repo. Massacci p. 336 cites "Fitting's tableaux [13, Chap. 8]" but attributes his own Technique 8.2 elsewhere, so Fitting's own invariant shape could not be established. |
| Contraction-free sequent calculi (LJT/G4ip) | `Dyckhoff1992` (`:218`) | BibTeX key only | not used by this fix | Termination there is a multiset ordering on the sequent, not ancestor blocking on worlds — likely the wrong citation for a loop-check invariant. |
| Structural proof theory | `NegriVonPlato2001` (`:931`) | **IS in the local corpus** (`negri_von_plato_2001`, 385 chunks) — the global index has no `bib_key` field for it, so `/cite` will not auto-link it | not used by this fix | See the corpus correction below. |

**Corpus-availability correction (H3).** The plan's H3 mapping table asserts that
`ChagrovZakharyaschev1997` is the **only** one of the five keys in the navigable corpus. **That
is false.** `NegriVonPlato2001` is present as `negri_von_plato_2001` (385 chunks, 7 per-chapter
children, `verified_conversion`); it is simply missing a `bib_key` field in the global index.
Also navigable and directly on-topic, though not among the five keys: `massacci_2000_…`,
`simpson_1994_intuitionisticmodallogic`,
`marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal`,
`blackburn_2002_book`, `troelstra_schwichtenberg_2000`. **The revised plan should correct its
H3 table and consider adding a Massacci 2000 BibKey**, since Massacci Def. 8.1/8.2 is the
sharpest locally-readable statement of the per-world/per-obligation distinction this task turns
on.

### Why the repo needs *less* machinery than GGN

GGN's blocking condition is the **per-world** fact `Sfor(x) ⊆ Sfor(y)` alone (Def. III.3 clauses
10b/12b). Because the witness is not required to carry the blocked obligation, GGN must transport
it there — which is what forces the added edge plus the Lemma III.5 monotonicity proof plus the
Lemma III.6 truth lemma.

The repo's `intFImpReuseWitnessAnc?` additionally requires the **Option-A** conjunct
`F(ψ)@x ∈ bPers` (`Expansion.lean:281`) — the Massacci Def. 8.2 shape. The witness therefore
carries the obligation's `T(φ)`/`F(ψ)` entries **explicitly, on the branch**. That is precisely
why the reuse-site discharge in §9 below is ~20 lines of direct term construction rather than an
appeal to a `Sfor`-transport lemma: `houtPhi` and `hFpsi` *are* the needed facts. Retaining that
conjunct (plan decision D4) is what makes this fix cheap.

All five BibKeys were confirmed present in `references.bib` at the lines above. No new
`references.bib` entry is required for the fix itself.

**H3 honesty note.** Three evidence tiers are used and kept distinct: (1) **locally verified** —
`ChagrovZakharyaschev1997`, Massacci 2000 (chunk-level quotes); (2) **web-verified** —
`GargGenoveseNegri2012` (PDF fetched at the URL above, quoted verbatim, but *not* in this repo's
corpus); (3) **provenance only** — `Fitting1983`, `Dyckhoff1992`. The recommendation's decisive
evidence remains the live Lean verification in §"Adversarial Self-Verification"; the literature
independently corroborates the mechanism and, importantly, refutes the alternative.

### Why the plain-to-Q lifting really fails (confirming the blocker record)

The blocker record's root-cause analysis is **correct and is confirmed**. Restated in the terms
the fix uses:

`intBlockRep b edges` is a function of the **final** branch and the **final** edge list. The
induction in `intExpandBranches_openBranch_sat` runs **forward**: at every step it holds
`IExpandedConsistent bPers eH` and `IExpandedAccessConsistent edgesH bPers eH` for the
*intermediate* `bPers`/`edgesH`. Any invariant phrased over `intBlockRep b_final edges_final`
cannot be established at an intermediate step without knowing the future, and
`intBlockRep` is **not monotone** under branch growth (adding formulas changes `negImpAt`'s
`findSome?` result and changes `posFormulasAt`, so blocking can appear, disappear, or retarget).
The blocker record's counterexample pattern is one instance of this general non-monotonicity.

Reshaping the ordering conjunct — remedy (a), replacing raw `Nat.le` on representatives with
`intAccessPreorderQ` — does **not** address this. It changes *which relation* the conjunct
asserts; it does not make `rep` computable during the induction, and it does not make `rep`
monotone. The blocker record already reached this conclusion from the witness-content angle
("the alternate ancestor was chosen to discharge a different signed formula"); the
forward/backward mismatch is the same obstruction seen structurally.

### The fix, and why it is sound

At the reuse site the proof holds, from `intFImpReuseWitnessAnc?_spec`:

- `hcont` : `Sfor(w') ⊆ posFormulasAt bPers x`, where `Sfor(w') = {φ} ∪ posFormulasAt bPers l`
- `hFpsi` : `F(ψ₀)@x ∈ bPers` (the load-bearing Option-A conjunct)
- `houtPhi` : `T(φ)@x ∈ bPers` (already derived at `Scheme.lean:3118-3138` from `hcont`)
- `hacc`/`hle` : `isAccessible edgesH x l`, `x ≤ l` — the **wrong direction** for both
  `sfSatisfied` and `sfAccessSat`

The obligation `F(φ→ψ₀)@l` needs a witness *above* `l`. The witness `x` is *below* `l`. The
model must therefore make `l ⊑ x`. Combined with the real edge path `x ⇝ l`, this makes `x` and
`l` preorder-equivalent — which is exactly what `Sfor`-containment licences: `hcont` gives
`posFormulasAt bPers l ⊆ posFormulasAt bPers x`, and ancestor persistence gives the converse
inclusion, so the two worlds force the same positive formulas. Intuitionistic Kripke semantics
requires only a **preorder** (`IForces` in `Cslib/Logics/Propositional/Semantics/Kripke.lean:81`
is defined over `[Preorder World]`, with no antisymmetry), so a cycle is admissible; it is a
one-point class after quotienting.

The fix realises `l ⊑ x` by adding the edge `(x, l)` to the invariant-side list. `isAccessible`
stores edges as `(child, parent)` and `isAccessible_one_step (hmem : (w', w) ∈ edges) :
isAccessible edges w w' = true` (`Scheme.lean:349`), so `(x, l) ∈ aug` yields
`isAccessible aug l x` in one hop — exactly `sfAccessSat`'s conjunct with `w' := x`.

### The `sat_fimp` numeric conjunct is dead and must be dropped

Independently of the above, `sfSatisfied`'s `.neg,.imp` clause and `IBranchSaturation.sat_fimp`
carry an ordering conjunct `sf.label ≤ w'` / `w ≤ w'` on **raw `Nat` labels**. Under
ancestor-directed blocking this is *false*: `x < l`. Under descendant-directed creation it was
true only because labels increase monotonically — a numeric proxy for accessibility, which the
file's own docstrings say explicitly (`Scheme.lean:72`, `:482`, `:753`).

**Verified**: `IBranchSaturation.sat_fimp` is *produced* (`IExpandedConsistent_sat`,
`Scheme.lean:1308-1319`) but **never consumed**. `truthLemma`'s F-imp case (`Scheme.lean:794-801`)
reads its witness from `hfimp : IFimpAccess edges b`, not from `hsat.sat_fimp`; no other
occurrence of `.sat_fimp` exists in `Cslib/`. The only external mentions of `IBranchSaturation`
are the two hypothesis positions `Intuitionistic/Completeness.lean:76` and
`Minimal/Completeness.lean:80`, both of which are *weakened* (hence still satisfiable) by the
change. Full `lake build` green confirms this.

Removing the conjunct is a **correction**, not a weakening-to-avoid-work: the genuine content
(the witness is accessible) is carried, in strictly stronger form, by `IFimpAccess`.

### Secondary Defect (independent of the fix; found while evaluating remedy (a))

**Claim**: `intBlockRepStep` (`Scheme.lean:547-559`, Phase 5.1) does **not** agree with
`intFImpReuseWitnessAnc?` "by construction", contrary to its docstring (`Scheme.lean:540-546`).

- **Counterexample pattern**: `intBlockRepStep` tests only
  `(posFormulasAt b x).contains φψ.1` — containment of the *single* formula `φ`. The
  expansion-time check `intFImpReuseWitnessAnc?` (`Expansion.lean:279`) tests
  `sfor.all ((posFormulasAt bPers x).contains ·)` where `sfor = {φ} ∪ posFormulasAt bPers w` —
  containment of the *whole* forced set. Any branch with a world `w` and ancestor `x` where
  `φ ∈ posFormulasAt b x` but `posFormulasAt b w ⊄ posFormulasAt b x` makes `intBlockRepStep`
  fire on a world that expansion never blocked. Additionally, `negImpAt b w`
  (`Scheme.lean:526-533`) uses `List.findSome?`, silently selecting only the *first*
  `.neg`-signed implication at `w`; a world carrying two `F(·→·)` obligations has the other one
  ignored.
- **Current behaviour**: `intBlockRep` may identify worlds that were never blocked, and may miss
  worlds that were.
- **Required behaviour**: to justify the docstring, the test would have to replay the full
  `sfor.all` containment against `posFormulasAt b w`, and quantify over all `.neg`-implications
  at `w`, not `findSome?` one.
- **Isolation**: `Scheme.lean:526-559` (`negImpAt`, `intBlockRepStep`) and the docstring claim at
  `:540-546`.

This defect does not affect the recommended fix (which deletes this machinery). It is recorded
because it is a second, independent reason remedy (a) is not rescuable by editing `sfSatisfiedQ`
alone: even a perfectly-shaped `sfSatisfiedQ` would be instantiated at a `rep` that does not
mean what its docstring says.

---

## Recommended Remedy: Exact Revised Declaration Shapes

All shapes below are the **verified prototype**, transcribed from
`scratch/Scheme.lean.prototype`. Line references are to the Phase 5 end state.

### 1. `sfSatisfied` — drop the numeric ordering conjunct (`Scheme.lean:962-965`)

```lean
  | .neg, .imp φ ψ =>
    ∃ w' : Nat,
      b.any (fun x => x.sign == .pos && x.formula == φ && x.label == w') = true ∧
      b.any (fun x => x.sign == .neg && x.formula == ψ && x.label == w') = true
```

### 2. `IBranchSaturation.sat_fimp` — same (`Scheme.lean:97-101`)

```lean
  sat_fimp : ∀ (φ ψ : Proposition Atom) (w : Nat),
      b.any (fun sf => sf.sign == .neg && sf.formula == .imp φ ψ && sf.label == w) = true →
      ∃ (w' : Nat),
        b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w') = true ∧
        b.any (fun sf => sf.sign == .neg && sf.formula == ψ && sf.label == w') = true
```

### 3. `sfSatisfied_mono` — arity of the `.neg,.imp` arm (`Scheme.lean:1000-1001`)

```lean
    | (obtain ⟨w', h1, h2⟩ := h
       exact ⟨w', any_mono_sub hmono h1, any_mono_sub hmono h2⟩)
```

### 4. `intStepBranch_linear_preserves` — drop `hsfl` from the fresh-world witness (`:1563`)

```lean
          refine ⟨nw, List.any_eq_true.mpr ⟨⟨.pos, φ, nw⟩, hmemNew _ ?_, by simp⟩,
                  List.any_eq_true.mpr ⟨⟨.neg, ψ, nw⟩, hmemNew _ ?_, by simp⟩⟩ <;>
```

*(No other change to this lemma. It is already fully parametric in `edges`, so instantiating it
at the augmented list requires no edit — verified.)*

### 5. `intExpandBranches_openBranch_sat` — the augmented-edge parameter (`:2930-2942`)

```lean
private lemma intExpandBranches_openBranch_sat (fuel : Nat)
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (edgeSets : List IEdges)
    (augSets : List IEdges)          -- NEW: invariant-side edge lists
    (closurePred : IBranch Atom → Bool)
    (b : IBranch Atom)
    (hAC : IAllConsistent branches expandedSets nextWorlds)
    (hLen0 : branches.length = edgeSets.length)
    (hACC : IAllAccessConsistent branches expandedSets augSets)   -- CHANGED: augSets
    (h : intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred
        = .openBranch b) :
    ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b := by
  induction fuel generalizing branches expandedSets nextWorlds edgeSets augSets hAC hLen0 hACC with
```

No length hypothesis is needed for `augSets`: `IAllAccessConsistent` is `False` on
mismatched-length lists, so the shape is forced.

### 6. The inner `suffices key` — two extra list parameters

```lean
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (pendingAug : List IEdges)          -- NEW
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges)
        (doneAug : List IEdges),            -- NEW
        IAllConsistent pending pendingExp pendingNW →
        pending.length = pendingEdges.length →
        IAllConsistent done doneExp doneNW →
        done.length = doneEdges.length →
        IAllAccessConsistent pending pendingExp pendingAug →   -- CHANGED
        IAllAccessConsistent done doneExp doneAug →            -- CHANGED
        intExpandBranches.go closurePred fuel' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .openBranch b →
        ∃ edges : IEdges, IBranchSaturation Atom b ∧ IFimpAccess edges b from
      key branches expandedSets nextWorlds edgeSets augSets [] [] [] [] []
        hAC hLen0 (by trivial) rfl hACC (by trivial) h
```

Note `intExpandBranches.go`'s argument list is **unchanged** — the algorithm still threads its own
`pendingEdges`/`doneEdges`. This decoupling is the whole mechanism.

### 7. New case split on `pendingAug`, nested inside the `pendingEdges` cons case

```lean
          | cons edgesH edgesT =>
           cases hpAug : pendingAug with
           | nil =>
             simp only [hpE, hpAug, IAllAccessConsistent] at hPendingACC
           | cons augH augT =>
            ...
            simp only [hpE, hpAug, IAllAccessConsistent] at hPendingACC   -- was hpEdges
            ...
            have hACC_bPers : IExpandedAccessConsistent augH bPers eH :=   -- was edgesH
              IExpandedAccessConsistent_mono
                (fun x hx => applyPersistenceFixpoint_mem_preserved bh edgesH (fuel' + 1) x hx)
                hACC_bh_eH
```

### 8. The `none` leaf — return the augmented list

```lean
                exact ⟨augH, IExpandedConsistent_sat hstep hIC_bPers,
                  IExpandedAccessConsistent_sat hstep hACC_bPers⟩
```

Both extraction lemmas are used **unchanged**; only the edge list they are instantiated at
differs. This is the "one-line substitution" the original Phase 6 task list anticipated — it just
needed the right list, not a Q-predicate.

### 9. **The reuse-site discharge** — the site that was `sorry` (`:3131-3143`)

```lean
                           have hreuse_sat : IExpandedConsistent bPers newExp ∧
                               IExpandedAccessConsistent (augH ++ [(x, l)]) bPers newExp := by
                             subst hnewExp
                             constructor
                             · intro sf' hsf'
                               rcases List.mem_append.mp hsf' with h' | h'
                               · exact hIC_bPers sf' h'
                               · rw [List.mem_singleton] at h'
                                 subst h'
                                 show sfSatisfied bPers ⟨.neg, .imp φ ψ₀, l⟩
                                 simp only [sfSatisfied]
                                 exact ⟨x, houtPhi, hFpsi⟩
                             · intro sf' hsf'
                               rcases List.mem_append.mp hsf' with h' | h'
                               · exact sfAccessSat_edges_mono (x, l) (hACC_bPers sf' h')
                               · rw [List.mem_singleton] at h'
                                 subst h'
                                 show sfAccessSat (augH ++ [(x, l)]) bPers
                                   ⟨.neg, .imp φ ψ₀, l⟩
                                 simp only [sfAccessSat]
                                 exact ⟨x, isAccessible_one_step (by simp), houtPhi, hFpsi⟩
```

followed by

```lean
                           have hACC'' : IAllAccessConsistent (done ++ [bPers] ++ bt)
                               (doneExp ++ [newExp] ++ eT)
                               (doneAug ++ [augH ++ [(x, l)]] ++ augT) := ...
                           exact ih _ _ _ _ _ hAC'' hLen0'' hACC'' hgo)
```

`hLen0''` is **unchanged** (it still speaks about `doneEdges`/`edgesT`, matching `hgo`).

### 10. `linearResult` and `branchingResult` arms — mechanical

`doneEdges ++ [newEdge.elim edgesH (fun e => edgesH ++ [e])] ++ edgesT`
→ `doneAug ++ [newEdge.elim augH (fun e => augH ++ [e])] ++ augT`;
`branches'.map (fun _ => edgesH)` → `branches'.map (fun _ => augH)`; each `exact ih _ _ _ _ …`
gains one `_`.

### 11. `openBranch_countermodel` — one extra argument (`:3367-3370`)

```lean
  obtain ⟨edges, hsat, hfimp⟩ :=
    intExpandBranches_openBranch_sat _ _ _ _ _ [[]] _ _
      (by simp [IAllConsistent, IExpandedConsistent, ILabelBound]) rfl
      (by simp [IAllAccessConsistent, IExpandedAccessConsistent]) h
```

The explicit `[[]]` is needed because `augSets` is otherwise unconstrained by unification.

---

## Phase 5.3 / 5.4 Dependents: Re-Verification and Expected Breakage

| Declaration | Landed in | Fate under the recommended fix | Expected breakage |
|---|---|---|---|
| `sfSatisfiedQ` (`:1095`) | 5.3 | **Delete** — no longer referenced | none (private, unused) |
| `IExpandedConsistentQ` (`:1120`) | 5.3 | **Delete** | none |
| `sfSatisfiedQ_mono` (`:1128`) | 5.3 | **Delete** | none |
| `IExpandedConsistentQ_mono` (`:1144`) | 5.3 | **Delete** | none |
| `sfAccessSatQ` (`:1152`) | 5.3 | **Delete** | none |
| `IExpandedAccessConsistentQ` (`:1163`) | 5.3 | **Delete** | none |
| `IBranchSaturationQ` (`:1175`) | 5.4 | **Delete** — public `structure`; `grep` shows zero external references | none |
| `IFimpAccessQ` (`:1215`) | 5.4 | **Delete** — public `def`; zero external references | none |
| `IExpandedConsistentQ_sat` (`:1340`) | 5.4 | **Delete** | none |
| `IExpandedAccessConsistentQ_sat` (`:1896`) | 5.4 | **Delete** | none |
| `intBlockRep`/`intBlockRepStep`/`negImpAt` + 4 lemmas (`:526-643`) | 5.1 | **Delete** — and see §"Secondary Defect": their docstring claim is false as landed | none |
| `intAccessPreorderQ` + 2 lemmas (`:654-678`) | 5.2 | **Delete** | none |
| **`sfSatisfied` `.neg,.imp`** (`:962`) | pre-existing | **Amend** (drop `sf.label ≤ w'`) | forces edits 3 and 4 below |
| **`IBranchSaturation.sat_fimp`** (`:97`) | pre-existing | **Amend** (drop `w ≤ w'`) | none downstream — verified never consumed |
| `sfSatisfied_mono` (`:989`) | pre-existing | **Amend** — `.neg,.imp` arm arity | fails to elaborate otherwise |
| `intStepBranch_linear_preserves` (`:1473`) | pre-existing | **Amend** — one `refine` arity (`:1563`) | fails to elaborate otherwise |
| `IExpandedConsistent_sat` (`:1249`) | pre-existing | **unchanged** — `exact hsat` still closes `sat_fimp` (definitional identity preserved) | none — verified green |
| `IExpandedAccessConsistent_sat` (`:1873`) | pre-existing | **unchanged** | none |
| `truthLemma` (`:756`) | pre-existing | **unchanged** — F-imp case stays green over `IFimpAccess`; T-imp `sorry` untouched | none — verified green |
| `Intuitionistic/Completeness.lean:76-77`, `Minimal/Completeness.lean:80-81` | pre-existing | **unchanged** — hypotheses only weaken | none — verified green in full build |
| `Soundness.lean` (all) | pre-existing | **untouched** | `grep -c sorry` = 0, `grep -c IBranchSaturation` = 0 — verified after prototype |

**Net accounting**: ~480 lines of Phase 5 output (4 green commits b70eadc0, 1a1eba9f, a9eb2e47,
07ab747c) become dead code and should be deleted. The replacement is ~92 changed lines in
`Scheme.lean`. This is a **preserved-assets loss** and must be stated as such in any revision —
Phase 5 is not salvaged, it is superseded.

---

## Step-Ordered Fix Path for the Re-Dispatched Phase 6

Each step is independently `lake build`-checkable. Steps 1-3 are red-until-step-3 (the
`sfSatisfied` arity change breaks two proofs); declare them as one **atomic-batch** objective.

| # | Step | Verification |
|---|---|---|
| **1** | Amend `sfSatisfied`'s `.neg,.imp` clause (`:962-965`): drop `sf.label ≤ w' ∧`. | (red) |
| **2** | Amend `IBranchSaturation.sat_fimp` (`:97-101`): drop `w ≤ w' ∧`. Update its doc comment and the `sat_fimp` note at `:72-73`. | (red) |
| **3** | Repair the two arity fallouts: `sfSatisfied_mono`'s `.neg,.imp` arm (`:1000-1001`), `intStepBranch_linear_preserves`'s `refine` (`:1563`). | `lake build …Scheme` **green** — commit `task 574 phase 6.1: retire the sat_fimp numeric proxy` |
| **4** | Add `augSets` to `intExpandBranches_openBranch_sat`'s signature and to `generalizing`; change `hACC`'s type to use `augSets`. | (red) |
| **5** | Add `pendingAug`/`doneAug` to `suffices key`, its two `IAllAccessConsistent` hypotheses, the `key …` application, and the `nil` branch's `intro` arity (13 → 15 underscores). | (red) |
| **6** | Add the `cases hpAug : pendingAug` split; retarget `hACC_bPers` to `augH`; thread `augT`/`doneAug ++ [augH]` through the `closurePred` recursion. | (red) |
| **7** | `none` leaf: `⟨edgesH, …⟩` → `⟨augH, …⟩`. `linearResult`/`branchingResult` arms: swap `edgesH`→`augH`, `edgesT`→`augT`, `doneEdges`→`doneAug` **in `hACC'` only** (leave `hLen0'` and `hgo` on the algorithm's lists); add one `_` to each `exact ih …`. | (red) |
| **8** | Update `openBranch_countermodel`'s call site with the explicit `[[]]`. | `lake build …Scheme` **green, with the reuse-site `sorry` still present** — commit `task 574 phase 6.2: thread the invariant-side edge list` |
| **9** | **Replace the reuse-site `sorry` with the discharge in §9 above**, and retype `hACC_reuse`/`hACC''` to `augH ++ [(x, l)]`. | `lake build` (full) **green**; `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean \| wc -l` = **6** — commit `task 574 phase 6.3: close the reuse-site discharge` |
| **10** | Delete the Phase 5 Q-stack and the `intBlockRep` machinery (12 declarations, ~480 lines) plus their section headers; rewrite the D5 design note at `:1009-1030` and the `intBlockRepStep`/`intBlockRep` docstrings' claims. | `lake build` (full) green; `grep -rn "Q\b" `-style sweep for orphan references — commit `task 574 phase 6.4: retire the superseded quotient stack` |
| **11** | Gates: `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` → `{propext, Classical.choice, Quot.sound}`; `grep -c sorry Soundness.lean` = 0; `grep -c IBranchSaturation Soundness.lean` = 0. | all verified in this dispatch's prototype |

**Not in this phase**: `lake lint`, `lake exe lint-style`, `lake shake` — those are Phase 8's gate
and were **not** run by this research dispatch (see Residual Risks).

---

## Does the Plan Need Formal Revision?

**Yes — `/revise` is required. This does not fit inside a Phase 6 re-dispatch.**

Four independent reasons:

1. **A stated plan Goal is contradicted.** `## Goals & Non-Goals` lists as a Goal: *"Restate the
   branch-saturation predicate stack … over a **blocking-quotient frame**, and rewrite
   `truthLemma` to read its F-imp witness off the quotient."* The recommended fix achieves the
   same *objective* (make the ancestor witness admissible) by a different *mechanism* and
   **abandons the quotient frame entirely**. Under `.claude/rules/plan-compliance.md`, a
   mechanism substitution on a `.lean` file must be raised as a blocker, not annotated post hoc.

2. **Phase 5's deliverable is superseded, not amended.** ~480 lines across four committed
   sub-phases become dead code. A Phase 6 re-dispatch has no authority to delete a `[COMPLETED]`
   phase's output; the Preserved-Assets accounting has to be rewritten.

3. **Phase 7 collapses.** Its entire 7.1 (migrate `truthLemma` to `IBranchSaturationQ`/
   `IFimpAccessQ`/`intAccessPreorderQ`) and most of 7.2 (migrate `openBranch_countermodel`,
   `tableau_complete`, both `Completeness.lean` signatures) become no-ops — `truthLemma`'s F-imp
   case is already green over `IFimpAccess` and stays that way. Phase 7's remaining content is
   only the docstring rewrite and the optional dead-code deletion, which step 10 above already
   absorbs into Phase 6.

4. **The plan's H3 source mapping is factually wrong in two places**, and H3 tables are part of
   the plan's contract: (i) it claims `ChagrovZakharyaschev1997` is the only navigable key —
   `NegriVonPlato2001` is in the corpus too (see §"Corpus-availability correction"); (ii) it
   attributes the `Sfor`-containment design to `GargGenoveseNegri2012` as "design rationale, not
   a checkable citation", when that source in fact **specifies a different countermodel
   construction from the one Phase 5 built** and explicitly reports the quotient route as
   unworkable. A revision must correct both.

**Suggested revised shape** (for the `/revise` dispatch to consider, not a decision this report
makes):

- **Phase 5 → `[SUPERSEDED]`**, with the four commits kept in history and the declarations
  deleted in the new Phase 6.
- **New Phase 6** = steps 1-11 above, four green sub-commits (6.1-6.4). Sized at ~92 lines of
  amendment + ~480 lines of deletion — within one agent run per sub-step.
- **Phase 7 → deleted or reduced** to "docstring reconciliation + confirm zero orphan
  references"; its `Depends on: 6` and Phase 8's `Depends on: 2, 7` need re-pointing.
- **Goals section**: replace the "blocking-quotient frame" goal with "make the ancestor witness
  admissible by recording each blocking event as a loop-back edge in the saturation invariant's
  own accessibility relation, exploiting `intExpandBranches_openBranch_sat`'s existential
  `edges`".
- **Non-Goals**: add "closing `truthLemma`'s T-imp `sorry`" and "the `intExtractValuation`
  monotonicity bridge" explicitly against the *enlarged* preorder (see Residual Risk R1), with a
  pointer to GGN Lemma III.5 (the same obligation, named) and GGN Lemma III.6 (any future T-imp
  attempt needs a **lexicographic induction on (formula, original tree order ⊑)** — `truthLemma`
  currently inducts on the formula alone).
- **H3 table**: correct the two errors listed in reason 4 above; consider adding a Massacci 2000
  BibKey (locally navigable, and Def. 8.1 vs 8.2 is the sharpest readable statement of the
  per-world/per-obligation distinction this task turns on).

---

## Residual Risks

**R1 (highest, but not a regression).** The enriched preorder `intAccessPreorder aug` contains
`l ⊑ x`. `tableau_complete`'s docstring (`:3388-3394`) defers an *upward-closure of
`intExtractValuation b`* obligation to `hvalid`'s callers — i.e. to the two open `sorry`s at
`Intuitionistic/Completeness.lean:133` and `Minimal/Completeness.lean:125`. Along the loop-back
edge that obligation reads: every atom positive at `l` on the **final** branch `b` must be
positive at `x`. `hcont` establishes exactly this on `bPers`, the branch at *block time*, not on
`b`. Later growth at `l` is not propagated to `x` (the algorithm does not know about the
back-edge).

*Literature status*: this is **GGN Lemma III.5** — a named, separately-proved obligation of the
add-an-edge design ("the valuation `h` is still monotone w.r.t. the enlarged `≤`"). It is
expected, not a surprise, and it is the price of the design that works. CZ's filtration gets the
valuation condition for free (condition (ii), quotient image on variables in Σ) — but CZ's
filtration is the route GGN report as unworkable here.

*Why this is not a differentiator*: the `rep`-quotient design carries an **isomorphic**
obligation — identifying `l` with `x` requires the same valuation agreement on the final branch,
and `intBlockRep`'s post-hoc test (see §"Secondary Defect") establishes strictly *less* than
`hcont` does. *Why it is not avoidable*: any construction that discharges `F(φ→ψ)@l` with an
ancestor witness must place that witness above `l` in the model. *Containment*: the obligation
lives entirely in already-`sorry`ed declarations listed in the plan's Non-Goals; nothing in this
fix path touches them. **It must be written into the revised plan's Non-Goals with this analysis
attached, not left implicit.**

**R2.** `tableau_complete`'s public contract is **unchanged**: `hvalid` is already
`∀ (edges : IEdges) (b : IBranch Atom), IForces …` — universally quantified over *all* edge
lists, so an augmented list is already in scope. Verified by reading `:3402-3406`; no caller
obligation changes.

**R3.** `lake lint` / `lake exe lint-style` / `lake shake` were **not** run. Deleting 12 private
and 2 public declarations (step 10) may shift `shake`'s import minimisation. Phase 8 gate.

**R4.** `CslibTests/TableauConformance.lean` was not exercised. The fix is proof-side only — no
`intExpandBranches`, `intFImpRule`, or `intFImpReuseWitnessAnc?` behaviour changes — so
conformance verdicts cannot move. Still Phase 8's gate.

---

## Adversarial Self-Verification (H4)

Every load-bearing claim below was challenged and then checked against the live tree. The
prototype was built, verified, deliberately broken to prove non-vacuity, rebuilt, and reverted;
`git diff --stat Cslib/` is empty at dispatch end.

### Claim Verification Table

| # | Claim | Source / Counterexample / Evidence |
|---|---|---|
| C1 | The recommended fix discharges the **reuse site** (`Scheme.lean:3143`), removing its `sorry`. | **Live**: `lake build Cslib.…Scheme` green with the term in §9 in place. `grep -n "^\s*sorry\s*$"` on the prototype returns exactly `793` (truthLemma T-imp) and `2971` (fuel-0 base case) — the reuse-site `sorry` is gone. |
| C2 | The recommended fix discharges the **`none`-leaf extraction** (`:3049-3050`). | **Live**: same build. `IExpandedConsistent_sat`/`IExpandedAccessConsistent_sat` are applied **unmodified** at `⟨augH, …⟩`; no Q-lemma is used anywhere. |
| C3 | The reuse-site term is **genuinely elaborated**, not vacuously satisfied by a fallback branch of the `first \| … \| …` combinator. | **Falsification test**: swapping the two witness arguments (`houtPhi`↔`hFpsi`) produces `error: Scheme.lean:3159:76: Application type mismatch` and `build failed`. Restoring them rebuilds green. |
| C4 | Full repository build is green. | **Live**: `lake build` → `Build completed successfully (3309 jobs)`, zero `error:` lines. |
| C5 | The repo-wide bare-`sorry` count returns to **exactly** the plan's 6-entry baseline, with identical declaration identities. | **Live**: `grep -rn "^\s*sorry\s*$" Cslib/ --include=*.lean` → 6 lines: `TemporalConservativity:269`, `Scheme:793` (truthLemma T-imp), `Scheme:2971` (fuel-0), `Intuitionistic/Completeness:133`, `Minimal/Completeness:125`, `FrameSoundness:1276`. Matches the plan's Preserved-Assets table declaration-for-declaration. |
| C6 | The acceptance gate is untouched and axiom-clean. | **Live**: `lean_verify Cslib.Logic.PL.intExpandBranches_closed_unsat` → `{propext, Classical.choice, Quot.sound}`, zero warnings. `Soundness.lean`: `grep -c sorry` = 0, `grep -c IBranchSaturation` = 0. `git diff` touched **only** `Scheme.lean`. |
| C7 | `IBranchSaturation.sat_fimp`'s ordering conjunct is **never consumed**, so dropping it breaks nothing. | **Challenged**: could `Completeness.lean`/`Minimal/Completeness.lean` use it? **Checked**: `grep -rn "sat_fimp"` across `Cslib/` returns hits only inside `Scheme.lean`, all of them either docstrings or the two *producer* bullets (`:1308`, `:1398`). `truthLemma`'s F-imp case (`:794-801`) reads `hfimp`, not `hsat.sat_fimp`. **Confirmed by build**: C4 is green with the weakened structure and both `Completeness.lean` files unmodified. |
| C8 | `intStepBranch_linear_preserves` needs no edit-beyond-arity to work over the augmented list. | **Challenged**: does it assume `edges` is the algorithm's? **Checked**: `edges` is an implicit variable (`:1474`), used only via `sfAccessSat_edges_mono` and `isAccessible_one_step` on the appended edge (`:1578-1585`). **Confirmed by build**: instantiated at `augH` with no edit. |
| C9 | Recording the block as edge `(x, l)` (not `(l, x)`) is the correct orientation. | **Checked**: `isAccessible` (Rules.lean:92) walks `(child, parent)` pairs parent→child; `isAccessible_one_step (hmem : (w', w) ∈ edges) : isAccessible edges w w'` (Scheme.lean:349). So `(x, l) ∈ aug ⟹ isAccessible aug l x` — the direction `sfAccessSat` needs. **Confirmed by build** (a wrong orientation fails `isAccessible_one_step (by simp)`). |
| C10 | Remedy (a) (reshape `sfSatisfiedQ`'s conjunct via `intAccessPreorderQ`) cannot be made to work. | **Three independent grounds.** (i) *Structural*: `intBlockRep` is a function of the final `b`/`edges`; the induction is forward and `intBlockRep` is not monotone under branch growth (`negImpAt`'s `findSome?` and `posFormulasAt` both move). Changing which order the conjunct asserts does not make `rep` available mid-induction. (ii) *Defect*: `intBlockRepStep` (`:547-559`) tests only `(posFormulasAt b x).contains φψ.1`, where the expansion-time check tests the full `sfor.all` containment (`Expansion.lean:279`) — so `intBlockRep` does not model the algorithm's blocking, contrary to its docstring. (iii) *Literature*: GGN's related-work section reports the filtration-on-`⪯ ∩ ⪰`-classes route as the one they could not make work ("extremely difficult to satisfy the 'back condition'"), and CZ p. 141 warns the interval `S̲ ⊆ S ⊆ S̄` contains relations that are nontransitive and that "not all S in this interval give rise to filtrations of intuitionistic models" — a direct hit on `intAccessPreorderQ`'s pullback docstring claim. **Still not an exhaustive refutation**; (i)+(ii) are design/code arguments and (iii) is a negative result reported by others. Weaker evidence than C1-C9; stated at that confidence. |
| C14 | The fix's mechanism matches published practice for this exact technique. | **Web-verified** (GGN LICS 2012, `people.mpi-sws.org/~dg/papers/lics12.pdf`, Def. III.4 and §III overview, quoted verbatim in §"Source-to-Implementation Mapping"). **Challenged**: does GGN add *one* edge or *all* `⪯`-edges? **Checked**: all `⪯`-pairs. The fix adds only the triggering pair — a strictly smaller relation, which is *weaker* and therefore safe here, and is sufficient because the repo's Option-A `F(ψ)@x` conjunct (Massacci Def. 8.2 shape, locally verified) makes the witness carry the obligation explicitly. **Caveat**: GGN is not in this repo's corpus; this is web-sourced, not locally reproducible. |
| C15 | The plan's H3 availability claim ("only `ChagrovZakharyaschev1997` is navigable") is wrong. | **Locally verified**: `negri_von_plato_2001` is in the corpus (385 chunks, `verified_conversion`), missing only a `bib_key` field in the global index. Also navigable: `massacci_2000_…`, `simpson_1994_…`, `marinmoralesstrassburger_2021_…`, `blackburn_2002_book`, `troelstra_schwichtenberg_2000`. |
| C11 | The public contract of `tableau_complete` is unchanged by returning an augmented edge list. | **Checked**: `hvalid : ∀ (edges : IEdges) (b : IBranch Atom), @IForces … (intAccessPreorder edges) …` (`:3402-3406`) already quantifies over every `IEdges`. An augmented list is in its scope already. Caller obligation is textually identical. |
| C12 | Intuitionistic Kripke semantics here tolerates the cycle the loop-back edge creates. | **Checked**: `IForces` (`Cslib/Logics/Propositional/Semantics/Kripke.lean:81`) is `[Preorder World]` — no antisymmetry requirement. `intAccessPreorder` is a `Relation.ReflTransGen` closure, already a genuine preorder over any edge list. |
| C13 | The valuation-agreement fact that *justifies* `l ⊑ x` is actually available at the block site. | **Checked**: `intFImpReuseWitnessAnc?_spec`'s third conjunct `hcont` is `sfor.all ((posFormulasAt bPers x).contains ·)` with `sfor = {φ} ∪ posFormulasAt bPers l` (`Expansion.lean:268-270, 300-301`), i.e. `posFormulasAt bPers l ⊆ posFormulasAt bPers x`. **Caveat (R1)**: this is at block time on `bPers`, not on the final `b`. Recorded as a residual risk, not claimed as discharged. |

### Claims revised after verification

- **Initially considered, then rejected**: adding the loop-back edge to the *algorithm's* edge
  list (`intFImpRule` returning `some (x, l)` at reuse). Rejected because it changes
  `intExpandBranches`'s behaviour and would put `intExpandBranches_closed_unsat`
  (`Soundness.lean:1108`, a Preserved Asset, verified axiom-clean) at risk for zero benefit — the
  existential `edges` in the conclusion makes an invariant-side list sufficient.
- **Initially considered, then rejected**: keeping `IAllAccessConsistent` on the algorithm's
  `edgeSets` and existentially quantifying the extra edges inside
  `IExpandedAccessConsistent` (`∃ extra, ∀ sf ∈ e, sfAccessSat (edges ++ extra) b sf`). Rejected
  because the world-creation step then needs `(edges ++ extra) ++ [newEdge]` to agree with
  `(edges ++ [newEdge]) ++ extra` — a permutation-invariance lemma for `isAccessible` that does
  not exist and would have to be proved. Parallel `augSets` avoids it: every append is at the end.
- **Downgraded**: an early draft asserted the fix "requires no plan revision, only a Phase 6
  re-dispatch amending Phase 5.3's declarations". Revised to the opposite conclusion after
  reading the plan's `## Goals & Non-Goals` and Phase 7 task list — the fix deletes rather than
  amends Phase 5, and empties Phase 7.

### Uncertain claims, with confidence

| Claim | Confidence | Why |
|---|---|---|
| Deleting the 12 Q/`intBlockRep` declarations passes `lake lint`/`lake shake` cleanly | Medium | Not run this dispatch (R3). They are additive and mostly `private`; low ripple expected. |
| The revised plan shape suggested above is the right decomposition | Medium | It is a suggestion for the `/revise` dispatch, not a verified result. |
| C10 (remedy (a) is unsalvageable) | Medium-high | Design argument + a located code defect, not an exhaustive refutation. |
| R1's monotonicity bridge is *no harder* under this fix than under the quotient | Medium-high | Argued from the two constructions' obligations being isomorphic; neither is proved. |

### BibKey verification status (H3)

| BibKey | `references.bib` line | Entry verified | Navigable in local corpus | Evidence tier used here |
|---|---|---|---|---|
| `ChagrovZakharyaschev1997` | 75 | `@book`, Chagrov & Zakharyaschev, *Modal Logic*, Oxford Logic Guides 35, OUP 1997, isbn 978-0-19-853779-3 | **Yes** (`chagrovzakharyaschev_1997_modallogic`, `verified_conversion`) | **locally verified** (chunk-level quotes, §5.3/§5.5) |
| `GargGenoveseNegri2012` | 228 | `@inproceedings`, Garg, Genovese, Negri, *Countermodels from Sequent Calculi in Multi-Modal Logics*, LICS 2012, IEEE | **No** | **web-verified** (PDF at `people.mpi-sws.org/~dg/papers/lics12.pdf`, quoted verbatim) — reproducible only with network access |
| `NegriVonPlato2001` | 931 | `@book`, Negri & von Plato, *Structural Proof Theory*, CUP 2001 | **Yes** (`negri_von_plato_2001`, 385 chunks) — **plan's table says otherwise; the plan is wrong** | not used by the fix |
| `Fitting1983` | 211 | `@book`, Fitting, *Proof Methods for Modal and Intuitionistic Logics*, D. Reidel 1983 | No | **provenance only** — its invariant shape could not be established |
| `Dyckhoff1992` | 218 | `@article`, Dyckhoff, *Contraction-free sequent calculi for intuitionistic logic*, JSL 57(3):795-807, 1992 | No | **provenance only**; likely the wrong citation for a loop-check invariant |
| Massacci 2000, *Single Step Tableaux for Modal Logics*, JAR 24:319-364 | **absent from `references.bib`** | — | **Yes** (`massacci_2000_single_step_tableaux_for_modal_logics`) | **locally verified** (Def. 8.1/8.2, pp. 336-337) — needs a BibKey if cited in Lean docstrings |

No claim in this report labelled "verified" rests on a provenance-only key. Every load-bearing
Lean claim (C1-C9) rests on the live build; the literature is corroboration and refutation of the
alternative, at the tiers marked above.

**OCR caveat** (reported by the literature pass): the Chagrov-Zakharyaschev conversion renders
`□` variously as `D`/`U`/`O` and `⊨` as `|=`. Quotes above are normalised reconstructions; the
numbering and structure are unambiguous, the glyphs are not. Any Lean docstring citing CZ should
cite by section/theorem number, not by transcribed symbol.

---

## Artifacts

| Path | Contents |
|---|---|
| `specs/574_.../reports/01_phase6-blocker-resolution.md` | this report |
| `specs/574_.../scratch/phase6-prototype.patch` | 241-line unified diff (92 changed lines in `Scheme.lean`) — the verified fix |
| `specs/574_.../scratch/Scheme.lean.prototype` | full prototype file, `lake build` green, 6-entry sorry baseline |
| `specs/574_.../scratch/Scheme.lean.baseline` | Phase 5 end state (restored into `Cslib/`) |

`Cslib/` is byte-identical to the Phase 5 committed end state at dispatch end
(`git diff --stat Cslib/` empty).

## Recommended Next Step

`/revise 574` — consuming this report's §"Does the Plan Need Formal Revision?" and
§"Step-Ordered Fix Path" directly. The fix path is fully specified and pre-verified; the revision
is needed for plan authority (deleting Phase 5's output, emptying Phase 7), not for further
research.
