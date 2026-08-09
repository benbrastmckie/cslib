# Research Report: `openBranch_countermodel` upward-closure disposition

**Task**: 591 — decide_openbranch_countermodel_disposition
**Session**: sess_1786294327_b96abd_591
**Date**: 2026-08-09
**Status**: verdict reached, machine-checked

---

## 1. Verdict

**Route (a), with a correction to its framing.**

The `∃ edges` conjunct of `openBranch_countermodel` is **NOT refuted**. The specific inference
that all four in-source "PERMANENTLY DEFERRED / refuted" annotations rest on is not merely
`[UNVERIFIED]` — it is **machine-refuted**.

For `phiRef1`, on the branch the *real* `intuitionisticTableau` returns, the edge set
`edges = [(1, 0)]` satisfies **both** conjuncts:

| `edges` | upward-closed | `IForces … 0 phiRef1` | witnesses `∃`? |
|---|---|---|---|
| `[]` (discrete) | true | true | no |
| `[(1,0),(2,1)]` (raw tree) | true | true | no |
| `[(1,0),(2,1),(1,2),(2,2)]` (augmented) | **false** | false | no |
| maximal inclusion frame `⊑` | true | true | no |
| **`[(1,0)]`** | **true** | **false** | **YES** |

Exhaustive enumeration over the *complete* space of admissible edge sets (see §3) finds
**40 distinct witnessing edge sets** for `phiRef1` under `intScheme`, and a witness for every
other open-branch formula tested. Under `minScheme` (the DP-4 site), `[(1,0)]` satisfies **both**
upward-closure obligations (valuation *and* `⊥`) and falsifies `phiRef1` at world 0.

This does **not** prove `openBranch_countermodel` in general (§5). It establishes that the
evidence the four deferrals cite does not support them, so the deferrals must be re-annotated,
and the planned restatement of the completeness theorems must **not** proceed on the strength of
a refutation that does not exist.

### Two premises in the task description are factually wrong

1. **"the existing refutation evidence (scratch/BetaSplitRefutation.lean) is CITED BUT ABSENT"**
   — it is **present**, at `/home/benjamin/Projects/cslib/CslibTests/BetaSplitRefutation.lean`
   (22 KB, `#guard_msgs`-asserted, CI-protected). It was promoted out of `scratch/` by the
   evidentiary-repair work, which is already `completed`. The prerequisite is satisfied; no
   blocking dependency remains.

2. **"DP-4 … refuted INDEPENDENTLY of DP-3"** — machine-refuted; see §4.3.

---

## 2. The decisive structural argument (independent of any computation)

`openBranch_countermodel` for `intScheme` concludes

```
∃ edges, (∀ w w' p, w ≤_edges w' → val_b w p → val_b w' p) ∧ ¬ IForces … 0 φ
```

with `val_b = intExtractValuation b` and `botForces = fun _ => False`.

`IValid φ` (`Cslib/Logics/Propositional/Semantics/Kripke.lean:145`) quantifies over **every**
preorder and **every** upward-closed valuation. So if `φ` were intuitionistically valid, the
first conjunct would force `IForces … 0 φ` for *every* admissible `edges`, making the existential
false. Contrapositive:

> **Any refutation of `openBranch_countermodel` must exhibit an IPC-valid `φ` on which the
> algorithm returns `.openBranch`.** Equivalently: the lemma is false exactly when the tableau
> procedure is incomplete.

`phiRef1 = ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr` is not even *classically* valid
(`ps = T, pr = F` falsifies it — and `BetaSplitRefutation.lean:400` says so itself). It was
therefore never a candidate refutation of this lemma, whatever it does to any particular frame.
This alone settles the decision; §3–§4 confirm it computationally.

---

## 3. New structural lemma: the admissible edge space is exactly `𝒫(⊑)`

Let `A(w) = { p | T(atom p)@w ∈ b }`, and let `⊑` be atom-set inclusion: `w ⊑ w' ⟺ A(w) ⊆ A(w')`.

- If `edges` keeps `val_b` upward-closed, then `w ≤_edges w' → A(w) ⊆ A(w')`, i.e.
  `≤_edges ⊆ ⊑`.
- `⊑` is already reflexive and transitive, so `ReflTransGen` of any subset of `⊑`'s pair set stays
  inside `⊑`.

Hence **the admissible `edges` are exactly the subsets of `⊑`'s pair set, and every such subset is
automatically upward-closed.** Two consequences:

1. **The search space is finite and small** — 7 pairs for `phiRef1`, so 128 candidates — which is
   what makes the exhaustive enumeration in §4 a *complete* search rather than a sample.
2. **Conjunct 1 needs no fact about the tableau algorithm at all.** Instantiating `edges` with any
   sub-`⊑` edge list discharges it by transitivity of `⊆` on atom sets. The entire persistence /
   `genCopies` / augmented-edge invariant apparatus that DP-3/DP-4/DP-5 are blocked on is
   **not required for this conjunct**. This is the single most useful finding for implementation.

`edges` is unconstrained in the statement (`IEdges := List (Nat × Nat)`,
`Rules.lean:85`); the statement never ties it to the algorithm's edge list. The proof route chose
to thread the `augSets` witness through, but nothing in the statement demands that.

---

## 4. Machine-checked evidence

All probes are preserved at
`/home/benjamin/Projects/cslib/specs/591_decide_openbranch_countermodel_disposition/scratch/`
and run with `lake env lean <file>` from the repo root. They use `#eval!` because
`Scheme.lean` carries `sorry`s; none of the probes *depends* on a sorried result — they evaluate
`intuitionisticTableau` / `minimalTableau`, which are executable definitions.

The evaluator mirrors `IForces` (`Kripke.lean:81`) case-for-case, with `≤` computed as BFS
reflexive-transitive closure of the parent→child step relation. That equals
`(intAccessPreorder edges).le`: `isAccessible` under-approximates reachability only via its fuel
bound, and `ReflTransGen` restores the closure in both directions.

### 4.1 Branch facts (`WitnessProbe.lean`)

`intuitionisticTableau phiRef1` returns `.openBranch b` with

```
world 0 : {}          world 1 : {ps}        world 2 : {pr, ps}
raw edges [(1,0),(2,1)]     loop-back edges [(1,2),(2,2)]
```

World 0 carries **no** positive atoms, so upward closure out of 0 is vacuous — this is why
pruning the frame down to `[(1,0)]` costs nothing on conjunct 1.

### 4.2 Exhaustive search, `intScheme` (`WitnessSearch2.lean`)

`(verdict, #worlds, #admissible pairs, first witness, #witnesses)`:

```
phiRef1   ("OPEN", 4,  7, some [(3,0),(1,3)],  40)
phiRef2   ("OPEN", 4,  8, some [(3,0),(1,3)], 216)
phiRef3   ("OPEN", 6, 19, some [(5,0),(1,5)], 40960)
exMiddle  ("OPEN", 3,  4, some [(2,0),(1,2)],  10)
dblNeg    ("OPEN", 4,  9, some [(3,0),(2,3)], 334)
peirce    ("OPEN", 4,  9, some [(3,0),(2,3)], 334)
deMorgan  ("OPEN", 5, 12, some [(4,0),(3,4),(2,4)], 2400)
dummett   ("OPEN", 4,  6, some [(3,0),(2,3),(1,3)],  26)
```

The `"OPEN"` verdict (rather than `"OPEN/UC-SANITY-FAILED"`) is an in-probe assertion that every
reported witness independently passes the upward-closure check — i.e. the §3 reduction is not
merely assumed, it is re-verified on every hit.

### 4.3 Minimal scheme, the DP-4 site (`MinProbe.lean`)

`minimalTableau phiRef1` yields the same world/atom table, with `⊥` forced nowhere.
`(edges, val-UC, ⊥-UC, ¬Forces)`:

```
[]              (true, true, false)
[(1,0)]         (true, true, TRUE)   ← witness
[(1,0),(2,1)]   (true, true, false)
[(2,0)]         (true, true, false)
[(1,0),(2,0)]   (true, true, TRUE)   ← witness
```

DP-4's claim of an *independent* refutation under `isMinimallyClosed` is therefore also refuted:
`[(1,0)]` discharges both of the upward-closure obligations DP-4 names and still falsifies
`phiRef1` at 0.

### 4.4 The maximal frame is not a uniform witness (`WitnessSearch3.lean`)

`(UC, ¬Forces)` for the maximal inclusion frame `⊑`:

```
phiRef1 (true, false)   phiRef2 (true, true)   phiRef3 (true, false)
exMiddle/dblNeg/peirce/deMorgan/dummett  all (true, true)
```

So `edges := ⊑` is **not** a uniform construction — it fails on exactly the `phiRef1`/`phiRef3`
family. The witness must be a properly smaller sub-preorder chosen as a function of `b`.

### 4.5 Source claims confirmed

- Augmented frame fails upward closure at `phiRef1` — **confirmed** (`firstViolation = (2,1,2)`).
- Raw frame satisfies upward closure yet forces `phiRef1` at 0 — **confirmed**. Mechanism: world 2
  forces `ps → (ps → pr)` (it has both `pr` and `ps`) but not `pb`, so the antecedent's second
  conjunct fails at world 1, and the implication holds vacuously there. Dropping the `(2,1)` edge
  removes world 2 from world 1's successors, which is exactly what `[(1,0)]` does.

---

## 5. What is *not* established

`openBranch_countermodel` is a `∀ φ` statement. The evidence above covers eight formulas
exhaustively under `intScheme` and two under `minScheme`. It does not construct a general witness,
and §4.4 shows the obvious canonical candidate does not generalise. So:

- Route (b) ("no edge set works") is **dead as argued** — its only evidence is refuted.
- Route (a) ("some edge set works") is **strongly supported but not proved in general**.
- The real remaining obligation is a **uniform construction** of `edges` from `b` plus a truth
  lemma over that frame. Per §2, proving it is equivalent to proving the tableau procedure
  complete, so it is not a small residual — it is the completeness theorem itself.

Honest characterisation of the four sites: **open, with a known-bad proof route and a
characterised admissible search space** — not "unprovable as stated", not "refuted".

---

## 6. Recommended dispositions (deliverable for the implementation phase)

Zero new sorries, zero new axioms; the four `sorry`s **stay**. Only annotations change.

| Site | Current annotation | Required correction |
|---|---|---|
| `Scheme.lean:7862` docstring + `:7937` proof-site comment (`openBranch_countermodel`) | "DISPOSITION UNDECIDED … gated on an open decision point" | Replace with: disposition **decided — not refuted**. Record the §2 structural argument, the `[(1,0)]` witness, the §3 `𝒫(⊑)` characterisation, and that the augmented frame is a bad witness choice rather than evidence against the statement. Drop the "no change authorized" freeze. |
| `Intuitionistic/Completeness.lean:161` (DP-3) | "PERMANENTLY DEFERRED — unprovable as stated"; "refuted at `phiRef1`" | Both claims are false. Re-annotate as an **open** obligation blocked on a uniform frame construction. Keep the `sorry`. Keep the existing prohibition on `exact h Nat (intExtractValuation _b) _huc 0` — it still only launders an unproved conjunct. |
| `Minimal/Completeness.lean:155` (DP-4) | "PERMANENTLY DEFERRED"; "refuted **independently** of DP-3" | Both false (§4.3). Re-annotate as open. The second, genuinely separate obligation — upward closure of `minBranchBotForces b` — is real and should be kept as a named residual; §4.3 shows it holds at the witness but it is not proved in general. |
| `Scheme.lean:760` (DP-5, `truthLemma` `T(φ'→ψ')`) | "PERMANENTLY DEFERRED, unprovable as stated … REFUTED by a machine-verified counterexample" | The counterexample refutes *augmented-edge positive-formula persistence*, which is a real refutation of **that invariant**. But DP-5's conclusion does not follow: the truth lemma's frame is a parameter, and the refuted invariant is only needed if the frame is the augmented one. Re-annotate as: the augmented-frame instantiation is refuted; the lemma over a sub-`⊑` frame is open. |

Also flag for the task tracker (not a code change): the **restatement task**
(`restate_propositional_tableau_completeness_theorems`) rests on the premise that the conjunct is
refuted. That premise is now false, so the task should be re-scoped or blocked pending this
verdict rather than executed as written.

### Proof route if the general result is later pursued

1. Define `inclEdges b : IEdges` (or a tuned sub-preorder) and prove conjunct 1 from transitivity
   of `⊆` on atom sets — short, and independent of all algorithm invariants (§3).
2. Conjunct 2 requires a truth lemma over the chosen frame. This is the hard part and is
   equivalent to procedure completeness (§2). §4.4 rules out the maximal frame; a
   "raw edges pruned at reuse/blocking sites" construction matches the `phiRef1` witness and is
   the most promising starting point, but is unverified.
3. The underlying algorithm defect the source correctly identifies —
   `intFImpReuseWitnessAnc?` records a loop-back edge on a containment check it never
   re-validates as the branch grows — remains real, and is what makes the augmented frame
   unusable. Fixing it is an alternative route to a workable frame.

---

## 7. Reuse check (CSLib reuse-first)

- `intAccessPreorder` (`Scheme.lean:268`), `intExtractValuation` (`Soundness.lean:1129`),
  `IEdges`/`isAccessible` (`Rules.lean:85,92`), `IForces`/`IValid`/`iforces_persistence`
  (`Kripke.lean:81,145,128`) all already exist and cover everything needed. **No new abstraction
  is recommended**; the only candidate new definition is `inclEdges`, and only if step 1 above is
  pursued.
- `Mathlib.Relation.ReflTransGen` is already the closure mechanism in use; no Mathlib addition
  needed.
