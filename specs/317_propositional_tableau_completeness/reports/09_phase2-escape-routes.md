# Report 09 — Phase 2 Escape Routes: Signature Un-Pin (a) vs `IForces` Redefinition (b)

- **Task**: 317, Phase 2 blocker of plan v5 (`plans/05_frame-change-and-fuel-raise.md`).
- **Scope**: RESEARCH ONLY. No `.lean` file edited. All claims grounded by direct `Read` + `grep`
  against **cslib** at HEAD (`553df99d` at read time; concurrent sessions committing — read-only, no
  contention). Line numbers are current-HEAD.
- **Reference-grounding tier**: Tier 1 (literature-backed: Negri–von Plato / Troelstra–Schwichtenberg
  labelled-countermodel frame) + Tier 3 (implementation-backed: the two escape routes).
- **Grounds**: reports `07_option-b-fuel-bound.md`, `08_b1-truthlemma-timp.md`; source
  `Scheme.lean`, `Kripke.lean`, `Soundness.lean`, `Completeness.lean` (int + min),
  `DecisionProcedure.lean` (int + min).

---

## VERDICT / RECOMMENDATION

**Choose Route (a): un-pin the completeness frame by restating the internal
`openBranch_countermodel` (and its two `*OpenBranch_countermodel` corollaries) over the
already-built `intAccessPreorder edges` instance of the *existing* `IForces`.**

Route (b) — redefining `IForces` in `Kripke.lean` — is **REJECTED**: it is a category error that
pollutes the shared, correct Kripke-forcing primitive with a proof-search artifact (branch edges),
puts ~205 references across 13 files of green, sorry-free soundness / FMP-decidability /
strong-completeness / algebra-bridge code at risk, and buys **nothing** on the second blocker
(monotonicity is still required for the model to be well-formed under either route). Route (b) either
corrupts the meaning of `IValid`/`MValid` (which must quantify over *all* preordered frames) or, in
its least-bad "add `IForcesEdge` alongside" form, strictly reduces to Route (a) plus a redundant
primitive.

**Decisive new fact (not in reports 07/08): Route (a)'s public blast radius is ~zero.** The only
library-visible consumer, `instDecidableIValid` (`DecisionProcedure.lean:105-111`), discharges its
`.openBranch` case via `intuitionisticTableau_complete φ hvalid` (the `IValid φ → .closed`
direction) — **it never calls `intuitionisticOpenBranch_countermodel`**. That countermodel lemma has
**no live consumer anywhere** (grep: only docstrings). So the signature we must change is consumed by
nothing; the stable public contract (`intuitionisticTableau_complete : IValid φ → .closed`,
`Decidable (IValid φ)`, `Decidable (Derivable IntPropAxiom φ)`) does **not** change.

**Second blocker**: Route (a) is *necessary but not sufficient*. It converts both blockers from
**false-as-stated** to **true-in-principle-but-fuel-entangled**. The `intExtractValuation`
monotonicity discharge and the new `sat_timp` saturation both require the returned branch to be a
*genuine* persistence fixpoint, which requires the **raised fuel** of report 07. So plan v6 = Route
(a) frame-plumbing ∪ report-07 fuel machinery. **This cannot be scoped to one wave** (≈9-11
H8-phases, ~1700-3400 lines). One wave *can* land the frame plumbing (report 08 P1-P2, independent of
B2), threading monotonicity + `sat_timp` as deferred obligations discharged later by the fuel wave.

---

## Source-to-Implementation Mapping (Tier 1)

| Source claim | BibKey (references.bib) | Lean target (file:line, HEAD) | Translation notes |
|---|---|---|---|
| Countermodel accessibility = **reflexive-transitive closure of the relational atoms `x ≤ y` on the open branch**, over the *finite* set of branch labels — never the ambient carrier order | **Negri–von Plato, *Structural Proof Theory*, Ch. 8** — **ABSENT** (recommend key `NegriVonPlato2001`) | `intAccessPreorder` = `Relation.ReflTransGen (isAccessible edges · · = true)` (`Scheme.lean:309-313`) | This IS Route (a). The preserved asset already encodes exactly the Negri–von Plato frame. The bug is that `IForces` was applied at the global `Nat.instPreorder` (total order) instead. |
| Canonical/countermodel worlds = saturated (prime) sets ordered by **inclusion**; adequacy lemma is a simultaneous both-signs induction; `→`-clause discharged by persistence across the order | `TroelstraSchwichtenberg2000` — **PRESENT** (`references.bib`) | `truthLemma` (`Scheme.lean:382-444`), mutual T/F induction; sorry at `:409` (T-imp) | The mutual induction means the externally-consumed F-direction transitively needs the T-direction, so "prove only `.2`" cannot dodge the frame problem (report 08 Q4). |
| Intuitionistic tableau: persistent `T(A→B)` rule reapplied at every accessible world; model frame = branch world-creation tree | `Fitting1983`, Ch. 4 — **PRESENT** (cited `Scheme.lean:244`,`1398`) | `intTImpRule`/`applyAllTImpRules` (`Soundness.lean:353-406`); proposed `sat_timp` field | Rule exists on the **soundness** side over `edges`; completeness needs its saturation dual as a new `IBranchSaturation` field, stated over `isAccessible`. |
| Persistence of forcing under the preorder (Prop 2.1) — the property `IForces` must preserve for a legal model | `ChagrovZakharyaschev1997` §2.2 — **PRESENT** (`references.bib`) | `iforces_persistence` (`Kripke.lean:125-140`) | Its imp-case proof uses `le_trans` of the preorder; **this is why Route (b) breaks it** — changing the imp-clause invalidates the persistence proof and hence every `KripkeModel`. |

BibKey status: `ChagrovZakharyaschev1997`, `Fitting1983`, `TroelstraSchwichtenberg2000`
**verified PRESENT**. `NegriVonPlato2001` (Ch. 8, the load-bearing citation for Route (a)'s frame)
**ABSENT** — recommend adding in plan v6's bib phase. `GargGenoveseNegri2012`, `DershowitzManna1979`
remain ABSENT (report 07).

---

## The single root cause (both blockers)

`openBranch_countermodel`/`tableau_complete` write `IForces (intExtractValuation b) (S.modelBot b) 0 φ`
with `b : IBranch Atom` (labels `: Nat`) and world `0 : Nat`. `IForces` requires `[Preorder World]`
(`Kripke.lean:81`); at `World = Nat` Lean binds the **global `Nat.instPreorder`** (total `≤`) at
signature-elaboration time. A total order cannot represent the tree/DAG accessibility that general
intuitionistic completeness needs (β-split siblings are edge-incomparable). Both live blockers are
this one fact:

1. **`truthLemma` T-imp** (`Scheme.lean:409`, sorry): goal `∀ w' : Nat, w ≤ w' → …` over numeric `≤`
   ranges over infinitely many "phantom" worlds the finite branch never labels; `T(¬p→q)` already
   falsifies it (report 08 adversarial §, verified).
2. **`intExtractValuation` monotonicity** (`Completeness.lean:113` / `Minimal/Completeness.lean:110`,
   sorry; STOP-gate `Scheme.lean:326-367`): instantiating `IValid`/`MValid` at `World = Nat`,
   `Nat.instPreorder` needs `∀{w w'} p, w ≤ w' → val w p → val w' p` over numeric `≤` — false (a
   larger label need not carry a smaller label's atoms). The extracted model
   `(Nat, ≤, intExtractValuation b)` is not even a legal `KripkeModel` (`iforces_persistence` fails),
   so even the *outer* `¬IForces_{≤} 0 φ` is effectively unprovable.

Both are **false as stated at the global preorder**, not merely hard. The preserved assets
`intAccessPreorder` / `intAccessPreorder_le_of_isAccessible` (`Scheme.lean:309-323`, committed green,
zero sorries) exist precisely to replace `Nat.instPreorder` with edge-reachability.

---

## Route (a) — un-pin the frame (restate over `intAccessPreorder edges`)

### (a.1) Exact blast radius

**Direct consumers of `openBranch_countermodel` / `tableau_complete`** (grep, whole `Cslib/`):

| Consumer | File:line | Effect of Route (a) |
|---|---|---|
| `intuitionisticOpenBranch_countermodel` | `Intuitionistic/Completeness.lean:87-90` | Signature changes (conclusion moves to edge preorder). **No live downstream consumer** (see below). |
| `minOpenBranch_countermodel` | `Minimal/Completeness.lean:93-96` | Mirror of the above. |
| `intuitionisticTableau_complete` | `Intuitionistic/Completeness.lean:106-113` | Uses `tableau_complete intScheme`; type `IValid φ → .closed` is **STABLE** (`IValid` already ∀-quantifies preorders; the internal `hvalid` obligation is discharged at the edge preorder). |
| `minimalTableau_complete` | `Minimal/Completeness.lean:106` | Mirror; `MValid φ → .closed` STABLE. |
| Temporal reference | `Temporal/Tableau/Completeness.lean:1029,1040` | **Commented out** (`--`). Not live. |

**Decidable / DecisionProcedure consumers** (the "green" surface the task asks to quantify):

- `instDecidableIValid` (`Intuitionistic/DecisionProcedure.lean:105-111`): `.openBranch` branch is
  `isFalse (fun hvalid => … intuitionisticTableau_complete φ hvalid …)`. **Consumes only the
  `IValid→closed` direction. Does NOT touch the countermodel lemma.** Signature stable ⇒ unaffected.
- `intuitionisticTableau_decides` (`:96-97`) = `⟨sound, complete⟩`; `instDecidableDerivableIntPropAxiom`
  (`:115-117`) = `decidable_of_iff (IValid φ) int_soundness_completeness`. Both rest on the stable
  `IValid→closed` type. Unaffected.
- Minimal analogues (`Minimal/DecisionProcedure.lean`): identical structure; unaffected.

**`intuitionisticOpenBranch_countermodel` / `minOpenBranch_countermodel` live-consumer grep**: only
docstrings (`DecisionProcedure.lean:30`, `Scheme.lean:1383-1384`, module headers). **Zero code
consumers.** ⇒ Route (a)'s only *actual* signature break is consumed by nothing.

**Net Route (a) blast radius: essentially nil.** Two internal corollary conclusions restate over the
edge preorder; no downstream `Decidable`/`Derivable` type changes; all soundness and FMP code is
untouched (Route (a) never touches `IForces`, `iforces_persistence`, `IValid`, `MValid`, or any
`*Soundness.lean`).

### (a.2) Second-blocker interaction

Route (a) **is the enabling precondition for both discharges** but does **not finish** either:

- It makes `truthLemma` T-imp *provable*: with `sat_timp` stated over `isAccessible` and the goal's
  `w ≤ w'` now meaning `intAccessPreorder`-reachability, `intAccessPreorder_le_of_isAccessible` lifts
  the raw witness; the 4-line discharge of report 08 Q2 closes `:409`.
- It makes monotonicity *stateable-and-true* (along edges, via `propagatePersistence`) instead of
  false (along `≤`). **But** the STOP-gate (`Scheme.lean:326-367`, verified) shows edge-monotonicity
  is still entangled with fuel: `intApplyRuleFull` maps every `T(φ→ψ)` to `.notApplicable`
  (`Rules.lean`, confirmed via `Soundness.lean:142`), so `intStepBranch = none` does **not** certify
  that `applyPersistenceFixpoint`/`applyAllTImpRules` reached a true fixpoint. A `T(atom p)`
  introduced via a `T(φ→atom p)`-triggered `intTImpRule` at a descendant needs the antecedent's
  monotonicity already propagated — resolvable only by repeated fixpoint passes bounded by fuel. The
  same fixpoint-completeness is what `sat_timp` saturation needs. ⇒ Both fold into the **report 07
  fuel-raise** (`2^(2c+2) → 2^Θ(c²)` + `intExpMeasure ≤ fuel`).

So Route (a) resolves the *frame* half of both blockers; the *fuel* half (report 07) remains and must
land jointly.

### (a.3) Postmortem-5 / CSLib acceptability

Postmortem Constraint 5 (byte-stable signatures) is in **direct, irreducible conflict** with
zero-debt here: the global-preorder conclusion of `openBranch_countermodel` is *false*, and a
false-but-byte-stable signature is closable only by `sorry`. Zero-debt strictly dominates, so
Constraint 5 **must be revised for exactly these two internal lemmas** — a principled, minimal
revision, not churn (the change *removes* sorries, does not thrash). CSLib-acceptable: no new
`sorry`/`axiom`/vacuous placeholder; the public contract (`Decidable (IValid φ)`,
`intuitionisticTableau_complete`) is unchanged, so no external CONTRIBUTING/NOTATION/ORGANISATION
surface moves. The frame construction is the standard, cited Negri–von Plato technique.

### (a.4) Minimal Lean-level sketch

```lean
-- Scheme.lean: add the saturation dual of intTImpRule (stated over isAccessible, NOT ≤)
structure IBranchSaturation (Atom …) … where
  … (sat_tand, sat_fand, sat_tor, sat_for_, sat_fimp unchanged) …
  /-- NEW: T(φ→ψ)@w with w reachable-to w' forces the β-split at w'. -/
  sat_timp : ∀ (φ ψ : Proposition Atom) (w w' : Nat),
      (b.any fun sf => sf.sign==.pos && sf.formula==(.imp φ ψ) && sf.label==w) = true →
      isAccessible edges w w' = true →
      (b.any fun sf => sf.sign==.neg && sf.formula==φ && sf.label==w') = true ∨
      (b.any fun sf => sf.sign==.pos && sf.formula==ψ && sf.label==w') = true

-- openBranch_countermodel: expose edges (already obtained internally) and restate the
-- conclusion over the edge preorder instance (SIGNATURE CHANGE — the intended revision):
lemma openBranch_countermodel (S : IntMinScheme Atom) (φ : Proposition Atom) (b : IBranch Atom)
    (h : intExpandBranches [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] (2^(2*φ.complexity+2)) S.closurePred
          = .openBranch b) :
    ∃ edges, ¬ @IForces Nat Atom (intAccessPreorder edges) (intExtractValuation b) (S.modelBot b) 0 φ

-- truthLemma T-imp (closes Scheme.lean:409) under the edge preorder:
--   intro w' hacc hφ'
--   rcases hsat.sat_timp φ' ψ' w w' a✝ (…isAccessible from hacc via ReflTransGen…) with hF | hT
--   · exact absurd hφ' ((ih_φ' w').2 hF)
--   · exact (ih_ψ' w').1 hT

-- Completeness.lean:113 bridge (instantiate IValid at the EDGE preorder, not Nat.instPreorder):
--   apply tableau_complete intScheme; intro b
--   exact h Nat (intAccessPreorder (edgesOf b)) (intExtractValuation b) (intExtractValuation_mono …) 0
-- where intExtractValuation_mono : monotone along intAccessPreorder  ← discharged by the fuel wave.
```

`intAccessPreorder` / `intAccessPreorder_le_of_isAccessible` already exist (`Scheme.lean:309-323`).

---

## Route (b) — redefine `IForces` in `Kripke.lean`

### (b.1) Exact blast radius

`IForces` is the shared propositional Kripke-forcing primitive. Grep of `Cslib/` — **205 occurrences
across 13 live files**:

| File | `IForces` refs | Green today? | Breakage under (b) |
|---|---|---|---|
| `Semantics/Kripke.lean` | 22 | yes | def site + 5 `@[simp]` clause lemmas + `iforces_persistence` (uses `le_trans`) + `IValid`/`MValid`. All invalidated. |
| `Tableau/Intuitionistic/Soundness.lean` | 32 | **yes, sorry-free** | soundness rests on `IForces` over arbitrary models. |
| `Metalogic/IntSoundness.lean` | 17 | **yes** | ditto |
| `Metalogic/IntDecidability.lean` | 17 | **yes (FMP, sorry-free)** | `int_fin_truth_lemma` over Σ-bounded worlds. |
| `SequentCalculus/LJ/Soundness.lean` | 20 | **yes** | LJ soundness vs Kripke. |
| `Metalogic/IntStrongCompleteness.lean` | 12 | yes | canonical-model completeness. |
| `Metalogic/MinStrongCompleteness.lean` | 12 | yes | mirror. |
| `Metalogic/MinSoundness.lean` | 13 | yes | mirror. |
| `Metalogic/MinDecidability.lean` | 10 | yes (FMP) | `min_fin_truth_lemma`. |
| `Semantics/Algebra/KripkeBridge.lean` | 11 | yes | Heyting-algebra ↔ Kripke bridge. |
| `Semantics/SemanticConsequence.lean` | 7 | yes | ⊨ relation. |
| `Tableau/{Intuitionistic,Minimal}/{Scheme,Completeness}.lean` | 17+6+5+… | the 317 target | also affected. |

Changing the `imp`-clause of `IForces` breaks `iforces_persistence` (`Kripke.lean:134-136` proves the
imp-case by `le_trans hw hu` — meaningless without a transitive `≤`), which is the upward-closure
every `KripkeModel` needs, cascading into **all** soundness and FMP proofs above — the largest body
of green, sorry-free task-316-adjacent code in the propositional development.

### (b.2) Second-blocker interaction

**None gained.** Even with edge-accessibility baked into `IForces`, the extracted model must still
satisfy the model's own upward-closure (`KripkeModel.v_upward_closed`, `Kripke.lean:65`) along that
accessibility — i.e. `intExtractValuation` monotone along edges — the *identical* fuel-entangled
obligation. Route (b) pays the catastrophic blast radius and does not advance the second blocker one
step.

### (b.3) Postmortem-5 / CSLib acceptability

**Not acceptable.** (b) is not a signature-stability question; it changes a semantic primitive's
*meaning*. It either (i) makes `IForces` non-general (an `edges`/`isAccessible` parameter is a tableau
artifact with no place in Kripke semantics), breaking the definitions of `IValid`/`MValid` — which
*must* range over all preordered frames for soundness and for `Decidable (IValid φ)` to decide the
*actual* validity — or (ii) forces re-proof of ~10 sorry-free files, risking regressions that violate
zero-debt-in-spirit (green→red churn). ORGANISATION/NOTATION cost is high (the primitive is imported
library-wide).

### (b.4) Minimal Lean-level sketch (for completeness; not recommended)

```lean
-- (b), least-bad variant: DO NOT touch IForces; add a parallel primitive
def IForcesEdge (edges : IEdges) (v …) (bf …) (w) : Proposition Atom → Prop
  | .imp φ ψ => ∀ w', isAccessible edges w w' = true → IForcesEdge … w' φ → IForcesEdge … w' ψ
  | …  -- other clauses identical to IForces
-- then prove  IForcesEdge edges v bf w φ ↔ @IForces Nat Atom (intAccessPreorder edges) v bf w φ
```

This equivalence lemma is *exactly* the `intAccessPreorder` instantiation Route (a) already performs
on the existing `IForces`. ⇒ (b.4) reduces to Route (a) plus a redundant primitive and a bridging
proof. Strictly dominated.

---

## Recommendation & plan-v6 sizing

**Route (a).** It is minimal (touches no shared primitive, ~zero public blast radius), reuses the
committed preserved assets, keeps every soundness/FMP/strong-completeness/algebra file green, and is
the standard cited construction. Route (b) is rejected on blast radius, semantic incorrectness, and
zero second-blocker benefit.

**Can plan v6 be one wave? No.** The full sorry-free close is the union of:

- **Frame plumbing (report 08 P1-P2, Route (a), B2-independent)** — expose branch `edges` at the
  `.openBranch` boundary; install `intAccessPreorder edges` as the completeness frame; restate the two
  `*OpenBranch_countermodel` conclusions; instantiate `IValid`/`MValid` at the edge frame with
  monotonicity threaded as a *deferred field/hypothesis*. **≈ one implementable wave, ~300-500 lines.**
- **Fuel machinery (report 07 P1-P6)** — raise fuel to `2^Θ(c²)`; `intUniverse`/`intWork`/
  `intExpMeasure`; `intExpMeasure_step_lt`; `intExpMeasure_init_le_fuel`; reformulate
  `intExpandBranches_openBranch_sat` with the measure (closes `Scheme.lean:1070`); then discharge
  `sat_timp` saturation + `intExtractValuation` monotonicity, closing `Scheme.lean:409` and the two
  `Completeness.lean` bridges. **Multiple waves, ~1400-2900 lines.**

So plan v6 ≈ **9-11 H8-phases across ≥2 waves**. A single wave can land only the frame plumbing
(leaving the fuel-entangled discharges as newly-threaded, explicitly-deferred obligations — not
sorries). If the user forbids raising the fuel formula, the correct terminal state after the frame
wave is **[BLOCKED]** on fuel sufficiency (report 07 verdict), with the frame plumbing as committed,
green, sorry-free progress.

Current sorry inventory (verified, HEAD): `Scheme.lean:409` (truthLemma T-imp), `Scheme.lean:1070`
(`intExpandBranches_openBranch_sat` fuel-0), `Completeness.lean:113`, `Minimal/Completeness.lean:110`
(the two validity→forcing bridges). Plus the documented STOP-gate `Scheme.lean:326-367` (no sorry).

---

## Adversarial Self-Verification (H4)

**Attack 1 — "Route (a)'s signature change is safe / has ~zero blast radius." Could a live consumer of
`intuitionisticOpenBranch_countermodel` exist that I missed?** I grepped the whole `Cslib/` for both
`*OpenBranch_countermodel` names; every hit outside the definition sites is a docstring/comment. The
`Decidable` instance (`DecisionProcedure.lean:105-111`, read line-by-line) discharges `.openBranch`
via `intuitionisticTableau_complete` (the `IValid→closed` arrow), **not** the countermodel. Residual
risk: a *future* consumer (or the Minimal decidability isFalse branch) might call the countermodel —
but no such call exists at HEAD. **Claim stands (HIGH confidence).** This is the single fact that most
strengthens Route (a) over reports 07/08, which conservatively assumed the countermodel signature was
load-bearing.

**Attack 2 — "Route (b) buys nothing on the second blocker." Could baking edges into `IForces` make
monotonicity vacuous?** No: `KripkeModel.v_upward_closed` (`Kripke.lean:65`) is a *field of the model*,
independent of how `IForces` reads accessibility; the extracted valuation must still be upward-closed
along whatever accessibility is used, and that is the same `propagatePersistence`-completeness =
fuel obligation (STOP-gate, verified). **Claim stands (HIGH confidence).**

**Attack 3 — "The global-preorder conclusion is genuinely *false*, so a signature change is
*unavoidable* (not mere preference)." Could `¬IForces_{≤} 0 φ` be provable by some non-`truthLemma`
route, letting us keep the byte-stable signature?** The extracted model `(Nat, ≤, intExtractValuation b)`
is not upward-closed along numeric `≤` (blocker 2), so it is not a legal `KripkeModel` and
`iforces_persistence` fails on it; there is no independent handle to refute forcing at a non-model.
And `truthLemma`'s mutual induction makes the F-direction depend on the (false) T-direction (report
08 Q4). **Claim stands (HIGH-MEDIUM):** I did not mechanically execute a failing instance of the
*outer* `¬IForces_{≤} 0 φ` (only the internal T-imp, which report 08 verified live). The frame change
is required *at least* to make the model legal; that suffices for the recommendation.

**Attack 4 — "Plan v6 cannot be one wave." Could raising the fuel alone cascade everything?** No: the
`intExpMeasure` step-lt (report 07 P3) and the `sat_timp` saturation proof (report 08 P3) are distinct
H8-phases with an explicit coupling; report 07 independently scoped 6 phases and report 08 4-5. Even
optimistically these do not collapse below ≥2 waves. **Claim stands (HIGH confidence).**

**Reuse-completeness check (5-step protocol).** (1) Foundations/preserved assets: `intAccessPreorder`,
`intAccessPreorder_le_of_isAccessible`, `isAccessible`, `IEdges`, `MonotoneEdges` all exist
(`Scheme.lean:309-323`, `Soundness.lean:344-406`) — no new abstraction needed for the frame. (2)
Soundness-side T-imp machinery (`intTImpRule`/`applyAllTImpRules`) reused as the `sat_timp` template.
(3) Fuel/measure pattern reuses Modal-K `FmpMeasure` (report 06/07). (4) Mathlib
`Relation.ReflTransGen` already underlies `intAccessPreorder`. (5) No Route requires inventing a new
CSLib typeclass. **`sat_timp` is the only genuinely new declaration; it is a transcription of an
existing soundness lemma.**

**Revision triggered.** Reports 07/08 treated the frame change and fuel raise as peers of comparable
risk and left the countermodel-signature blast radius unquantified. Verification **downgraded** the
Route-(a) cost: the signature it must change has **no live consumer**, so the public contract is fully
stable and Route (a) is materially cheaper/safer than reports 07/08 implied. The recommendation
(Route (a) + fuel wave, ≥2 waves) is **confirmed and sharpened**.

**Verified-name check.** `openBranch_countermodel`/`tableau_complete` (`Scheme.lean:1399,1447`),
`intuitionisticOpenBranch_countermodel`/`intuitionisticTableau_complete`/`instDecidableIValid`
(`Completeness.lean:87,106`, `DecisionProcedure.lean:105`), `intAccessPreorder`/
`intAccessPreorder_le_of_isAccessible` (`Scheme.lean:309,321`), `IForces`/`iforces_persistence`/
`IValid`/`MValid` (`Kripke.lean:81,125,145,153`), `truthLemma` sorry (`Scheme.lean:409`),
`IBranchSaturation`/`sat_fimp` (`Scheme.lean:72,95`), `intTImpRule`/`applyAllTImpRules`
(`Soundness.lean:353-406`) — all read directly. `sat_timp` is explicitly **proposed (does not exist)**.
BibKeys grep-checked against `references.bib`.

---

## Zero-Debt / escalation note

No `sorry`/`axiom`/vacuous placeholder recommended. Route (a) is the sorry-free-enabling change;
combined with the report-07 fuel raise it closes all four completeness-chain sorries. If the fuel
formula may not rise, the correct terminal state after the frame wave is **[BLOCKED]** on fuel
sufficiency, with this report + report 07 as the escalation record — never a placeholder.

## Files Referenced (absolute paths)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Kripke.lean` (58-168)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
  (72-144, 245-259, 305-367, 382-444, 1399-1455)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (87-113)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` (96-117)
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/{Completeness,DecisionProcedure}.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (142, 344-406)
- `/home/benjamin/Projects/cslib/references.bib` (ChagrovZakharyaschev1997, Fitting1983, TroelstraSchwichtenberg2000 present)
- `specs/317_propositional_tableau_completeness/reports/{07,08}_*.md`
