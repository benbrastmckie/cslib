# B1 Research: Closing `sorry 330` — truthLemma T(φ→ψ) forward case

Task 317 · Hard-mode research (H2 anti-analysis, H3 reference grounding, H4 adversarial verification)
Agent: cslib-research-hard-agent · Reference-grounding tier: **Tier 1 (literature-backed)** + Tier 3 (implementation-backed)

---

## Headline result (read this first)

**`sorry 330` cannot be closed by adding a saturation lemma to the current setup, because the
goal as stated is _false_ under the completeness frame that is currently in scope.** The
completeness `truthLemma` runs `IForces` over `[Preorder ℕ]` with the **standard `≤`**, so the
T(→) case must prove `∀ w' : ℕ, w ≤ w' → …` over *all* naturals `≥ w`, including infinitely many
"phantom" worlds that the finite branch never labels. A concrete phantom world falsifies the
obligation (see §Adversarial verification). Closing 330 requires **re-basing the completeness
countermodel's accessibility from numeric `≤` to the branch's edge-reachability relation**
(`isAccessible`, already formalized on the soundness side), *and then* adding a persistent
`sat_timp` saturation field. Neither the naive "one-sided F-only" reformulation nor a "branch
completeness over ℕ" strengthening can rescue the current frame.

---

## Source-to-Implementation Mapping (H3)

| Source Claim | Citation | Lean Target | Translation Notes |
|--------------|----------|-------------|-------------------|
| Kripke forcing of `A→B` at `w` = "for all `w' ≥ w`, `w'⊩A ⟹ w'⊩B`" over the **model's own** accessibility `≤` | Troelstra & Schwichtenberg, *Basic Proof Theory* (2nd ed.), §2.4 (Kripke semantics for IPC); Negri & von Plato, *Structural Proof Theory*, Ch. 8 (labelled calculi G3I, relational atoms `x ≤ y`) | `Kripke.lean:100` `IForces_imp` | Frame `≤` must be the *constructed* accessibility of the countermodel, **not** the ambient order on the carrier. The bug is that the carrier's ambient `≤` on ℕ was taken as accessibility. |
| Countermodel = **saturated** (Hintikka/prime) sets as worlds; accessibility = the constructed inclusion/edge relation; the finite set of worlds is exactly those the construction creates | Troelstra & Schwichtenberg §2.4 (canonical model over saturated theories, inclusion order); Negri & von Plato Ch. 8 (countermodel read off an open saturated derivation branch; worlds = labels occurring on the branch) | `Scheme.lean:72-99` `IBranchSaturation`; `Soundness.lean:344-348` `MonotoneEdges` / `isAccessible` | "World" ranges over the **finite** set of branch labels, ordered by branch edges — never over all of ℕ. |
| Truth lemma is a **simultaneous induction** on both signs (T- and F-direction), mutually dependent through `→` | Troelstra & Schwichtenberg §2.4 (truth lemma / "adequacy" both directions); Fitting, *Proof Methods for Modal and Intuitionistic Logics*, Ch. 4 (already cited in-file at `Scheme.lean:45,244,1313`) | `Scheme.lean:303-335` `truthLemma` | F-imp needs the T-direction of a subformula (`ih_φ'.1`), so the two directions cannot be decoupled. |
| Persistent `T(A→B)` rule: `T(A→B)` copies to every accessible world and there splits `F(A) ∣ T(B)` | Fitting Ch. 4 (intuitionistic tableaux: special "S⁺→" rule reapplied at each accessible world); Negri & von Plato Ch. 8 (rule `L→` with monotonicity of relational atoms) | `Soundness.lean:377-406` `intTImpRule`/`applyAllTImpRules`; `Expansion.lean:122,133,199,245` `propagatePersistence`/`applyPersistenceFixpoint` | The rule already exists — but only on the **soundness** side (over `edges`). Completeness needs its saturation dual as a new `IBranchSaturation` field. |

> Note on BibKey: this task references the PDFs in `specs/literature/` directly
> (`Structural_Proof_Theory_Negri_von_Plato.pdf`, `Basic_Proof_Theory_Troelstra_Schwichtenberg.pdf`).
> `references.bib` is **not present** in the CSLib project root; the only in-repo bib key used by
> this development is `[Fitting1983]` (referenced at `Scheme.lean:45,244,1313`,
> `Soundness.lean` references, and the Kripke module). No new BibKey could be verified against a
> `references.bib`; recommend adding `Negri2001` (Negri & von Plato) and `Troelstra2000`
> (Troelstra & Schwichtenberg) to whatever bib source the repo adopts. See §H3 status.

---

## Q1 — The exact obligation at `Scheme.lean:330` (`lean_goal`, verified)

Goal state captured live via `lean_goal` at line 330 (`case imp.left`):

```
φ' ψ' : Proposition Atom
ih_φ' : ∀ (w : ℕ),
  ((b.any fun sf => sf.sign==.pos && sf.formula==φ' && sf.label==w) →
      IForces (intExtractValuation b) (S.modelBot b) w φ') ∧
  ((b.any fun sf => sf.sign==.neg && sf.formula==φ' && sf.label==w) →
      ¬IForces (intExtractValuation b) (S.modelBot b) w φ')
ih_ψ' : (… same shape for ψ' …)
w : ℕ
a✝ : (b.any fun sf => sf.sign==.pos && sf.formula==(φ' → ψ') && sf.label==w) = true
⊢ ∀ (w' : ℕ),
    w ≤ w' →
      IForces (intExtractValuation b) (S.modelBot b) w' φ' →
      IForces (intExtractValuation b) (S.modelBot b) w' ψ'
```

Load-bearing facts in this state:
- The conclusion quantifies `∀ (w' : ℕ), w ≤ w' → …`. The `≤` is the **default `Preorder ℕ`** (standard
  numeric order) — `truthLemma` (`Scheme.lean:303`) never installs a custom `Preorder`, and `IForces`
  (`Kripke.lean:81`, `[Preorder World]`) is applied at `World = ℕ`.
- `intExtractValuation b w' p` (`Soundness.lean:1811`) `= (T(atom p)@w' ∈ b)`. At any world `w'` that
  carries **no** signed formulas, every atom is false and `S.modelBot b w'` is `False`
  (`intScheme.modelBot = fun _ _ => False`, `Scheme.lean:159`).
- Both IHs give **both** directions for `φ'` and `ψ'`; the hypothesis `a✝` is `T(φ'→ψ')@w ∈ b`.

Note the F-direction sibling (`Scheme.lean:331-335`) is already proved and consumes `hsat.sat_fimp`
plus `ih_φ'.1` and `ih_ψ'.2`.

## Q2 — What branch property is needed?

**A new field is required; the existing five are insufficient, and even a naive completeness field
would be unprovable under the current frame.**

Existing `IBranchSaturation` fields (`Scheme.lean:74-99`): `sat_tand`, `sat_fand`, `sat_tor`,
`sat_for_`, `sat_fimp`. Only `sat_fimp` concerns `→`, and it is the **existential** F-rule
(`F(φ→ψ)@w → ∃ w'≥w, T(φ)@w' ∧ F(ψ)@w'`) — used by the already-proved F-direction. **Nothing in the
structure gives the T(→) beta-split at accessible worlds.** The intended-but-absent field is named
in the in-file comment (`Scheme.lean:325`, "`sat_timp`").

The property the T(→) case needs is the saturation dual of the soundness rule
`intTImpRule`/`applyAllTImpRules` (`Soundness.lean:353-406`):

```
sat_timp : ∀ (φ ψ : Proposition Atom) (w w' : Nat),
    (b.any fun sf => sf.sign==.pos && sf.formula==(.imp φ ψ) && sf.label==w) = true →
    Accessible w w' →                                   -- ⬅ MUST be edge-reachability, not w ≤ w'
    (b.any fun sf => sf.sign==.neg && sf.formula==φ && sf.label==w') = true ∨
    (b.any fun sf => sf.sign==.pos && sf.formula==ψ && sf.label==w') = true
```

With such a field, the T(→) case closes cleanly:
```
intro w' hacc hφ'
rcases hsat.sat_timp φ' ψ' w w' a✝ hacc with hF | hT
· exact absurd hφ' ((ih_φ' w').2 hF)     -- F(φ')@w' ⇒ ¬w'⊩φ', contradiction
· exact (ih_ψ' w').1 hT                    -- T(ψ')@w' ⇒ w'⊩ψ'
```

But this only type-checks/holds if `Accessible = w ≤ w'` is replaced by the branch's edge
relation **and** `sat_timp` is actually true — which fails under numeric `≤` (§Adversarial). Under
edge-reachability it is provable, because `propagatePersistence` (`Expansion.lean:199,245`) copies
`T(φ→ψ)` to every edge-created world `w'`, where the saturation loop then applies the T(→) beta
rule producing `F(φ)@w' ∣ T(ψ)@w'`. **The truth is: numeric `≤` over-generates accessible worlds;
the finite branch can only witness the beta-split at edge-reachable worlds.**

Two coupled sub-requirements also surface:
1. **Monotonicity of `intExtractValuation`** along accessibility (needed for the model to even be a
   `KripkeModel`, `Kripke.lean:64-65` `v_upward_closed`). Provable from `propagatePersistence`
   copying `T(atom p)` to created worlds — but again only along **edges**, not numeric `≤`.
2. The `IBranchSaturation` **structure signature changes** (new field), so B2 (`Scheme.lean:986`,
   `intExpandBranches_openBranch_sat`) must additionally discharge `sat_timp` — a coupling, see Q6.

## Q3 — Standard technique + citations

The published completeness/countermodel constructions never quantify accessibility over the ambient
carrier order; they quantify over the **constructed** relation on the finite set of created worlds:

- **Negri & von Plato, _Structural Proof Theory_, Ch. 8** (labelled sequent calculi for
  intuitionistic logic, G3I). The countermodel is read off a single open, saturated branch of a
  failed root-first proof search. Worlds = the **labels** `x, y, …` occurring on that branch;
  accessibility = the reflexive-transitive closure of the relational atoms `x ≤ y` present on the
  branch (the frame conditions Refl/Trans are built in as rules). The truth lemma ("if the search
  fails, the constructed model refutes the endsequent") inducts on formula structure; the `→`-case
  uses exactly the `L→`/`R→` saturation of relational atoms — i.e. `T(A→B)` at `x` together with
  `x ≤ y` on the branch forces `F(A)@y ∣ T(B)@y`. This is the direct analogue of the proposed
  `sat_timp`, with `Accessible = (branch ≤-atoms)*`, **not** the metalanguage `≤`.

- **Troelstra & Schwichtenberg, _Basic Proof Theory_ (2nd ed.), §2.4** (Kripke semantics and
  completeness of IPC). The canonical/countermodel construction takes **saturated (prime) sets** as
  worlds ordered by **set inclusion**; the truth (adequacy) lemma is a simultaneous induction on
  both membership directions, and the `→`-clause is discharged using saturation ("if `A→B ∉ Γ` then
  there is a saturated `Δ ⊇ Γ` with `A ∈ Δ`, `B ∉ Δ`" for the F-direction; and monotone persistence
  of `A→B` across the inclusion order for the T-direction). Again accessibility is the constructed
  inclusion order over a specific (here possibly infinite, but in the finite/FMP case finite) set,
  never an ambient numeric order.

- **Fitting, _Proof Methods for Modal and Intuitionistic Logics_, Ch. 4** (already the in-file
  reference, `Scheme.lean:45`). Intuitionistic tableaux carry a special persistent `T(A→B)` rule
  that is **reapplied at every accessible world** created later; the model extracted from an open
  branch uses the branch's world-creation tree as its frame.

All three agree: **the frame of the extracted model is the branch's own (finite) accessibility, and
the T(→) truth-lemma case is discharged by a persistence+beta saturation over that frame.** The
current Lean development has this exactly right on the **soundness** side
(`Soundness.lean:344-406`, `MonotoneEdges`/`intTImpRule`) but wired the **completeness** side to the
ambient `≤ : ℕ → ℕ → Prop`.

## Q4 — Full truth lemma vs. one-sided reformulation (recommendation)

**Recommendation: neither "one-sided" nor "branch-completeness-over-ℕ" works; the mutual truth lemma
is required, and it is only true after the frame change. Adopt the edge-accessibility frame + a
`sat_timp` field, keeping the full two-direction `truthLemma`.**

Why the one-sided path fails (this refutes the handoff's suggestion at the top level):
- `openBranch_countermodel` (`Scheme.lean:1336`) indeed calls **only** `.2` at the top level:
  `exact (truthLemma S b hopen hsat φ 0).2 hFmem`. So *externally* only the F-direction is consumed.
- **But the induction is mutually recursive.** The already-proved F-imp case
  (`Scheme.lean:333-335`) calls `(ih_φ' w').1` — the **T-direction** of the subformula. So the
  T-direction cannot be dropped from the induction; a "prove only `.2`" restructuring still has to
  establish `.1` for every implication-shaped subformula.
- And `.1` **for an implication subformula is exactly the false statement** (§Adversarial). So the
  frame problem infects the F-direction transitively. One-sidedness changes nothing.
- Downstream, dropping `.1` would also not simplify `tableau_complete` (`Scheme.lean:1360-1368`) or
  the `Decidable`/decision-procedure users — they consume `openBranch_countermodel`/`tableau_complete`
  as black boxes and are unaffected by the internal structure. So there is **no downstream saving**
  to justify a one-sided rewrite.

Why "branch completeness at every formula/world pair over ℕ" fails: a finite branch labels only
finitely many of the infinitely many `w' : ℕ`; it can never sign a formula at a never-created label.
"T-or-F at every world" is only *attainable* when "world" ranges over the finite branch labels —
which is *definitionally the same move* as restricting the frame to edge-reachable worlds. The two
handoff options therefore collapse into one: **restrict the frame.**

Cost/scope of the recommended path: it is larger than "add one lemma" — it touches the frame plumbing
(`Preorder`/accessibility on the completeness carrier), requires exposing the branch **edges** from
the expansion (currently discarded at the `.openBranch b` boundary, `Scheme.lean:1314-1318`), and
adds `sat_timp` + `intExtractValuation` monotonicity. See Q6 for the phased breakdown.

## Q5 — Interaction with the Option A dedup (commit 4202d1df)

World reuse **sharpens** the case against numeric `≤` and must be accounted for in the frame design:

- Dedup (per the fix "require explicit `F(ψ)@x` on reuse") lets a world-creation step point back to an
  **existing** label `x` instead of allocating a fresh larger one. That means an accessibility edge
  `(w', w)` can now have `w' ≤ w` numerically **false** (the reused target may be a *smaller*
  label), while the *intended* accessibility (edge-reachability) still holds. Numeric `≤` is thus not
  merely too coarse (phantom worlds) but can be **outright inconsistent** with the true accessibility
  once reuse is live. This is independent confirmation that the accessibility relation must be the
  edge relation, not `≤`.
- `sat_fimp` (`Scheme.lean:95-99`) still asserts the numeric `w ≤ w'` ordering for the F-created
  witness (justified by `nextWorld` monotonicity, `Scheme.lean:70-71`, `ILabelBound`,
  `Scheme.lean:635-639`). If reuse can target a smaller label, the `w ≤ w'` clause of `sat_fimp`
  needs re-checking; the edge-reachability reformulation of accessibility would keep `sat_fimp`
  coherent (reachability, not numeric order). **Flag for the planner:** verify `sat_fimp`'s `w ≤ w'`
  survives dedup, or restate it over the edge relation alongside `sat_timp`.
- The persistence copy (`propagatePersistence`, `Expansion.lean:199,245`) on reuse must ensure the
  reused world receives the parent's `T`-formulas; if reuse *skips* re-propagation, monotonicity of
  `intExtractValuation` along that edge could fail. **Flag:** the monotonicity lemma (Q2 sub-req 1)
  must be proved against the *dedup* expansion, not a fresh-world idealization.

## Q6 — v5 phase breakdown (H8-sized, ~100-500 lines each)

Ordering note: **B1 is _partially_ independent of B2.** The frame/plumbing phases (P1–P2 below) do
not touch `Scheme.lean:986`. But adding a field to `IBranchSaturation` (P3) forces B2's
`intExpandBranches_openBranch_sat` to discharge the extra field. **Recommend: land P1–P2 in parallel
with B2, then sequence P3 after (or jointly with) B2's fuel proof so the structure change is made
once.** Do **not** run P3 concurrently with an in-flight B2 on the same structure.

- **P1 — Expose branch edges from the expansion (plumbing).** Thread the per-branch `edges` (already
  tracked internally, cf. the `[[]]` edge argument to `intExpandBranches`, `Scheme.lean:1316`) out
  through the `.openBranch` result, or provide a structural lemma
  `intExpandBranches_openBranch_edges` yielding the branch's `IEdges`. Reuse `IEdges`/`isAccessible`
  (`Soundness.lean`). ~150-300 lines. Independent of B2.

- **P2 — Install edge-accessibility as the completeness frame.** Define the countermodel `Preorder`
  on the carrier as the reflexive-transitive closure of `isAccessible edges` (or move to a
  reachable-label subtype). Re-express `truthLemma`/`openBranch_countermodel`/`tableau_complete`
  (`Scheme.lean:303,1314,1360`) over this `Preorder`. Prove `intExtractValuation` monotone from
  `propagatePersistence` (Q2 sub-req 1). Confirm `IValid φ` still instantiates at this frame for
  `hvalid` (`Scheme.lean:1348-1353`). ~300-500 lines. Independent of B2; largest phase — consider
  splitting P2a (frame + monotonicity) / P2b (re-thread the three completeness lemmas).

- **P3 — Add `sat_timp` to `IBranchSaturation` and prove it.** Extend the structure
  (`Scheme.lean:72-99`) with the `sat_timp` field (Q2), stated over the edge relation. Prove it in
  `IExpandedConsistent_sat` (`Scheme.lean:563-633`) by mirroring the soundness
  `applyAllTImpRules`/`intTImpRule` argument (`Soundness.lean:353-406`): persistence copies
  `T(φ→ψ)` to `w'`, saturation applies the beta split. **Coupled with B2:** also discharge the new
  field inside `intExpandBranches_openBranch_sat` (`Scheme.lean:986`). ~200-400 lines. Sequence
  after/with B2.

- **P4 — Close `sorry 330`.** Replace it with the 4-line `sat_timp` discharge (Q2 snippet). Re-verify
  the F-imp case still type-checks against the new frame (its `w' ≥ w` witness from `sat_fimp` must
  be edge-accessible — see Q5 flag). `lake build` the module. ~50-150 lines incl. fallout fixes.
  Sequence last.

Estimated total: ~700-1350 lines across 4-5 phase runs. **This is a frame-restructuring, not a
one-lemma fill** — plan v5 should size B1 accordingly and not budget it as a peer of a single
saturation case.

---

## Adversarial Self-Verification (H4)

**Challenge: is the T(→) obligation at line 330 actually _false_ under the current frame, or merely
hard? Construct the single worst case and either resolve or downgrade the recommendation.**

Worst case (the handoff's "nested `φ→(ψ→χ)` at a reused world", instantiated minimally): consider a
branch containing `T((¬p)→q)@0` on an **open, fully saturated** branch (`¬p := p→⊥`; `q, p` atoms).
Pick a natural number `w' = k` strictly larger than every label the finite branch ever created — a
"phantom" world. Because `truthLemma`'s frame is `(ℕ, ≤)`, we have `0 ≤ k`, so `k` is in the scope
of the goal's `∀ w'`.

- `intExtractValuation b k p = (T(atom p)@k ∈ b) = False` (no formula carries label `k`), so `k ⊮ p`.
- Therefore `k ⊩ ¬p`: `IForces … k (p→⊥) = ∀ j ≥ k, j⊩p → j⊩⊥`; every `j ≥ k` is also phantom so
  `j ⊮ p`, making the implication vacuously true. Hence `k ⊩ ¬p`, i.e. `k ⊩ φ'` with `φ' = ¬p`.
- `intExtractValuation b k q = False`, so `k ⊮ q`, i.e. `¬ (k ⊩ ψ')` with `ψ' = q`.
- So `w' = k` witnesses `k ⊩ φ' ∧ ¬(k ⊩ ψ')`, **refuting** `∀ w' ≥ 0, w'⊩φ' → w'⊩ψ'`.

The goal at 330 is therefore **not provable** — it has a genuine countermodel — whenever a branch
carries a `T`-implication whose antecedent is intuitionistically forced at empty worlds (any
`T(¬A→B)`, and more generally any `T(A→B)` with `A` valid-at-the-empty-world). This is not an
artifact of exotic nesting; the minimal `T(¬p→q)` already breaks it. **Resolution:** the countermodel
must exclude phantom worlds from accessibility — i.e. accessibility = edge-reachability — which is
exactly the recommended frame change. The recommendation is **confirmed, and upgraded from "needs a
lemma" to "needs a frame change"**; the earlier framing of B1 as "add `sat_timp`" alone is
**downgraded** (necessary but not sufficient).

Second challenge — *does the recommended frame change silently break the already-green F-direction?*
The F-imp proof (`Scheme.lean:333-335`) uses the `sat_fimp` witness `w'` with `w ≤ w'` and calls
`hcontra w' hw' …`; under the new frame, `hw'` must witness **edge-accessibility** `w ≤_edge w'`, not
numeric `≤`. Since the `sat_fimp` witness is a genuinely edge-created world, this holds — **but it
must be re-proved**, and dedup (Q5) means the numeric `w ≤ w'` clause of `sat_fimp` may need
restating over edges. Captured as a Q6-P4 flag; not a blocker, but not free either.

Third challenge — *reuse completeness of the Reuse Check Protocol.* Confirmed the T(→) machinery
already exists on the soundness side and is reusable: `intTImpRule`, `applyAllTImpRules`
(`Soundness.lean:353-406`), `isAccessible`, `MonotoneEdges` (`Soundness.lean:344-348`),
`propagatePersistence`, `applyPersistenceFixpoint` (`Expansion.lean:122-139,199,245`), and `IEdges`.
No new *concept* is invented; `sat_timp` is the saturation transcription of an existing soundness
lemma. I did **not** find a pre-existing edge-based `Preorder`/frame on the completeness carrier
(that is the gap). `lean_leansearch`/`lean_loogle` were not needed — this is an internal-architecture
problem, not a missing-Mathlib-lemma problem; the corpus `literature-search.sh` returned empty for
both queries (index coverage gap), so citations rest on the two named PDFs read by section.

Uncertain / lower-confidence items (flagged for the planner, not asserted):
- **Medium confidence** that edges are cleanly exposable at the `.openBranch` boundary without a
  return-type change; the internal edge argument exists but its post-loop availability was not proved
  here (P1 risk).
- **Medium confidence** on the exact `IValid`-instantiation at a non-`≤` `Preorder` for `hvalid`
  (`Scheme.lean:1348-1353`); `IValid` quantifies over all preordered upward-closed models, so it
  *should* instantiate, but the monotonicity obligation for `intExtractValuation` at the edge frame
  is a real proof (P2), not a given.
- **Zero-debt:** no `sorry`/axiom deferral is recommended; if P1's edge-exposure proves infeasible
  within the return-type constraints, the correct action is to mark B1 **[BLOCKED]** pending an
  expansion return-type revision — not to weaken the truth lemma statement.

## H3 citation-verification status

- `[Fitting1983]` — **verified** in-repo (used at `Scheme.lean:45,244,1313`).
- Negri & von Plato (Ch. 8) and Troelstra & Schwichtenberg (§2.4) — **PDFs present** in
  `specs/literature/` but **no `references.bib` exists** in the project root to hold BibKeys.
  Recommend adding `Negri2001` / `Troelstra2000` when a bib source is established. Cited here by
  author/chapter/section per the fallback rule.
- All Lean symbol names cited (`intTImpRule`, `applyAllTImpRules`, `isAccessible`, `MonotoneEdges`,
  `propagatePersistence`, `applyPersistenceFixpoint`, `intExtractValuation`, `IBranchSaturation`,
  `sat_fimp`, `IForces_imp`) were read directly from source; `sat_timp` is explicitly **proposed
  (does not yet exist)**.
```
