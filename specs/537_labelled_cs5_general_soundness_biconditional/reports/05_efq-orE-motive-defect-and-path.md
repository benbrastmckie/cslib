# Research Report: What Remains for `nik_TS5_soundness`, and Why the Planned Next Step Targets a False Statement

- **Task**: 537 — general labelled CS5 soundness biconditional (Simpson 1994 Thm 8.1.4, direction 2⟹1)
- **Type**: cslib (Lean 4) — RESEARCH dispatch (no implementation performed)
- **Primary file**: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (2094 lines)
- **Inputs read**: current source (verified), plan v5, summaries 11/12/13, orchestrator handoff, `Deduction.lean` `NIK` constructors
- **Headline finding**: The file is **green, zero-`sorry`, zero-axiom** and all landed infrastructure is sound. But the **currently-planned next step (add a root-connectivity invariant, keep `nikTr` as-is) builds toward a `nik_adequacy` statement that is mathematically FALSE** at the disconnected-`y` `efq` case. The blocker is not "root-connectivity is missing"; it is that the landed `nikTr` translation is **target-oriented** and therefore drops the entire graph/context when the target label is disconnected. The fix is a translation/motive redesign (Phase 8.1), not a new invariant on top of the existing definition.

---

## 1. Current state (verified against source + build)

- **Scoped build GREEN**: `lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` → "Build completed successfully (960 jobs)", exit 0.
- **`sorry`/`admit`: ZERO real occurrences.** Every `grep` hit for `sorry` is inside docstring prose (lines 217, 220, 268, 274, 327, 646). No `admit`. No `axiom`.
- **File shape**: 2094 lines. Ends cleanly at `nikTrFuel_fuel_invariant_step` inside `end Cslib.Logic.Modal.Labelled`.
- **Landed target-theorem chain does NOT yet exist**: there is **no** `nik_adequacy`, **no** `nik_TS5_to_hilbert`, **no** `nik_TS5_soundness` in the file. The goal theorem is unstarted at the assembly level.
- **What IS landed** (all sorry-free, axiom-clean, committed):
  - Phases 1–7 Preserved Assets (`box_iff_*`, `dia_iff_*`, `cs5FCIncest_*`, `boxI_lift*`, `IsDerivationForest` + `forest_trivial`/`forest_addEdge_fresh`, `raise_subtree`, `siblings_disjoint`, `ht_le_of_reflTransGen`).
  - PD.1 `bot_*` lemmas (semantic; see §3 — NOT reusable for the Hilbert route).
  - Phase 8.1: the translation `nikTr` / `sigAt` / `sigAtFuel` / `nikTrFuel` / `factsAt` / `bigAndL` (lines 1383–1497) + 2 sanity `example`s.
  - Phase 8.2 (partial): the propositional-combinator toolkit (`cs5_deriv_imp_*`, `cs5_deriv_box_mono`, `cs5_deriv_imp_congr_right`), 8 label-local "core" case lemmas (`sigAt_assumption`, `sigAt_andI/andE1/andE2/orI1/orI2/impE/impI`), and the cross-label infrastructure landed over the last two dispatches: `nikTrFuel_mono`, `bigAndL_imp_of_pointwise`, `sigAtFuel_mono_context`, `sigAtFuel_mono_fuel`/`_le`, `nikTrFuel_succ_eq`, `nikTrFuel_no_parent`, `nikTrFuel_fuel_invariant_step`.

**Conclusion on state**: there is no debt to clean up. The task is legitimately `[PARTIAL]` with a green tree. The problem is purely forward-direction: the two cross-label cases (`efq`, `orE`) have never been machine-attempted, and — the new finding below — cannot be, against the current translation.

---

## 2. What remains (smallest closing set, per plan v5)

Ordered remaining obligations to reach `nik_TS5_soundness`:

1. **Sub-step 8.2 cross-label cases**: `efq`, `orE` of `nik_adequacy`. **NOT attempted; blocked — see §3/§4.**
2. **Sub-step 8.3 modal cases**: `boxI`, `boxE`, `diaI`, `diaE` (reuse `boxI_lift`, `box_iff_TClosure`/`dia_iff_TClosure`). Not started.
3. **Assemble `nik_adequacy`**: the actual 12-constructor induction (currently only standalone "core" helper lemmas exist; `nik_adequacy` itself is unstated).
4. **Sub-step 8.4**: `nik_TS5_to_hilbert` by specialising `nik_adequacy` at `Graph.trivial`, `Γ = []`.
5. **Phase 9**: `nik_TS5_soundness := fun h => cs5_soundness_derivable_incest (nik_TS5_to_hilbert h)`; retire stale docstring notes.
6. **Phase 10**: full-project regression gate (`lake build`/`lint`/`shake`/`checkInitImports`/`test`).

Steps 2–6 are genuinely "known-shape" transcription. **Everything hinges on step 1, and step 1 is where the design is wrong.**

---

## 3. Blocker analysis — which blockers are live

| Blocker (historical) | Origin | Status now |
|---|---|---|
| Gate C / INTRACTABLE (semantic ∀ρ motive) | early dispatches | **Superseded** — route pivoted to Hilbert bridge (plan v5). Stale docstring text remains (Phase 9 cleanup). |
| PD.2 motive redesign / PD.3 `efq` residual (semantic route) | summary 10 | **Deferred** to route-(b) research recommendation; genuinely open; not on the v5 critical path. |
| Cross-label EFQ "PD.1 `bot_*` reuse" | summary 12 | **Resolved-as-negative**: PD.1's `bot_*` are `CKForces` (semantic) facts, NOT syntactic `Derivable`/`sigAt` facts, so they are **not reusable** for the Hilbert bridge. Confirmed in source (lines 488–492 of plan). |
| "core `sigAt`-only motive insufficient for efq/orE" | summary 12 | **Correct and live** — a bare `sigAt x` fact packages only `x`'s subtree (source docstring lines 1889–1911). |
| Root-connectivity not implied by `IsDerivationForest` | summary 13 / handoff | **Correct but incomplete** — see §4. Root-connectivity is *necessary* but *not sufficient*, and by itself does not rescue the current `nikTr`. |

### The concrete, live obstruction (new this dispatch)

`efq` is `efq (G Γ x y A) (h : NIK 𝒯 G Γ (x ∶ ⊥)) : NIK 𝒯 G Γ (y ∶ A)` (`Deduction.lean:247`). **The constructor places NO constraint on `y`** — in particular `y ∉ G.X` is permitted (and is exactly the disconnected form completeness needs, `Deduction.lean:242-246`).

Trace the landed `nikTr` on such a node with `y ∉ G.X`, `y ∉ labels(Γ)`, `A = atom p`:

- `nikTr G Γ hfin y p = nikTrFuel … (card+1) y (sigAt … y ⊃ p)`.
- `y ∉ G.X` ⟹ no `q` with `G.R q y` (by `Graph.edge_mem`) ⟹ `nikTrFuel` returns `inner` immediately (no ancestor wrap).
- `sigAt … y`: `y` has no `R`-children and no `Γ`-facts ⟹ `bigAndL [] ∧ bigAndL []` = `(⊥⊃⊥) ∧ (⊥⊃⊥)` (a `⊤`-surrogate).
- So `nikTr G Γ hfin y p = ((⊥⊃⊥) ∧ (⊥⊃⊥)) ⊃ p`.

`nik_adequacy` would require `⊢_{CS5} ((⊥⊃⊥)∧(⊥⊃⊥)) ⊃ p`. Its antecedent is a theorem (`⊤∧⊤`), so modus ponens yields `⊢_{CS5} p` for an **arbitrary atom `p`** — contradicting CS5 consistency (already certified by `nik_TS5_consistent` and `cs5_soundness_derivable_incest`). **Therefore `nik_adequacy`, with the landed `nikTr`, is a false statement**, and the 12-constructor induction cannot close at this case.

**Why root-connectivity does NOT fix this.** The planned `IsRootedForest G := ∃ root, ∀ z ∈ G.X, ReflTransGen G.R root z` only quantifies over `z ∈ G.X`. The offending `efq` has `y ∉ G.X`, so it is *outside* the invariant's scope. Adding root-connectivity closes the "propagate down to `y`" sub-argument only for `y ∈ G.X`; the disconnected `y` — the whole reason `efq` is cross-label — is untouched. `orE` has the identical defect (`y` independent of `x`, `y ∉ G.X` permitted; `Deduction.lean:271`).

**Root cause**: `nikTr` is **target-oriented** — it walks up the *target's* ancestor spine (`nikTrFuel` at line 1427) and threads in only the off-spine siblings *of that spine*. When the target is disconnected, the spine is empty and the translation **drops the entire graph `G` and context `Γ`**. Two conclusions over the *same* `(G,Γ)` (`x:⊥` and `y:A`) get **structurally unrelated** formulas, so no `efq` bridge between them can exist.

This is high-confidence analytical (a clean reductio via CS5 soundness), not yet machine-refuted. Per the plan's postmortem constraint, the next dispatch should **machine-confirm it first** with one `example` (a 2–3 node graph, disconnected `y`) before acting — cheap and decisive.

---

## 4. Recommended path

### Primary recommendation: revise Phase 8.1 — make the translation target-independent

The bridge is not dead, but the **translation shape is wrong**. Simpson's faithful `(Γ ⊢_G x:A)^T` (Lemma 6.1.2) encodes the **whole sequent**: the graph+context form a **target-independent antecedent**, and only the *placement* of `A` depends on `x`. The landed `nikTr` made the antecedent target-*dependent*, which is precisely what breaks `efq`/`orE`.

Concrete redesign to evaluate:

- Define the sequent translation as `Θ(G,Γ) ⊃ place(x, A)`, where:
  - `Θ(G,Γ)` = `sigAt G Γ hfin root` at **the single tree root** (target-independent; captures the entire tree). **This reuses the landed `sigAt`/`sigAtFuel` verbatim** — evaluate it at the root instead of at the target.
  - `place(x, A)` = `A` boxed to `x`'s tree-depth-from-root (a small new "descend `k` box levels" helper; `k` = `ht x - ht root`, available from the landed graded-rank witness / `ht_le_of_reflTransGen`).
- **`efq` then closes cleanly using the CS5 `T` axiom** (`□A ⊃ A`, which CS5/IKTB4 *has*): from `⊢ Θ ⊃ place(x,⊥)` = `⊢ Θ ⊃ □^{d_x}⊥`, iterate `T` to get `⊢ Θ ⊃ ⊥`, then `⊥ ⊃ place(y,A)` (ex falso) gives `⊢ Θ ⊃ place(y,A)` — **for any `y`, including the disconnected case** (`place(y,A)` at depth 0 is just `A` under `Θ`). This is why the Hilbert route was chosen over the semantic route: `T` discharges disconnected `⊥` where the intuitionistic Kripke semantics could not.
- **`orE`**: with a shared `Θ`, both branch IHs and the major-premise IH sit under the *same* antecedent; combine via the disjunction-elimination combinator already in the toolkit family, boxed to `x`'s depth. No LCA computation, no root-propagation walk.

What this costs / preserves:
- **Still needs `IsRootedForest`** (single-rootedness) — to name *the* root anchoring `Θ` and to define `place`'s depth. The previous dispatch's instinct to add this invariant is correct and reusable; only the *proof strategy* built on top of `nikTr` (propagate-up-then-down) is discarded.
- **Reusable as-is**: `sigAt`/`sigAtFuel`/`factsAt`/`bigAndL`, `sigAtFuel_mono_context`, `bigAndL_mono`/`_imp_of_pointwise`, the entire `cs5_deriv_*` combinator toolkit, `cs5_deriv_box_mono` (for the box-placement helper and the `T`-iteration).
- **Likely retired**: `nikTrFuel` and its bespoke lemmas (`nikTrFuel_mono`, `nikTrFuel_succ_eq`, `nikTrFuel_no_parent`, `nikTrFuel_fuel_invariant_step`, `sigAtFuel_mono_fuel`/`_le`) — these serve the target-oriented ancestor-walk, which the redesign removes. This is real sunk cost (~200+ lines) and should be acknowledged in the revision.

### Mandatory precondition: resolve the source

Plan v5 records (Sub-step 8.1 deviation, lines 352–358) that Simpson Ch. 6 Fig. 6-1/6-2 is **OCR-corrupted at the formula level** and `nikTr`'s shape was reconstructed from prose. **Getting the translation shape exactly right is the linchpin of the entire route**, and a prose reconstruction already produced a false-making definition once. Before re-defining, obtain a legible copy of Simpson 1994 §6.1 (Fig. 6-1/6-2 + the one worked example) — via `/literature` discovery, a cleaner PDF, or the published thesis — and pin `Θ`/`place` against it. Do NOT re-guess.

### Concrete lemmas to prove (post-redesign, in order)

1. `IsRootedForest` + `rooted_trivial` + `rooted_addEdge_fresh` (mirror `forest_trivial`/`forest_addEdge_fresh`; `addEdge x y` for fresh `y`: root already reaches `x`, extend by one step). Thread it alongside `IsDerivationForest` through the `boxI`/`diaE` graph-extension cases.
2. `place`/depth helper + `place_trivial` sanity (`Graph.trivial`: depth 0 ⟹ `place = A`, so the whole translation collapses to `Θ ⊃ A` = `⊤ ⊃ A` ≡ `A`, matching Phase 8.4's needed collapse).
3. `T`-iteration lemma: `⊢ □^k ⊥ ⊃ ⊥` (via the landed `.ax … .t` / reflexivity axiom of `CS5ModalAxiom`; confirm the exact `T` constructor name with `lean_local_search`/`lean_hover_info` on `CS5ModalAxiom`).
4. `efq` case; `orE` case; then the 4 modal cases (8.3); assemble `nik_adequacy`; 8.4; 9; 10.

### Honest contingency

If the source cannot be resolved legibly, or the redesigned translation *also* resists `efq`/`orE` under machine check, this is the sanctioned point to invoke plan v5's **Phase 11 `[BLOCKED]` terminal + route-(b) research recommendation** — with the green tree, PD.1 + the reusable combinator/`sigAt` toolkit preserved, zero debt. The task has now spent ~14 orchestration cycles and ~700 lines of infrastructure without closing a single cross-label case; the revision should set a hard dispatch budget for the redesigned `efq`/`orE` before escalating, rather than accreting more infrastructure.

---

## 5. Answers to the four questions (summary)

1. **Current state**: green, 0 `sorry`/`axiom`, 2094 lines; infra through `nikTrFuel_fuel_invariant_step`; `nik_adequacy`/`nik_TS5_to_hilbert`/`nik_TS5_soundness` do not exist yet.
2. **What remains**: `efq`+`orE` (8.2), 4 modal cases (8.3), assemble `nik_adequacy`, specialise (8.4), corollary + docstring (9), regression (10). Only step 1 is hard.
3. **Blocker analysis**: Gate C superseded; PD/route-b deferred-open; PD.1 reuse disproved; "sigAt-core insufficient" live; root-connectivity **live but insufficient** — the true obstruction is that `nikTr` is target-oriented and drops `(G,Γ)` for a disconnected `efq`/`orE` target, making `nik_adequacy` **false as currently shaped**.
4. **Recommended path**: revise Phase 8.1 to a **target-independent `Θ(G,Γ) ⊃ place(x,A)`** translation (reusing `sigAt` at the root); close `efq` via the CS5 **`T` axiom** (`□⊥ ⊃ ⊥`), `orE` under the shared `Θ`; keep/add `IsRootedForest`; retire the `nikTrFuel` ancestor-walk lemmas. **Resolve the OCR-corrupted Simpson §6.1 source first.** Machine-confirm the falseness finding with one `example` before redesigning.
