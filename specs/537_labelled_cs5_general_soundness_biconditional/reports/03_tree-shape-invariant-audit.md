# Divergence Audit: `boxI_lift` Tree-Shape Invariant (Phase 4.2 Blocker)

- **Task**: 537 — general labelled CS5 soundness biconditional (direct route, `plans/02_direct-route.md`)
- **Trigger**: Phase 4.2 `[BLOCKED]` (`handoffs/04_phase4-2-boxI-lift-blocked.md`): a fully general
  `boxI_lift` over an arbitrary finite `Graph` is unsound (3-cycle counterexample). Landed:
  `boxI_lift_star` (direct raw-neighbours only). Missing: the full recursive cascade, which was
  hypothesized to require a tree-shape/acyclicity invariant that "does not exist as a standalone lemma."
- **Mandate**: confirm or refute — via the actual Lean source and the published sources — that a NIK
  *derivation* never produces a cyclic raw graph, so the tree-restricted `boxI_lift` needed by
  soundness is completable by threading a tree invariant through the Phase 5 induction.
- **Reference-grounding tier**: **Tier 1** (literature-backed: Simpson 1994 §8.1.2–8.1.3, MMS 2021 §5).
- **Effort mode**: `--hard` (H2 anti-analysis, H3 reference grounding, H4 adversarial self-verification).

## Verdict (up front)

**CONFIRMED — the direct route is completable. The blocker is a mis-scoped lemma statement, not a
genuine mathematical wall.** The 3-cycle counterexample refutes only `boxI_lift` stated over an
*arbitrary* `Graph`. It does **not** refute the *tree-restricted* `boxI_lift` that soundness actually
needs, because **no NIK constructor can build a cyclic raw graph**: the only two edge-adding rules
(`boxI`, `diaE`) each attach a *fresh* eigenvariable by a single edge to an already-present node,
starting from `Graph.trivial`. The raw R-graph of any derivation is therefore a finite rooted forest
by construction. This is exactly the invariant Simpson's own soundness proof relies on
([Simpson1994] Lemma 8.1.3 is stated *"Let G be a tree"*; his §8.1.2 (□I) case reads *"Let G′ = G ∪
{xRy} which is a tree as y is not in G"*). The two Wijesekera-side confluence lemmas CSLib already
landed (`cs5FCIncest_lift` = F1, `cs5FCIncest_raise` = F2) are the exact analogues of the F1/F2 that
Simpson's Lifting-Lemma cascade uses. Recommended action: **fold a "derivation-forest" invariant into
the Phase 5 induction motive and complete `boxI_lift` as a standalone lemma taking that invariant as
a hypothesis — do NOT route to `[BLOCKED]`/follow-up.** A revised Phase 4.2+5 sequence is given below.

---

## Findings

### Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| Lifting Lemma 8.1.3 "Let G be a tree … there exists [-]′ with [x]′ = w and ∀ z∈G, [z]′ ≥ [z]" (chunk 0154) | Simpson1994 | `boxI_lift` (to land, Phase 4.2) | Needs a tree/forest hypothesis on `G`; raise x, cascade to whole component |
| 8.1.3 proof: raise x, then `[x_{m-1}]′` via **(F2)** up the unique path; then off-path `y` via **(F1)** down its unique path (chunk 0155) | Simpson1994 | `cs5FCIncest_raise` (F2, LANDED `Soundness.lean:337`), `cs5FCIncest_lift` (F1, LANDED `:322`), iterated | CSLib's F1/F2 are *Wijesekera-side* substitutes (from `cs5Incest`/`hsymbox`), NOT Simpson's birelational F1/F2 — same shape, different derivation |
| 8.1.3 fails for non-tree G (Figure 8-1 counterexample) (chunk 0154) | Simpson1994 | (the blocker's 3-cycle) | Confirms `boxI_lift`-over-arbitrary-`Graph` is genuinely false; tree restriction is essential |
| §8.1.2 main induction: "throughout the induction we can restrict attention to graphs that are trees" (chunk 0156) | Simpson1994 | Phase 5 motive carries `IsDerivationForest G` | Tree-invariant threaded as motive hypothesis, discharged at `Graph.trivial`, preserved per constructor |
| §8.1.2 (□I) case: "Let G′ = G ∪ {xRy} which is a tree as y is not in G" (chunk 0156) | Simpson1994 | preservation lemma `forest_addEdge_fresh` | Fresh eigenvariable ⟹ forest preserved; matches `NIK.boxI` `addEdge x y`, `y` fresh |
| §8.1.2 (⊃I)/(◇E) cases: raise via Lifting Lemma + monotonicity carries Γ-cond; extend by `[y]′ = v` (chunk 0156) | Simpson1994 | boxI case: `boxI_lift` + `ckforces_persistence` + `σ y = u` | monotonicity = `ckforces_persistence` (`Forcing.lean:122`, LANDED) |
| Def 5.1 G-interpretation: "whenever xRy in R, then ⟦x⟧ R^M ⟦y⟧" (chunk 0026) | MarinMoralesStrassburger2021 | raw edge-cond `∀ a b, G.R a b → r (ρ a) (ρ b)` | The invariant threaded through Phase 5 — **raw** edges only, never a TClosure-clique |

Both BibKeys verified present in `references.bib` (`@phdthesis{Simpson1994}`,
`@article{MarinMoralesStrassburger2021}`).

### 1. Derivation graph structure — is the raw R-graph acyclic by construction? YES.

Ground truth from `Deduction.lean` (the `NIK` inductive, `:240–312`):

- **Only two constructors add edges.** `boxI` (`:297–299`) and `diaE` (`:309–312`) are the sole rules
  that change the graph; both use `G.addEdge x y` (`Syntax.lean:148`, which adds nodes `{x, y}` and
  the single directed disjunct `a = x ∧ b = y`). Every other constructor threads `G` unchanged.
- **The added edge always goes `existing → fresh`.** In both `boxI` and `diaE` the premise is
  `∀ y ∉ L, NIK 𝒯 (G.addEdge x y) …` with `x` the pre-existing subject label and `y` cofinitely
  quantified. When the derivation is *used* (in the soundness induction) the consumer chooses `y`;
  choosing `y ∉ G.X` (always possible — see §soundness below) means `y` has no pre-existing edges
  (`Graph.edge_mem`, `Syntax.lean:118`, confines all edges to `X`). So the new edge `x → y` points
  into a brand-new sink; it cannot close a cycle.
- **The base graph is a single node.** `NIKTheorem` (`:316–317`) fixes `G = Graph.trivial`
  (`Syntax.lean:123`: `X = {var 0}`, `R = fun _ _ => False`) — a one-node, zero-edge graph, trivially
  a forest.

**Precise invariant (as it could be formalized).** Define, over `Graph Atom`,
`IsDerivationForest G : Prop :=`
`  G.X.Finite`
`  ∧ (∃ ht : Label Atom → ℕ, ∀ a b, G.R a b → ht b = ht a + 1)   -- graded ⟹ directed-acyclic`
`  ∧ (∀ a₁ a₂ b, G.R a₁ b → G.R a₂ b → a₁ = a₂)                  -- unique parent ⟹ no undirected diamond`

The graded-rank conjunct rules out *directed* cycles (the blocker's 3-cycle); the unique-parent
conjunct rules out *undirected* diamonds (`x→a→b`, `x→c→b`). **Both are needed and both hold by
construction** — this matches the blocker handoff's own analysis (a rank function *plus* unique-parent
together make `G` a rooted forest; "unique parent" alone is insufficient, as the 3-cycle shows).
`G.X.Finite` is a third conjunct the blocker did not list but which `boxI_lift`'s finite recursion
requires; `Graph` (`Syntax.lean:110`) carries none of these fields, so all three must be *threaded*,
not read off the type.

### 2. Where the invariant should live — THREAD through the Phase 5 motive; state `boxI_lift` as a hypothesis-taking standalone lemma.

**Do not modify `Graph`.** Adding finiteness/acyclicity fields to the `Graph` structure would perturb
every downstream user (the completeness direction, `CanonicalModel.lean`, `Context.lean`), and the
canonical model's graph is *not* a finite forest. The invariant is a property of *derivation* graphs,
not of `Graph` per se.

Recommended split (mirrors Simpson, who states 8.1.3 as a standalone lemma and *uses* it inside the
8.1.2 induction):

- **`IsDerivationForest` as a `def` + two preservation lemmas** (`forest_trivial`,
  `forest_addEdge_fresh`). Small, self-contained graph lemmas over `Syntax.lean`'s `Graph`.
- **`boxI_lift` as a standalone theorem** taking `IsDerivationForest G` and the raw edge-cond as
  explicit hypotheses (signature below). This keeps the heavy recursion isolated and independently
  build-checkable, exactly as Phase 4.1/4.2 already isolate `boxI_raise_step`/`boxI_lift_star`.
- **Phase 5 soundness motive carries `IsDerivationForest G` as a hypothesis**, discharged at
  `Graph.trivial` (via `forest_trivial`) and preserved at `boxI`/`diaE` (via `forest_addEdge_fresh`).
  The `NIK` recursor gives exactly this: at `boxI`/`diaE` we assume the invariant for the conclusion's
  `G` and must *supply* it for the sub-derivation's `G.addEdge x y` — the forward, constructive
  direction, which `forest_addEdge_fresh` provides.

### 3. Concrete completion path for `boxI_lift` + the `boxI` case (lemma-by-lemma, reusing landed assets)

Landed and reusable: `cs5FCIncest_lift` (F1), `cs5FCIncest_raise` (F2), `boxI_raise_step`,
`boxI_lift_star`, `box_iff_TClosure`, `dia_iff_TClosure`, `box_gives_here`, `ckforces_persistence`.

1. **`forest_trivial : IsDerivationForest (Graph.trivial Atom)`** — `ht := fun _ => 0`; no edges so
   graded/unique-parent vacuous; `X = {var 0}` finite. (~5 lines)
2. **`forest_addEdge_fresh : IsDerivationForest G → x ∈ G.X → y ∉ G.X → IsDerivationForest (G.addEdge x y)`**
   — `ht' := Function.update ht y (ht x + 1)`; new edge `x→y` graded by construction; unique-parent
   preserved because `y ∉ G.X` ⟹ `y` was not previously a target and gains exactly one source `x`;
   finiteness via `Set.Finite.union … (Set.finite_insert …)`. (~30–50 lines)
3. **`boxI_lift`** (the one genuinely new recursion; ~120–220 lines):
   `cs5FCIncest r → (v upward-closed) → (botForces upward-closed) → IsDerivationForest G →`
   `(∀ a b, G.R a b → r (ρ a) (ρ b)) → ρ x ≤ w' →`
   `∃ ρ', ρ' x = w' ∧ (∀ z, ρ z ≤ ρ' z) ∧ (∀ a b, G.R a b → r (ρ' a) (ρ' b)) ∧`
   `  (∀ {φ z}, CKForces r v botForces (ρ z) φ → CKForces r v botForces (ρ' z) φ)`.
   *Proof shape (Simpson 8.1.3, chunk 0155):* raise `x` to `w'`; process the finite connected
   component of `x` in increasing undirected-distance order (well-founded on `ht`-distance, finite by
   `G.X.Finite`); at each node `m`, its **unique** neighbour `n` toward `x` is already raised to
   `ρ' n`, so re-establish the single incident edge via `cs5FCIncest_lift` (edge `n→m`, F1) or
   `cs5FCIncest_raise` (edge `m→n`, F2) — literally one `boxI_raise_step` application per node.
   Unique-parent + acyclicity guarantee each node receives exactly one constraint (this is precisely
   what defeats the 3-cycle: there, `b` received two). Γ-persistence rides along via
   `ckforces_persistence` at each raised node (as in `boxI_raise_step`/`boxI_lift_star`).
4. **`boxI` case of Phase 5**: given `IsDerivationForest G`, raw edge-cond, Γ-cond, and the `boxI`
   premise `∀ y ∉ L, …`; goal `CKForces (ρ x) (□A)` = `∀ w' ≥ ρ x, ∀ u, r w' u → CKForces u A`. Take
   adversarial `w', u`. Pick `y ∉ L ∪ G.X` (fresh; exists since `Label Atom` is infinite and `L`,
   `G.X` finite — reuse the `exists_fresh_notMem_of_coinfinite`/`addFreshVar` supply machinery,
   `Syntax.lean:90`/`CanonicalModel.lean:116`). Apply `boxI_lift` to get `ρ'` (raise `x` to `w'`), set
   `σ := Function.update ρ' y u`. Then: raw edge-cond for `G.addEdge x y` holds (old edges from
   `boxI_lift`; new edge `x→y` is `r (σ x) (σ y) = r w' u`, given); Γ-cond via persistence
   (`ρ' ≥ ρ`, `σ` differs only at fresh `y ∉ Γ`); `IsDerivationForest (G.addEdge x y)` via
   `forest_addEdge_fresh`. Feed to the IH at `y ∉ L`, obtaining `CKForces (σ y) A = CKForces u A`. ∎
5. **`diaE` case**: needs **no** lift (matches `Soundness.lean:335` "diaE needs neither"). `x:◇A`
   forced at `ρ x` gives (dia clause at `w' = ρ x` via `le_refl`) `∃ u, r (ρ x) u ∧ CKForces u A`. Set
   `σ := Function.update ρ y u`; new edge `x→y` is `r (ρ x) u`, given; forest preserved by fresh `y`;
   Γ-cond adds `y:A` (from the witness) to unchanged Γ. Feed the IH.
6. **`boxE`/`diaI` cases**: `box_iff_TClosure`/`dia_iff_TClosure` (LANDED, Phase 2) + `box_gives_here`
   (LANDED, Phase 3) — no lift, raw edge-cond only.
7. **Remaining 9 constructors**: generalize the already-landed `nik_soundness_onePoint`
   (`Soundness.lean:666`) skeleton over `ρ`/model, carrying raw edge-cond + Γ-cond.
8. **`nik_TS5_soundness`**: specialize to `Graph.trivial`/`[]` — discharge `IsDerivationForest` via
   `forest_trivial`, raw edge-cond vacuously (no edges), Γ-cond vacuously (empty Γ).

### 4. Soundness check — does the invariant genuinely exclude the 3-cycle? YES, and it is not papering over unsoundness.

Two independent reasons the fix is *real*:

- **The 3-cycle can never be presented to `nik_TS5_soundness`.** The theorem concerns `NIKTheorem TS5 φ`
  = derivation over `Graph.trivial`. The Phase 5 motive carries `IsDerivationForest G` as a
  *hypothesis*, discharged at the trivial root and preserved by every constructor (§1). No NIK
  constructor maps a forest to a non-forest (only `boxI`/`diaE` extend, and only by a fresh sink).
  Hence every `G` reached in the induction genuinely satisfies `IsDerivationForest`; the 3-cycle is a
  graph for which the motive holds *vacuously* (its hypothesis is false) and which no derivation ever
  produces. We are **not** assuming a false statement — `boxI_lift` is only ever invoked at graphs
  that *provably* satisfy the invariant.
- **The invariant is exactly strong enough and no stronger.** In the 3-cycle, when the cascade from
  `x` reaches `b`, `b` is simultaneously constrained by `a→b` (F1 from raised `a`) and `b→x` (F2 from
  raised `x`) — two witnesses that need not coincide. The graded-rank conjunct makes this
  configuration unrepresentable (`ht b = ht a + 1 = ht x + 2` from `a→b`, `x→a`, but `ht x = ht b + 1`
  from `b→x` — contradiction). So under `IsDerivationForest` every node has a *unique* path to `x` and
  receives exactly *one* raise constraint. This is Simpson's own guarantee (chunk 0155: "each of
  these, y, has a **unique path** from x₀").

### 5. Cross-check against the published sources

**[Simpson1994] §8.1.2–8.1.3 (chunks 0154–0156) — a textbook-exact match.**
- Lemma 8.1.3 is stated **"Let G be a tree."** and immediately followed by: *"The model of Figure 8-1
  demonstrates that the lemma can fail when G is not a tree."* — i.e. Simpson's own counterexample is
  the published analogue of the blocker's 3-cycle. The tree restriction is his, not an artefact.
- The 8.1.3 **proof is the cascade** proposed above: set `[x_m]′ = w`; determine `[x_{m-1}]′` by **(F2)**
  up the unique path to the root; then each off-path `y` (unique path `…x_j R y_1…y_i = y`) by **(F1)**
  down from the already-determined `[x_j]′`. CSLib's `cs5FCIncest_raise` (F2) and `cs5FCIncest_lift`
  (F1) are the precise operations, already landed.
- The main induction (Thm 8.1.1, 1⟹2, chunk 0156) opens: *"we must ensure that throughout the
  induction we can restrict attention to graphs that are trees. However, this is indeed possible."*
  The **(□I)** case reads: *"Let G′ = G ∪ {xRy} which is a tree as y is not in G … By the lifting
  lemma there is a G-interpretation [-]′ such that [x]′ = w … by the monotonicity lemma, for all
  z:C ∈ Γ, [z]′ ⊩ C."* This is line-for-line the Phase 5 `boxI` case in §3 above (fresh-`y` forest
  preservation + Lifting Lemma raise + persistence).

**[MarinMoralesStrassburger2021] §5 (chunks 0026, 0045).** MMS use a *fully-labelled* sequent system
(`labIK≤`) with explicit relational atoms and a `≤`-labelled interpretation (Def 5.1: a
G-interpretation maps labels so that "whenever xRy in R, then ⟦x⟧ R^M ⟦y⟧" — the **raw** edge-cond
CSLib threads). Their soundness (Thm 5.3) is a rule-by-rule induction on derivation height and does
**not** foreground a tree restriction, because their sequent framework side-steps the non-tree
excursions that Simpson's natural-deduction system incurs (Simpson himself notes the sequent detour
`L_m(𝒯,∅)` avoids non-tree excursions — `Soundness.lean:60`). MMS therefore corroborate the *raw
edge-cond invariant* (the thing threaded through Phase 5) but are silent on the tree shape; the
tree-shape argument is genuinely Simpson-specific and is the correct source for this
natural-deduction development. **Net**: the published proof CSLib is transcribing (Simpson's) relies
on the derivation-tree shape *exactly* as hypothesized.

---

## Adversarial Self-Verification (H4)

I attempted to refute "the derivation raw graph is a forest" and "the tree-restricted `boxI_lift` is
completable." Each refutation attempt and its resolution:

| Claim | Source / Counterexample tried | Verdict |
|-------|-------------------------------|---------|
| Some NIK rule can create a raw cycle | Scanned all 13 `NIK` constructors (`Deduction.lean:242–312`). Only `boxI`/`diaE` add edges; both `addEdge x y` with `y` cofinitely fresh, `x` pre-existing. A fresh `y ∉ G.X` has no edges (`edge_mem`). New edge is a sink. | **REFUTED** (no rule creates a cycle) — hypothesis holds |
| The graph is a free index, so the 3-cycle is a legal input to `nik_TS5_soundness` | `NIKTheorem` (`:316`) fixes `G = Graph.trivial`; the motive carries `IsDerivationForest` as a *discharged* hypothesis. The 3-cycle satisfies the motive vacuously and is never produced. | **Concern DEFUSED** — 3-cycle unreachable in the actual theorem |
| Graded-rank alone suffices (drop unique-parent) | Diamond DAG `x→a→b`, `x→c→b`: graded (ht b = 2) but `b` has two parents ⟹ two raise constraints. | Unique-parent **IS** needed; both conjuncts retained (matches blocker) |
| Unique-parent alone suffices (drop rank) | The blocker's 3-cycle `x→a→b→x`: unique-parent holds, yet `b` double-constrained. | Rank **IS** needed; both conjuncts retained |
| `boxI_lift`'s cascade might not terminate / `G.X` could be infinite | `Graph` has no finiteness field. But `Graph.trivial` is finite and `addEdge` adds one node ⟹ `G.X.Finite` threadable as a third conjunct. Cascade is finite recursion over the component. | **Resolved** by adding `G.X.Finite` to the invariant (a gap in the blocker's 2-conjunct framing) |
| A fresh `y ∉ L ∪ G.X` might not exist (can't preserve forest at boxI) | `Label Atom` is infinite (`var : ℕ ↪ Label`); `L` finite (rule field `hL`), `G.X` finite (invariant). Union finite ⟹ fresh `y` exists. Supply infra already present (`exists_fresh_notMem_of_coinfinite`, `addFreshVar`). | **Resolved** — fresh label always available |
| The deep "exact-symmetry / clique-closure" obstruction (dispatches 3–4, GATE-C) still blocks this | That wall was for the `boxE`/`diaI` *consumer* side and was **dissolved** in Phase 1–3 by `box_iff_base`/`dia_iff_base` (`Soundness.lean:374,392`): consumers need forcing-*equivalence* across an r-edge, never exact symmetry. The residual is *only* the `boxI` producer lift, which is the tree cascade. | **Not applicable** to `boxI_lift`; the wall is already down |
| `diaE` also needs the lift/cascade | dia clause at `w' = ρ x` (`le_refl`) yields `∃u, r (ρ x) u ∧ …`; map fresh `y ↦ u` with **no** raise of `x`. New edge `r (ρ x) u` given directly. | **REFUTED** — `diaE` needs no lift (confirms `Soundness.lean:335`) |
| The whole thing is just as intractable as the earlier `INTRACTABLE` verdict | The earlier verdict predates the Phase 1–3 breakthrough (`box_iff_*`) that dissolved Wall A. With consumers handled and `diaE` free, the *only* remaining item is the tree cascade — which Simpson does on paper in two paragraphs (chunk 0155) and which reuses `boxI_raise_step` per node. | **Superseded** — the module's own `INTRACTABLE`/`GATE-C` docstring notes are stale and should be removed at Phase 5 |

**Residual uncertainty (honestly flagged).**
- **Confidence the direct route is mathematically completable: HIGH (~90%).** The math is Simpson's,
  the F1/F2 primitives are landed, the invariant is discharge-able, and the consumer wall is already
  down.
- **Confidence `boxI_lift` fits a *single* dispatch: MEDIUM (~60%).** The component-cascade recursion
  (threading each node's already-raised parent value, well-founded on `ht`-distance over a finite
  `Finset`) is fiddly Lean engineering beyond what `boxI_lift_star` (direct neighbours only) does. It
  may want its own dispatch, or a helper `raise_component_by_distance` sub-lemma. This is an
  *engineering* risk, not a soundness risk.
- **One formalization choice left open for the planner**: whether to recurse via strong induction on
  the rank `ht` (process by distance from `x`) or to re-root the finite forest at `x` and structurally
  recurse. Both are viable; the rank route reuses the invariant's `ht` directly and is recommended.

No recommendation in this report involves `sorry`, a new axiom, or weakening `cs5FCIncest`.

---

## Revised Direction — phase sequence for plan v2 (fold into `plans/02_direct-route.md`)

Restructure the blocked Phase 4.2 and the not-started Phase 5. **Un-block; do NOT route to Phase 7.**

- **Phase 4.2a — Derivation-forest invariant (NEW, small).** Define `IsDerivationForest` (3 conjuncts:
  `X.Finite`, graded rank, unique-parent) over `Syntax.lean`'s `Graph`; prove `forest_trivial` and
  `forest_addEdge_fresh`. Zero new dependencies on the model. ~40–70 lines. Bounded, independently
  build-checkable. Depends on: nothing new.
- **Phase 4.2b — `boxI_lift` (the recursion).** State `boxI_lift` taking `IsDerivationForest G` +
  raw edge-cond as hypotheses (§3 signature). Prove by well-founded recursion on `ht`-distance over
  the finite component, one `boxI_raise_step` per node, reusing `boxI_lift_star`'s Γ-persistence
  bookkeeping. ~120–220 lines. **This is the sole concentrated-risk unit** (was Phase 4.2's residual).
  Depends on: 4.1 (`boxI_raise_step`, landed), 4.2 (`boxI_lift_star`, landed), 4.2a.
- **Phase 5 — main induction (as planned, motive amended).** Add `IsDerivationForest G` to the motive
  alongside raw edge-cond + Γ-cond. `boxI` via `boxI_lift` + fresh-`y` + `forest_addEdge_fresh` +
  persistence; `diaE` via `le_refl` (no lift); `boxE`/`diaI` via `box_iff_TClosure`/`dia_iff_TClosure`
  + `box_gives_here` (landed); 9 others from the `nik_soundness_onePoint` skeleton. Discharge the
  motive at `Graph.trivial` via `forest_trivial`. Land `nik_TS5_soundness`. Remove the stale
  `INTRACTABLE`/`GATE-C`/"What remains" docstring notes. Depends on: 2, 4.2b.
- **Phase 6 — regression gate (unchanged).**
- **Phase 7 — now genuinely contingency-only.** Only fires if Phase 4.2b's *engineering* (not its
  mathematics) overruns budget across dispatches; even then the correct escalation is a scoped
  follow-up task for `boxI_lift` alone, not a `[BLOCKED]` on the whole soundness direction.

**Zero-debt constraints (unchanged): no `sorry`, no new axiom, `cs5FCIncest` unweakened, no Preserved
Asset regressed.**

## Reference Grounding — H3 source/code table

| # | Claim in this report | Source (BibKey / chunk) OR Code (file:line) | Status |
|---|----------------------|---------------------------------------------|--------|
| G1 | Only `boxI`/`diaE` add edges; edge is `existing→fresh` | `Deduction.lean:297–299, 309–312`; `Syntax.lean:148` | verified (read) |
| G2 | Base graph is one node, no edges | `Deduction.lean:316–317`; `Syntax.lean:123` | verified (read) |
| G3 | Edges confined to `X` (fresh node has no edges) | `Syntax.lean:118` (`edge_mem`) | verified (read) |
| G4 | F1 = `cs5FCIncest_lift`, F2 = `cs5FCIncest_raise` landed | `Soundness.lean:322, 337` | verified (read) |
| G5 | Consumer wall dissolved (no exact symmetry needed) | `Soundness.lean:374, 392, 422, 437` | verified (read) |
| G6 | `boxI_raise_step`, `boxI_lift_star` landed, sorry-free | `Soundness.lean:472, 563`; handoff verify block | verified (read) |
| G7 | `cs5FCIncest` 5 conjuncts (refl, trans, hfour, hsymbox, incest) | `CS5Canonical.lean:255–260`, `:234` | verified (read) |
| G8 | `ckforces_persistence` (monotonicity) available | `Forcing.lean:122` (cited `Soundness.lean:88, 456`) | cited (not re-opened) |
| G9 | Fresh-label supply infrastructure exists | `Syntax.lean:90`; `CanonicalModel.lean:116` | verified (read) |
| S1 | Lifting Lemma 8.1.3 stated for trees; fails off-tree (Fig 8-1) | Simpson1994, chunk 0154 | verified (read) |
| S2 | 8.1.3 proof = F2-up-unique-path then F1-down-unique-path | Simpson1994, chunk 0155 | verified (read) |
| S3 | Main induction restricts to trees; (□I) "G′ = G ∪ {xRy} tree as y not in G" | Simpson1994, chunk 0156 | verified (read) |
| M1 | Raw edge-cond = MMS G-interpretation Def 5.1 | MarinMoralesStrassburger2021, chunk 0026 | verified (read) |

## Memory Candidates

1. In `Cslib.Logic.Modal.Labelled`, the raw R-graph of any `NIK` derivation is a **finite rooted
   forest by construction**: only `boxI`/`diaE` add edges, always `addEdge x y` with `y` a cofinitely-
   fresh sink and `x` pre-existing, from `Graph.trivial`. A tree/acyclicity invariant on `NIK`
   derivations therefore needs no new `Graph` field — it is a *threaded motive hypothesis* (discharged
   at `Graph.trivial`, preserved per constructor), never a standalone fact about arbitrary `Graph`.
2. A `boxI_lift`/Lifting-Lemma-style lemma stated over an *arbitrary* finite `Graph` is genuinely
   false (3-cycle counterexample), but this does **not** block soundness: the tree-*restricted* lift
   is what the `boxI` case needs, and Simpson 1994 Lemma 8.1.3 is itself stated only for trees. When a
   "general" lemma is refuted by a counterexample, check whether the *induction that consumes it* ever
   supplies that counterexample — often a discharged motive hypothesis makes the general statement
   unnecessary.
3. For `cs5FCIncest`-model soundness, `box_iff_base`/`dia_iff_base` (forcing-equivalence across an
   r-edge, no exact symmetry) dissolve the `boxE`/`diaI` "exact-symmetry" wall that earlier dispatches
   assessed INTRACTABLE/GATE-C; after that breakthrough the *only* residual is the `boxI` producer
   lift. Stale "intractable" docstring verdicts should be re-audited against later same-file
   breakthroughs before being trusted.
