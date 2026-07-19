# Handoff: Phase 7 (`boxI_lift`) — Partial

## Immediate Next Action

Open `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`, locate the landed
`raise_subtree` theorem (ends just before line ~1017, right before
`end Cslib.Logic.Modal.Labelled`), and add the `boxI_lift` theorem after it. Follow the
"Remaining sub-goal" statement in `plans/03_direct-route-forest.md`'s Phase 7 partial-progress
note verbatim — it gives the exact corrected (Finset-exclusion-parametrized) induction statement
that fixes the unsoundness this dispatch found in the naive version.

## Current State

- `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` builds green (`lake build
  Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness`), sorry-free, axiom-clean
  (`lean_verify` on both new lemmas reports `{propext, Classical.choice, Quot.sound}` only).
- Two new lemmas landed and committed (commits `f651948d`, `c19d6dc7`):
  - `ht_le_of_reflTransGen` — rank non-decreasing along forward `G.R`-reachability.
  - `raise_subtree` — the downward-cascade helper: given `p` already raised to a fixed `wp`,
    raises `p` + the forward-reachable closure through a chosen `Finset` of direct
    raw-neighbours, via repeated `cs5FCIncest_lift` (F1). Well-founded on
    `Set.ncard {q ∈ G.X | ht q ≥ ht p}` (strictly decreasing per child). Disjointness of
    different children's closures follows from a last-edge unique-parent argument (no separate
    tree/cycle-freeness lemma needed).
- `boxI_lift` itself is **not started in the file** — a draft was written, found unsound
  in its recursive step (see below), and **discarded before commit** (via `git stash`, never
  landed) rather than committed with a `sorry`. The file currently contains only the two lemmas
  above; nothing is in an inconsistent state.
- No new import beyond `public import Mathlib.Data.Set.Card` (added to `raise_subtree`'s file;
  needed for `Set.ncard`).

## Key Decisions Made (bind successors)

1. **Downward-cascade / ancestor-walk split is the right decomposition**, and avoids ever needing
   a general BFS-uniqueness or cycle-freeness lemma over the raw `Graph`. Do not revert to trying
   to prove a single monolithic "process the whole component" induction directly — the two-piece
   split (already landed downward piece + still-needed upward piece) is deliberately how the
   engineering risk was de-risked.
2. **`raise_subtree`'s Finset-of-children parameter is the reusable primitive for exclusion.**
   The ancestor walk needs the SAME mechanism but inverted (exclude, not include) — see the
   corrected statement in the plan note. Do not invent a different exclusion encoding (e.g. an
   `Option (Label Atom)`) without a concrete reason; the Finset form composes directly with
   `raise_subtree`'s own signature.
3. **Disjointness/non-overlap facts are always provable via a single application of `huniq`
   (unique-parent) at the last edge of whichever path would witness an overlap** — this pattern
   (see `hkey` inside `raise_subtree`'s `insert` case) is the template to reuse for the ancestor
   walk's own combine step. Do not reach for general tree-path-uniqueness machinery.
4. **`cases`/`induction` on a `Relation.ReflTransGen` hypothesis auto-generalizes any locally-bound
   endpoint it depends on**, renaming it to an inaccessible variable per case — use `rename_i` to
   recover names, and verify with `lean_goal` which name got which role before writing the rest of
   the branch (this cost significant iteration in this dispatch; see `hkey`'s tail case for the
   confirmed correct naming order: `rename_i mid a'` gives `mid` = intermediate, `a'` = current
   target).
5. **`rcases ... with rfl | ...` on an equation between two pre-existing local variables (not a
   fresh `intro`) can substitute in either direction** (observed: `Finset.mem_insert.mp hcm with
   rfl | ...` eliminated the OLDER variable `c`, not the newer `cm`) — use a named `heq` and
   explicit `rw [heq]` instead of `rfl` whenever both sides of the equation are pre-existing
   variables that appear in outer/shared context.

## What NOT to Try

- **Do NOT apply the outer ancestor-walk induction hypothesis directly to the parent `q`
  unconditionally covering "all of `G`'s edges."** This was attempted in this dispatch (not
  committed) and is unsound: the induction hypothesis's own conclusion promises to re-derive
  *every* edge of `G`, including the child branch (`z`) the walk is currently ascending from —
  its internal `raise_subtree` call would pick some F1-derived value for `z` that need not equal
  the value already pinned two levels down. This is not a proof-search dead end reached after
  much effort; it was caught immediately via `lean_goal` inspection before any further code was
  written. Fix: add the Finset-exclusion parameter (see the plan note) before recursing upward.
- Do not re-attempt a monolithic "distance-from-x BFS in one induction" (the approach considered
  and rejected during design, before any Lean code was written, in favor of the ancestor-walk +
  downward-cascade split) — it requires a general "unique attachment point" / BFS-tree lemma this
  dispatch's design phase concluded is strictly harder to formalize than the split adopted.

## Remaining Goals (from plan, verbatim)

From `plans/03_direct-route-forest.md` Phase 7 task list:
- [ ] State `boxI_lift` with the audit §3 signature (schematically):
      `cs5FCIncest r → (v upward-closed) → (botForces upward-closed) → IsDerivationForest G →`
      `(∀ a b, G.R a b → r (ρ a) (ρ b)) → ρ x ≤ w' →`
      `∃ ρ', ρ' x = w' ∧ (∀ z, ρ z ≤ ρ' z) ∧ (∀ a b, G.R a b → r (ρ' a) (ρ' b)) ∧`
      `(∀ {φ z}, CKForces r v botForces (ρ z) φ → CKForces r v botForces (ρ' z) φ)`.
- [ ] Recommended internal decomposition — **already substantially done**: `raise_subtree` is
      landed; only the ancestor-walk assembly (with the Finset-exclusion fix specified in the
      plan's Phase 7 partial-progress note) remains.

## References

- Plan: `specs/537_labelled_cs5_general_soundness_biconditional/plans/03_direct-route-forest.md`
  — Phase 7 section, including the "Phase 7 partial-progress note" with the exact corrected
  induction statement and combine strategy.
- Progress file: `specs/537_labelled_cs5_general_soundness_biconditional/progress/phase-7-progress.json`
- Key file: `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`
  (`raise_subtree` and `ht_le_of_reflTransGen`, both landed sorry-free/axiom-clean)
- Audit: `specs/537_labelled_cs5_general_soundness_biconditional/reports/03_tree-shape-invariant-audit.md`
  §3 (signature and proof-shape source)
