# Continuation Handoff: Task 512 — Phase 3 Route-2, Partial Progress

## State at end of this dispatch

- Phases 1-2: landed, committed, CI-green (unchanged from prior dispatch).
- Phase 3 (`cs5Combined_seed_excludes`): **`[PARTIAL]`**, not `[BLOCKED]`. Real, sorry-free,
  axiom-clean progress landed in `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`
  (commit "task 512 phase 3: land collapse-projection + HR seed-pair facts"), plus two new
  general-purpose lemmas in `Cslib/Logics/Modal/Basic.lean` (`Proposition.map_id`,
  `Proposition.map_map`).
- Phases 4-5: not started (both consume Phase 3's full closure, which has not been reached).

## What was landed (all sorry-free, `#print axioms` clean: only `propext`/`Quot.sound`/
`Classical.choice`)

1. **`cs5Collapse` / `τ0`** (`CS5Canonical.lean`): the atom-collapse `ProofSigHom` erasing the
   `τL`/`τR` tagging via `Sum.elim id id`. Both `crossLR`/`crossRL` collapse onto the SAME
   `CS5ModalAxiom.tBox` instance (`□B → B`), so `τ0` is a valid morphism reusing the same
   `Deriv.map` machinery as `τL`/`τR` — no new infrastructure class, just a new instance of the
   existing `ProofSigHom` pattern.
2. **`cs5_lift_deriv_collapse` / `cs5_collapse_of_L_deriv` / `exists_preimage_list_of_forall_mem_image`
   / `cs5Combined_collapse_mem_L`**: the transport corollaries taking a `τL`-tagged
   `CS5Combined`-derivation from `τL '' H` down to a bare `CS5ModalAxiom`-derivation from `H`.
3. **`cs5Combined_bot_excluded`** and **`cs5Combined_boxA_excluded`**: using (2), these FULLY
   discharge two of the four seed-exclusion sub-obligations — `⊥` and `τL(□A)` cannot leak into
   `modalDeductiveClosure CS5Combined (τL '' H)`, each via a direct contradiction (`H`
   consistency from `h_not`, or `h_not` itself).
4. **`cs5Combined_boxInv_subset_HR` / `cs5Combined_HR_subset_H` / `cs5Combined_boxInv_HR_subset_H`
   / `cs5Combined_A_notMem_HR`**: the four `HR`-seed-pair facts (`HR := modalDeductiveClosure
   CS5ModalAxiom (boxInv H)`), a direct mechanical port of the sorry-free `cs5_pair_seed_mem`
   probe body (`specs/509_.../probes/cs5-pair-primeness.lean:98`). These are exactly report 02's
   "Step 1" and are reusable as-is by Phase 4's pair recovery, independent of how the rest of
   Phase 3 resolves.
5. **`cs5Combined_boxL_imp_boxR` / `cs5Combined_boxR_imp_boxL`**: `⊢ □(τL B) ↔ □(τR B)` for every
   `B` (empty context), via necessitating `crossLR`/`crossRL` and combining with `K`
   (`CS5ModalAxiom.k`) and axiom `4` (`.fourBox`). This is the exact SYNTACTIC form of report
   02's "crossRL-conservativity" lever (the two sorts agree on all *boxed* content). It is
   landed as a standalone, verified fact but was **not yet successfully combined** into a closed
   argument for the remaining obligation (see below).

## What remains open: `τR A` excluded, and the mixed `bigOr` disjunction case

**The reduction already established** (mechanical, safe to reuse): by the deduction theorem, any
`Γ ⊢_{CS5Combined} τR A` with `Γ` a finite list `⊆ τL '' H` reduces (via `∧`-introduction on the
context, both derivable in `H` since `H` is deductively closed) to a SINGLE empty-context
combined theorem `⊢_{CS5Combined} τL(Ψ) → τR(A)` for some `Ψ ∈ H`. So the remaining obligation
reduces to:

> For all `Ψ ∈ H`: `⊬_{CS5Combined} τL(Ψ) → τR(A)`, given `A ∉ HR` (equivalently `□A ∉ H`).

**Confirmed dead ends** (do not re-attempt without a genuinely new idea):

- **Any single compositional/homomorphic translation** `tr : Proposition(Atom⊕Atom) →
  Proposition Atom` commuting with all connectives (including `box`) — report 02 §5's general
  impossibility (`□(p∨q) → (□p∨□q)` counterexample) rules this out for ANY atom-substitution
  `ρ`. This dispatch independently re-derived the same wall via a semantic argument: pick
  `ρ := □` (test `B = p ∨ q`) or `ρ := id` (collapses `A ∈ H` case) — both fail. The landed
  `τ0` collapse (`ρ := id`) is exactly the ONE translation that IS mechanizable, and it is
  provably too weak for this specific obligation (gives only `⊢CS5 Ψ → A`, not a contradiction,
  since `A ∈ H` is consistent with `h_not`).
- **The "mirrored" semantic model** (set `v(w, inr p) := v(w, inl p)` pointwise, NOT uniformly —
  i.e., copy L's valuation to R at every world, not collapse to a single value): this dispatch
  checked this is ALWAYS a valid `CS5Combined` model (crossLR/crossRL trivially satisfied, since
  L/R become pointwise-identical), so it only re-derives the same weak necessary condition
  `⊢CS5 Ψ → A` as the `τ0` collapse — no new information.
- **The "L-uniform" semantic model** (fix L-atoms to have the SAME value at every world in an S5
  cluster, let R-atoms vary freely subject to crossLR/crossRL): this dispatch used this class to
  CONFIRM the `⊢CS5 Ψ → A` necessary condition is not sufficient either (a genuine 2-world
  countermodel to `τL(A) → τR(A)` itself was exhibited: `v(w1, inl p) = true`,
  `v(w2, inl p) = false`, `v(w1, inr p) = false` satisfies crossLR/crossRL vacuously at `w1` since
  `box(τL p)` is false there, so `τL(A) → τR(A)` is NOT a `CS5Combined` theorem — consistent with
  what we need, but also shows the necessary condition alone under-determines the truth value).

**One unexplored, promising lead** (not confirmed or refuted — worth investigating FIRST in the
next dispatch): the **"necessity transfer" conjecture**:

> `⊢_{CS5Combined} τL(Ψ) → τR(A)` implies `⊢_{CS5} Ψ → □A`.

If TRUE (as both necessary AND sufficient, or even just necessary), this would close the
obligation immediately: `Ψ ∈ H` (deductively closed) + `⊢CS5 Ψ → □A` gives `□A ∈ H` directly via
`H`'s closure, contradicting `h_not`. This dispatch did NOT find a proof or a countermodel for
this conjecture; the landed `cs5Combined_boxL_imp_boxR`/`_boxR_imp_boxL` lemmas (item 5 above)
are the most promising available LEVER for attacking it (they show boxed L/R content transfer
freely both ways), but connecting `⊢ τLΨ → τRA` (a BARE, non-boxed target) to a BOXED conclusion
about `Ψ, A` needs an argument this dispatch did not complete. A natural next step: attempt to
show the CONVERSE first — is `⊢CS5 Ψ → □A` actually SUFFICIENT for `⊢CS5Combined τLΨ → τRA`? If
yes, try deriving it via: necessitate `Ψ → □A` (empty-context theorem, if provable) to get
`□(Ψ → □A)`, `K`-distribute to `□Ψ → □□A`, combine with axiom `4` and the box-equivalence lemmas
above. If a clean derivation emerges, attack necessity separately (or look for a genuinely
different combinatorial argument via the derivation-height induction report 02 §5 originally
recommended, which this dispatch did not attempt directly — it pursued semantic/algebraic
shortcuts instead, all of which hit the "no compositional translation suffices" wall).

**Fallback still available** (per plan, if genuinely exhausted): a PROVED mechanized obstruction
theorem showing the sorts DO collapse — but per report 02's analysis (~85-90% confidence the
claim is TRUE) and this dispatch's own failure to find ANY leak/collapse derivation, this is
assessed as UNLIKELY to be the right outcome; do not manufacture a false obstruction. Continue
attacking the derivation-induction route or the necessity-transfer conjecture first.

## Files touched this dispatch

- `Cslib/Logics/Modal/Basic.lean` — added `Proposition.map_id`, `Proposition.map_map`.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — added `cs5Collapse`, `τ0`,
  transport corollaries, `cs5Combined_bot_excluded`, `cs5Combined_boxA_excluded`, the four
  `HR`-seed-pair facts, and the box-equivalence lemmas.
- `specs/512_cs5_box_backward_atom_sum_completeness/plans/01_box-backward-atom-sum.md` — Phase 3
  heading updated to `[PARTIAL]` with a resumed-dispatch progress note.

## Verification commands

```bash
cd ~/Projects/cslib
lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5Canonical
lake build   # full project, confirmed green this dispatch
lake test    # confirmed green this dispatch
lake exe checkInitImports
lake exe lint-style
grep -n "\bsorry\b" Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean Cslib/Logics/Modal/Basic.lean
```

## Next dispatch instructions

1. Read this handoff and report 02 in full before writing any code.
2. Attempt the necessity-transfer conjecture (`⊢CS5Combined τLΨ→τRA ⟹ ⊢CS5 Ψ→□A`) first — it is
   the most promising untried lead and would close the obligation in a handful of lines if it
   goes through.
3. If that conjecture fails (countermodel found, or proof attempt stalls), pursue the full
   derivation-height induction on `CS5Combined` `DerivationTree`/`Deriv` (5 rule cases) that
   report 02 §5 describes as the "single hard node" — budget ~150-220 lines, and expect it to
   need genuine new casework, not a template clone.
4. Zero-debt holds throughout: no `sorry`, no new axiom. If this dispatch's budget is exhausted
   again without closing the obligation, land whatever builds green, update this handoff, and
   keep Phase 3 `[PARTIAL]` (not `[BLOCKED]` unless a genuine obstruction is PROVED).
5. Do NOT re-attempt the confirmed dead ends listed above (homomorphic translations, mirrored
   model, L-uniform model) without a genuinely new angle not covered here.
